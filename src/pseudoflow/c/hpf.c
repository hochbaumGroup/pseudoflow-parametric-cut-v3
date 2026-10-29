/*************************************************************************
 * Hochbaum's Pseudo-flow (HPF) Algorithm for Parametric Minimum Cut     *
 * ***********************************************************************
 * Command-line driver: reads a graph in the modified DIMACS format,     *
 * calls the parametric solver (see ../core/libhpf.c), and writes the    *
 * breakpoints to an output file.                                        *
 *                                                                       *
 * Usage:                                                                *
 *   hpf <path input file> <path output file>                           *
 *                                                                       *
 * See ../core/libhpf.c for the algorithm and the input/output file      *
 * format description.                                                   *
 *************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include "../core/libhpf.h"

typedef struct nodeBreakpoint
{
    double lambda;
    uint node;


}ndb;

int cmp_ndb(const void *lp, const void *rp){
    const ndb *l = (const ndb*) lp;
    const ndb *r = (const ndb*) rp;

    if ( l->lambda < r->lambda ) return -1;
    if ( l->lambda > r->lambda ) return 1;

    return l->node - r->node;
}

static void readData(char *filename, int* numNodes, int* numArcs, int *source, int *sink,
	double ** arcMatrixPointer, double lambdaRange[2], int * roundNegativeCapacity)
/*************************************************************************
readData
*************************************************************************/
{
	char buffer[32768];

	/* define parameters */
	int arcCount = 0;
	int numRemovedArcs = 0;
	int currentNode;
	int isSourceAssigned = 0;
	int isSinkAssigned = 0;
	char sourceSinkIndicator;
	int from;
	int to;
	double constantCapacity;
	double multiplierCapacity;
	double * arcMatrix = NULL;
	double * arcMatrixNew;

	int i;

	// open input file
	FILE* f = fopen(filename, "r");
	if (f == NULL)
	{
		printf("I/O error while opening input file %s", filename);
		exit(0);
	}

	/* Read lines of input file */
	while (1)
	{
		if (fgets(buffer, sizeof buffer, f) != NULL)
		{
			switch (*buffer)
			{
			case 'p': /* initialize problem */
				sscanf(buffer, "p %d %d %lf %lf\n", numNodes, numArcs, &lambdaRange[0], &lambdaRange[1]);

				if ((arcMatrix = (double *)malloc(*numArcs * 4 * sizeof(double))) == NULL)
				{
					printf("Could not allocate memory.\n");
					exit(0);
				}

				break;
			case 'n':
				sscanf(buffer, "n %i %c\n", &currentNode, &sourceSinkIndicator);
				if (sourceSinkIndicator == 's')
				{
					/* check if source is valid */
					if (currentNode >= *numNodes || currentNode < 0)
					{
						printf("A: Nodes are labeled from 0 to <number of nodes>  - 1\n");
						exit(0);
					}
					/* check if source is assigned */
					if (isSourceAssigned)
					{
						printf("Source is already defined\n");
						exit(0);
					}
					else
					{
						*source = currentNode;
						isSourceAssigned = 1;
					}
				}
				else if (sourceSinkIndicator == 't')
				{
					/* check if sink is valid */
					if (currentNode >= *numNodes || currentNode < 0)
					{
						printf("B: Nodes are labeled from 0 to <number of nodes>  - 1\n");
						exit(0);
					}
					/* check if sink is assigned */
					if (isSinkAssigned)
					{
						printf("Sink is already defined\n");
						exit(0);
					}
					else
					{
						*sink = currentNode;
						isSinkAssigned = 1;
					}
				}
				else
				{
					printf("Node type: %c is unknown\n", sourceSinkIndicator);
					exit(0);
				}

				break;
			case 'a':
				sscanf(buffer, "a %d %d %lf %lf\n", &from, &to, &constantCapacity, &multiplierCapacity);

				if (isSinkAssigned == 0 || isSourceAssigned == 0)
				{
					printf("Source and sink need to be defined before arcs are defined.\n");
					printf("from %d to %d const cap %lf multi cap %lf \n",
									from, to, constantCapacity, multiplierCapacity);
					exit(0);
				}

				/* assign arc */
				if (from < 0 || to < 0 || from >= *numNodes || to >= *numNodes )
				{
					printf("C: Nodes are labeled from 0 to <number of nodes>  - 1\n");
					printf("from %d to %d const cap %lf multi cap %lf \n",
									from, to, constantCapacity, multiplierCapacity);
					exit(0);
				}
				else if (from == to)
				{
					printf("Node %u has a self loop which is not allowed\n", from);
					printf("from %d to %d const cap %lf multi cap %lf \n",
									from, to, constantCapacity, multiplierCapacity);
					exit(0);
				}
				else if (multiplierCapacity > 0 && from != *source)
				{
					printf("Only source adjacent arcs can have a strictly positive capacity multiplier\n");
					printf("from %d to %d const cap %lf multi cap %lf \n",
									from, to, constantCapacity, multiplierCapacity);
					exit(0);
				}
				else if (multiplierCapacity < 0 && to != *sink)
				{
					printf("Only sink adjacent arcs can have a strictly negative capacity multiplier\n");
					printf("from %d to %d const cap %lf multi cap %lf \n",
									from, to, constantCapacity, multiplierCapacity);
					exit(0);
				}
				else if (arcCount >= *numArcs)
				{
					printf("Incorrect number of arcs specified\n");
					printf("from %d to %d const cap %lf multi cap %lf \n",
									from, to, constantCapacity, multiplierCapacity);
					exit(0);
				}
				else if (to==*source || from==*sink)
				{
				  numRemovedArcs++;
				  continue;
				}

				arcMatrix[ arcCount * 4 + 0] = (double) from;
				arcMatrix[ arcCount * 4 + 1] = (double) to;
				arcMatrix[ arcCount * 4 + 2] = constantCapacity;
				arcMatrix[ arcCount * 4 + 3] = multiplierCapacity;

				++arcCount;
			}
		}
		else if (feof(f))
		{
			break;
		}
		else
		{
			printf("I/O error while reading %s\n", filename);
			exit(0);
		}
	}

	// close file
	fclose(f);

	if (numRemovedArcs>0)
	{
#ifdef VERBOSE
		printf("There are %d arcs removed\n", numRemovedArcs);
#endif
	  *numArcs-= numRemovedArcs;
	  if ((arcMatrixNew = (double *)malloc((*numArcs)*4 * sizeof(double))) == NULL)
	    {
	      printf("Could not allocate memory.\n");
	      exit(0);
	    }
	  for(i = 0;i < *numArcs * 4;++i)
		{
	   	arcMatrixNew[i] = arcMatrix[i];
	  }
	  free(arcMatrix);
	  arcMatrix = arcMatrixNew;
	}
	/* check if correct number of arcs has been specified */
	if (arcCount != *numArcs)
	{
		printf("Incorrect number of arcs specified\n");
		exit(0);
	}
	else if (isSourceAssigned == 0)
	{
		printf("Source is not assigned\n");
		exit(0);
	}
	else if (isSinkAssigned == 0)
	{
		printf("Sink is not assigned\n");
		exit(0);
	}
	else if (*source == *sink)
	{
		printf("The source node and sink node need to be distinct\n");
		exit(0);
	}

	*arcMatrixPointer = arcMatrix;
}

static void writeOutput (char *filename, int numBreakpoints, int numNodes, double* breakpoints,
	double* cuts, int* stats, double* times)
{
/*************************************************************************
writeOutput
*************************************************************************/
	int i;

	// open outputFile
	FILE* f = fopen(filename,"w");
	if (f == NULL)
	{
		printf("I/O error while opening output file %s", filename);
		exit(0);
	}

	/* print times */
	fprintf(f, "t %.3lf %.3lf %.3lf\n", times[0], times[1], times[2]);
	/* print stats */
	fprintf(f, "s %d %d %d %d %d\n", stats[0], stats[1], stats[2], stats[3], stats[4]);

	/* print lambda values */
    ndb *brarr;
    if ((brarr= (ndb *)malloc(numNodes *  sizeof(ndb))) == NULL)
    {
        printf("Could not allocate memory.\n");
        exit(0);
    }

	for (i = 0; i < numNodes; i++)
	{
        brarr[i].lambda = cuts[i];
        brarr[i].node = i;
	}

    qsort(brarr, numNodes, sizeof(ndb), cmp_ndb);

    /* count distinct lambda values so p matches the actual number of l-lines */
    int numLambdas = 0;
    double prevLambda = brarr[0].lambda - 10.0;
    for (i = 0; i < numNodes; i++)
    {
        if (brarr[i].lambda != prevLambda)
        {
            numLambdas++;
            prevLambda = brarr[i].lambda;
        }
    }
    fprintf(f, "p %d\n", numLambdas);

    double clambda = brarr[0].lambda - 10.0;
    int first = 1;
	for (i = 0; i < numNodes; i++)
	{
        int node = brarr[i].node;
        double clam = brarr[i].lambda;

        if ( clam != clambda ){

            if(!first)
                fprintf(f, "\n");
            fprintf(f, "l %.10lf ", clam);
            clambda = clam;
            first = 0;
        }

		fprintf(f, "%d ", node);

	}

    free(brarr);

	// close output file
	fclose(f);
}


int main(int argc, char **argv)
/*************************************************************************
main - Main function
*************************************************************************/
{
	// check number of input arguments
	if (argc != 3)
	{
		printf("Incorrect number of input arguments. Call hpf.exe inputFile outputFile\n");
		exit(0);
	}

	// prepare input solver
	int numNodes;
	int numArcs;
	int source;
	int sink;
	double* arcMatrix;
	double lambdaRange[2];
	int roundNegativeCapacity=0;

	readData(argv[1], &numNodes, &numArcs, &source, &sink, &arcMatrix, lambdaRange, &roundNegativeCapacity);

#ifdef VERBOSE
	printf("NumNodes: %d\n", numNodes);
	printf("NumArcs: %d\n", numArcs);
	printf("Lambda Range: [%.15lf, %.15lf]\n", lambdaRange[0], lambdaRange[1]);
#endif

	// prepare output solver
	int numBreakpoints;
	double *cuts;
	double *breakpoints;
	int stats[5];
	double times[3];

	hpf_solve(numNodes, numArcs, source, sink, arcMatrix, lambdaRange, roundNegativeCapacity,
		&numBreakpoints, &cuts, &breakpoints, stats, times );

#ifdef VERBOSE
	printf("Stats: [%d, %d, %d, %d, %d]\n", stats[0],stats[1],stats[2],stats[3],stats[4]);
	printf("times: [%lf, %lf, %lf]\n", times[0],times[1],times[2]);
	printf("Num breakpoints: %d\n", numBreakpoints);
#endif

	writeOutput(argv[2], numBreakpoints, numNodes, breakpoints, cuts, stats, times);

    free(arcMatrix);
    free(breakpoints);
    free(cuts);

	return 1;
}
