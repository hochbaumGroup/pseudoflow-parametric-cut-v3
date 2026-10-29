/*************************************************************************
 * Hochbaum's Pseudo-flow (HPF) Algorithm for Parametric Minimimum Cut   *
 * ***********************************************************************
 Copyright © 2017. The Regents of the University of California (Regents). All Rights Reserved.

 Permission to use, copy, modify, and distribute this software and its documentation for educational, research, and not-for-profit purposes, without fee and without a signed licensing agreement, is hereby granted, provided that the above copyright notice, this paragraph and the following two paragraphs appear in all copies, modifications, and distributions. Contact The Office of Technology Licensing, UC Berkeley, 2150 Shattuck Avenue, Suite 510, Berkeley, CA 94720-1620, (510) 643-7201, for commercial licensing opportunities. Created by Quico Spaen and Dorit S. Hochbaum, Department of Industrial Engineering and Operations Research, University of California, Berkeley. This work is adapted from the Pseudoflow implementation by Bala Chandran and Dorit S. Hochbaum available at https://riot.ieor.berkeley.edu/Applications/Pseudoflow/maxflow.html

 IN NO EVENT SHALL REGENTS BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES, INCLUDING LOST PROFITS, ARISING OUT OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF REGENTS HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

 REGENTS SPECIFICALLY DISCLAIMS ANY WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE AND ACCOMPANYING DOCUMENTATION, IF ANY, PROVIDED HEREUNDER IS PROVIDED "AS IS". REGENTS HAS NO OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.

 * The HPF algorithm for finding a minimum cut in a graph is described in: *
 * [1] D.S. Hochbaum, "The Pseudoflow algorithm: A new algorithm for the *
 * maximum flow problem", Operations Research, 58(4):992-1009, 2008.      *
 *                                                                       *
 * The algorithm was found to be fast in theory (see the above paper)    *
 * and in practice (see:                                                 *
 * [2] D.S. Hochbaum and B. Chandran, "A Computational Study of the      *
 * Pseudoflow and Push-relabel Algorithms for the Maximum Flow Problem", *
 * Operations Research, 57(2):358-376, 2009.)                            *
 *                                                                       *
 * This file implements a fully parametric variant that solves the       *
 * minimum cut for every value of the parameter lambda in a given range  *
 * [lower bound, upper bound]. Source-adjacent arc capacities must be     *
 * non-decreasing in lambda and sink-adjacent arc capacities must be      *
 * non-increasing in lambda; both are 2-piecewise linear of the form      *
 * capacity = max(0, constant + multiplier * lambda). The algorithm finds *
 * all breakpoints at which the source set of the minimum cut changes by  *
 * recursively concluding that an interval contains 0, 1, or more         *
 * breakpoints, splitting it in two whenever it contains more than one.    *
 *                                                                       *
 * INPUT FILE                                                            *
 * **********                                                            *
 * The input file is assumed to be in a modified DIMACS format:          *
 * c <comment lines>                                                     *
 * p <# nodes> <# arcs> <lower bound> <upper bound>                      *
 * n <source node> s                                                     *
 * n <sink node> t                                                       *
 * a <from-node> <to-node> <constant capacity> <lambda multiplier>       *
 * where the following conditions are satisfied:                         *
 * - Nodes are labeled 0 .. <# nodes> - 1                                *
 * - <lambda multiplier> is non-negative if <from-node> == <source node> *
 *       and <to-node> != <sink-node>                                    *
 * - <lambda multiplier> is non-positive if <from-node> != <source node> *
 *       and <to-node> == <sink-node>                                    *
 * - <lambda multiplier> is zero if <from-node> != <source node>         *
 *       and <to-node> != <sink-node>                                    *
 *                                                                       *
 * OUTPUT FILE                                                           *
 * ***********                                                           *
 * The solver generates the following output file:                       *
 * t <time (sec) read data> <time (sec) initialize> <time (sec) solve>   *
 * s <# arc scans> <# mergers> <# pushes> <# relabels> <# gap>           *
 * p <number of breakpoints = k>                                         *
 * l <lambda> <node> <node> ...                                          *
 *   one line per distinct breakpoint lambda, listing the nodes that     *
 *   enter the source set of the minimum cut at that lambda value.       *
 *                                                                       *
 * When using this code, please cite:                                    *
 * References [1] and [2] above and:                                     *
 * Q. Spaen, B. Fishbain and D.S. Hochbaum, "Hochbaum's Pseudo-flow C    *
 * Implementation", http://riot.ieor.berkeley.edu/riot/Applications/     *
 * Pseudoflow/maxflow.html                                               *
 *************************************************************************/

#define _CRTDBG_MAP_ALLOC
#include "stdio.h"
#include <assert.h>
#include "stdlib.h"
#include "string.h"
#include "time.h"
#include <math.h>
#include <limits.h>

/*************************************************************************
Definitions
*************************************************************************/
#define MAX_LEVELS  300
#define VERSION 3.3

#define NODE_NONE UINT_MAX
#define ARC_NONE  UINT_MAX

typedef unsigned int uint;
typedef long int lint;
typedef long long int llint;
typedef unsigned long long int ullint;

/*************************************************************************
Core struct definitions — layouts unchanged; accessor layer above them
*************************************************************************/

typedef struct Arc
{
    uint from;
    uint to;
    double flow;
    double capacity;
    double constant;
    double multiplier;
    uint direction;
} Arc;

typedef struct Node
{
    uint parent;
    uint childList;
    uint nextScan;
    Arc **outOfTree;
    uint arcToParent;
    uint next;
    uint prev;
    double excess;
    uint visited;
    uint numAdjacent;
    uint number;
    int originalIndex;
    uint label;
    uint numOutOfTree;
    uint nextArc;
} Node;

/*************************************************************************
Arc inline accessors

Scalar fields: trivial get/set; compiler eliminates all overhead.

Endpoint fields (from/to): the get accessor takes the owning node array as
a context parameter.  Today that parameter is ignored (the pointer is stored
directly in the Arc); it will be used once from/to become uint indices.
The index-based get/set pair carries the node list explicitly so future
call sites require no changes when the layout switches.
*************************************************************************/

static inline double arc_get_capacity(const Arc *a)           { return a->capacity; }
static inline void   arc_set_capacity(Arc *a, double v)        { a->capacity = v; }
static inline double arc_get_flow(const Arc *a)                { return a->flow; }
static inline void   arc_set_flow(Arc *a, double v)            { a->flow = v; }
static inline void   arc_add_flow(Arc *a, double delta)        { a->flow += delta; }
static inline double arc_get_constant(const Arc *a)            { return a->constant; }
static inline void   arc_set_constant(Arc *a, double v)        { a->constant = v; }
static inline void   arc_add_constant(Arc *a, double delta)    { a->constant += delta; }
static inline double arc_get_multiplier(const Arc *a)          { return a->multiplier; }
static inline void   arc_set_multiplier(Arc *a, double v)      { a->multiplier = v; }
static inline void   arc_add_multiplier(Arc *a, double delta)  { a->multiplier += delta; }
static inline uint   arc_get_direction(const Arc *a)           { return a->direction; }
static inline void   arc_set_direction(Arc *a, uint v)         { a->direction = v; }

/* Pointer get — resolves uint index to pointer. */
static inline Node *arc_get_from(const Arc *a, const Node *nodeList)
    { return (Node*)&nodeList[a->from]; }
static inline Node *arc_get_to(const Arc *a, const Node *nodeList)
    { return (Node*)&nodeList[a->to]; }

/* Index get — direct field read; nodeList unused. */
static inline uint arc_get_from_idx(const Arc *a, const Node *nodeList)
    { (void)nodeList; return a->from; }
static inline uint arc_get_to_idx(const Arc *a, const Node *nodeList)
    { (void)nodeList; return a->to; }

/* Index set — direct field write; nodeList unused. */
static inline void arc_set_from_idx(Arc *a, uint idx, const Node *nodeList)
    { (void)nodeList; a->from = idx; }
static inline void arc_set_to_idx(Arc *a, uint idx, const Node *nodeList)
    { (void)nodeList; a->to = idx; }

/*************************************************************************
Node inline accessors
*************************************************************************/

static inline double node_get_excess(const Node *n)            { return n->excess; }
static inline void   node_set_excess(Node *n, double v)        { n->excess = v; }
static inline void   node_add_excess(Node *n, double delta)    { n->excess += delta; }
static inline uint   node_get_label(const Node *n)             { return n->label; }
static inline void   node_set_label(Node *n, uint v)           { n->label = v; }
static inline uint   node_get_num_adjacent(const Node *n)      { return n->numAdjacent; }
static inline void   node_inc_num_adjacent(Node *n)            { ++n->numAdjacent; }
static inline uint   node_get_num_out_of_tree(const Node *n)   { return n->numOutOfTree; }
static inline void   node_set_num_out_of_tree(Node *n, uint v) { n->numOutOfTree = v; }
static inline void   node_inc_num_out_of_tree(Node *n)         { ++n->numOutOfTree; }
static inline uint   node_get_next_arc(const Node *n)          { return n->nextArc; }
static inline void   node_set_next_arc(Node *n, uint v)        { n->nextArc = v; }
static inline int    node_get_original_index(const Node *n)    { return n->originalIndex; }
static inline void   node_set_original_index(Node *n, int v)   { n->originalIndex = v; }
static inline uint   node_get_number(const Node *n)            { return n->number; }
static inline void   node_set_number(Node *n, uint v)          { n->number = v; }

/* Append arc to a node's out-of-tree list. */
static inline void node_push_out_of_tree(Node *n, Arc *a)
{
    n->outOfTree[n->numOutOfTree] = a;
    ++n->numOutOfTree;
}

/*************************************************************************
Remaining struct definitions
*************************************************************************/

typedef struct CutProblem
{
    uint numNodesInList;
    uint numSourceSet;
    uint numSinkSet;
    uint numArcs;
    uint solved;
    double lambdaValue;
    Arc *arcList;
    Node *nodeList;
    double cutValue;
    Node *sourceSet;
    Node *sinkSet;
    char *optimalSourceSetIndicator;
    double cutFunctionA;
    double cutFunctionB;
} CutProblem;

typedef struct Root
{
    uint start;
    uint end;
} Root;

/*
 * HpfInstance — all state for one hpf_solve invocation.
 * Stack-allocated in hpf_solve; passed as HpfInstance* to every function.
 * Eliminates all module-level global variables.
 */
typedef struct HpfInstance
{
    /* problem description */
    uint    numNodesSuper;
    uint    numArcsSuper;
    uint    sourceSuper;
    uint    sinkSuper;
    Node   *nodeListSuper;
    Arc    *arcListSuper;
    double  lambdaLow;
    double  lambdaHigh;
    uint    useParametricCut;
    uint    roundNegativeCapacity;
    uint    isSymmetric;  /* 1 if all parametric arcs connect to sourceSuper or sinkSuper */
    double  tol;
    /* parametric arc list (sorted by breakpoint; used for piecewise intersection) */
    uint    numParametricArcs;
    Arc   **paramArcList;
    /* per-node breakpoint output */
    double *nodeBreakpoints;
    /* cumulative solve statistics */
    uint    numArcScans;
    uint    numPushes;
    uint    numMergers;
    uint    numRelabels;
    uint    numGaps;
    /*
     * Scratch arenas: allocated once in readGraphSuper to numNodesSuper.
     * Reused safely across all recursion levels because contracted
     * sub-problems are always smaller than the original.
     */
    int    *nodeMap;
    int    *sourceAdjacentArcIndices;
    int    *sinkAdjacentArcIndices;
    char   *pdifferenceCache;
    uint   *pdiffListCache;   /* index list of difference nodes; filled by differenceSourceSetsCount */
} HpfInstance;

/*
 * SolveContext — per-solveProblem state.
 * Stack-allocated in solveProblem; passed to all pseudoflow-phase functions.
 * Stats are accumulated locally here and flushed into HpfInstance on return.
 */
typedef struct SolveContext
{
    uint    numNodes;
    uint    numArcs;
    uint    source;
    uint    sink;
    uint    highestStrongLabel;
    uint    lowestPositiveExcessNode;
    Node   *nodesList;
    Arc    *arcList;
    Root   *strongRoots;
    uint   *labelCount;
    /* local stats — accumulated into HpfInstance at end of solveProblem */
    uint    numArcScans;
    uint    numPushes;
    uint    numMergers;
    uint    numRelabels;
    uint    numGaps;
} SolveContext;

#ifndef TRUE
#define TRUE (1)
#endif
#ifndef FALSE
#define FALSE (0)
#endif

/*************************************************************************
Math helpers
*************************************************************************/

void libfree(void *p) { free(p); }

static int isExcess(double excess)
{
    if (excess < 0) return -1;
    if (excess > 0) return  1;
    return 0;
}

/*************************************************************************
Node / arc initializers (no global state)
*************************************************************************/

static void createOutOfTree(Node *nd)
{
    if (node_get_num_adjacent(nd))
    {
        if ((nd->outOfTree = (Arc **)malloc(node_get_num_adjacent(nd) * sizeof(Arc *))) == NULL)
        { printf("Out of memory\n"); exit(0); }
    }
}

static void initializeArc(Arc *ac)
{
    ac->from = NODE_NONE;
    ac->to   = NODE_NONE;
    arc_set_capacity(ac, 0.0);
    arc_set_flow(ac, 0.0);
    arc_set_direction(ac, 1);
    arc_set_constant(ac, 0.0);
    arc_set_multiplier(ac, 0.0);
}

static void initializeNode(Node *nd, const uint n)
{
    node_set_label(nd, 0);
    node_set_excess(nd, 0.0);
    nd->parent      = NODE_NONE;
    nd->childList   = NODE_NONE;
    nd->nextScan    = NODE_NONE;
    node_set_next_arc(nd, 0);
    node_set_num_out_of_tree(nd, 0);
    nd->arcToParent = ARC_NONE;
    nd->next = NODE_NONE;
    nd->prev = NODE_NONE;
    nd->visited = 0;
    nd->numAdjacent = 0;
    node_set_number(nd, n);
    node_set_original_index(nd, -10);
    nd->outOfTree = NULL;
}

static void initializeRoot(Root *rt) { rt->start = NODE_NONE; rt->end = NODE_NONE; }
static void freeRoot(Root *rt)       { rt->start = NODE_NONE; rt->end = NODE_NONE; }

/*************************************************************************
HpfInstance lifecycle
*************************************************************************/

static void hpf_instance_init(HpfInstance *inst)
{
    memset(inst, 0, sizeof(*inst));
    inst->tol              = 1e-9;
    inst->useParametricCut = 1;
}

static void hpf_instance_destroy(HpfInstance *inst)
{
    free(inst->nodeListSuper);            inst->nodeListSuper = NULL;
    free(inst->arcListSuper);             inst->arcListSuper  = NULL;
    free(inst->nodeBreakpoints);          inst->nodeBreakpoints = NULL;
    free(inst->paramArcList);             inst->paramArcList  = NULL;
    free(inst->nodeMap);                  inst->nodeMap = NULL;
    free(inst->sourceAdjacentArcIndices); inst->sourceAdjacentArcIndices = NULL;
    free(inst->sinkAdjacentArcIndices);   inst->sinkAdjacentArcIndices   = NULL;
    free(inst->pdifferenceCache);         inst->pdifferenceCache = NULL;
    free(inst->pdiffListCache);           inst->pdiffListCache   = NULL;
}

/*************************************************************************
Bucket / tree helpers (no global state)
*************************************************************************/

static void addOutOfTreeNode(Node *n, Arc *out)
{
    node_push_out_of_tree(n, out);
}

static void addToStrongBucket(Node *newRoot, Root *rootBucket, Node *nodesList)
{
    uint newRootIdx = (uint)(newRoot - nodesList);
    if (rootBucket->start != NODE_NONE)
    {
        nodesList[rootBucket->end].next = newRootIdx;
        rootBucket->end = newRootIdx;
        newRoot->next = NODE_NONE;
    }
    else
    {
        rootBucket->start = newRootIdx;
        rootBucket->end   = newRootIdx;
        newRoot->next = NODE_NONE;
    }
}

static inline int addRelationship(Node *newParent, Node *child, Node *nodesList)
{
    uint childIdx     = (uint)(child     - nodesList);
    uint newParentIdx = (uint)(newParent - nodesList);
    child->parent = newParentIdx;
    child->next   = newParent->childList;
#ifdef PREV_CHILDLIST
    if (newParent->childList != NODE_NONE)
        nodesList[newParent->childList].prev = childIdx;
#endif
    newParent->childList = childIdx;
    return 0;
}

static inline void breakRelationship(Node *oldParent, Node *child, Node *nodesList)
{
    uint childIdx = (uint)(child - nodesList);
    child->parent = NODE_NONE;

    if (oldParent->childList == childIdx)
    {
        oldParent->childList = child->next;
        child->next = NODE_NONE;
        return;
    }
#ifdef PREV_CHILDLIST
    Node *current = &nodesList[child->prev];
    if (child->next != NODE_NONE) nodesList[child->next].prev = child->prev;
#else
    Node *current = &nodesList[oldParent->childList];
    while (current->next != childIdx) current = &nodesList[current->next];
#endif
    current->next = child->next;
    child->next = NODE_NONE;
}

/*************************************************************************
Pseudoflow phase — all functions take SolveContext *ctx
*************************************************************************/

static void liftAll(SolveContext * restrict ctx, Node *rootNode)
{
    Node *temp, *current = rootNode;
    Node *nodesList = ctx->nodesList;
    current->nextScan = current->childList;

    --ctx->labelCount[node_get_label(current)];
    node_set_label(current, ctx->numNodes);

    for (; current; current = (current->parent != NODE_NONE) ? &nodesList[current->parent] : NULL)
    {
        while (current->nextScan != NODE_NONE)
        {
            temp = &nodesList[current->nextScan];
            current->nextScan = temp->next;
            current = temp;
            current->nextScan = current->childList;
            --ctx->labelCount[node_get_label(current)];
            node_set_label(current, ctx->numNodes);
        }
    }
}

static void merge(SolveContext * restrict ctx, Node *parent, Node *child, Arc *newArc)
{
    Arc *oldArc;
    Node *current = child, *oldParent, *newParent = parent;
    Node *nodesList = ctx->nodesList;

    ++ctx->numMergers;

    while (current->parent != NODE_NONE)
    {
        oldArc               = &ctx->arcList[current->arcToParent];
        current->arcToParent = (uint)(newArc - ctx->arcList);
        oldParent            = &nodesList[current->parent];
        breakRelationship(oldParent, current, nodesList);
        addRelationship(newParent, current, nodesList);
        newParent = current;
        current   = oldParent;
        newArc    = oldArc;
        arc_set_direction(newArc, 1 - arc_get_direction(newArc));
    }

    current->arcToParent = (uint)(newArc - ctx->arcList);
    addRelationship(newParent, current, nodesList);
}

static inline void pushUpward(SolveContext * restrict ctx, Arc *currentArc, Node *child,
    Node *parent, const double resCap)
{
    ++ctx->numPushes;

    if (isExcess(resCap - node_get_excess(child)) >= 0)
    {
        node_add_excess(parent, node_get_excess(child));
        arc_add_flow(currentArc, node_get_excess(child));
        node_set_excess(child, 0);
        return;
    }

    arc_set_direction(currentArc, 0);
    node_add_excess(parent, resCap);
    node_add_excess(child, -resCap);
    arc_set_flow(currentArc, arc_get_capacity(currentArc));
    node_push_out_of_tree(parent, currentArc);
    breakRelationship(parent, child, ctx->nodesList);
    addToStrongBucket(child, &ctx->strongRoots[node_get_label(child)], ctx->nodesList);
}

static inline void pushDownward(SolveContext * restrict ctx, Arc *currentArc, Node *child,
    Node *parent, const double flow)
{
    ++ctx->numPushes;

    if (isExcess(flow - node_get_excess(child)) >= 0)
    {
        node_add_excess(parent, node_get_excess(child));
        arc_add_flow(currentArc, -node_get_excess(child));
        node_set_excess(child, 0);
        return;
    }

    arc_set_direction(currentArc, 1);
    node_add_excess(child, -flow);
    node_add_excess(parent, flow);
    arc_set_flow(currentArc, 0);
    node_push_out_of_tree(parent, currentArc);
    breakRelationship(parent, child, ctx->nodesList);
    addToStrongBucket(child, &ctx->strongRoots[node_get_label(child)], ctx->nodesList);
}

static void pushExcess(SolveContext * restrict ctx, Node *strongRoot)
{
    Node *current, *parent;
    Arc *arcToParent;
    double prevEx = 1;

    for (current = strongRoot;
         (isExcess(node_get_excess(current)) && current->parent != NODE_NONE);
         current = parent)
    {
        parent      = &ctx->nodesList[current->parent];
        prevEx      = node_get_excess(parent);
        arcToParent = &ctx->arcList[current->arcToParent];

        if (arc_get_direction(arcToParent))
            pushUpward(ctx, arcToParent, current, parent,
                arc_get_capacity(arcToParent) - arc_get_flow(arcToParent));
        else
            pushDownward(ctx, arcToParent, current, parent, arc_get_flow(arcToParent));
    }

    if ((isExcess(node_get_excess(current)) > 0) && (isExcess(prevEx) <= 0))
        addToStrongBucket(current, &ctx->strongRoots[node_get_label(current)], ctx->nodesList);
}

static Arc *findWeakNode(SolveContext * restrict ctx, Node *strongNode, Node **weakNode)
{
    uint i, size;
    Arc *out;

    size = node_get_num_out_of_tree(strongNode);

    for (i = node_get_next_arc(strongNode); i < size; ++i)
    {
        ++ctx->numArcScans;
        if (node_get_label(arc_get_to(strongNode->outOfTree[i], ctx->nodesList)) == (ctx->highestStrongLabel - 1))
        {
            node_set_next_arc(strongNode, i);
            out = strongNode->outOfTree[i];
            *weakNode = arc_get_to(out, ctx->nodesList);
            --strongNode->numOutOfTree;
            strongNode->outOfTree[i] = strongNode->outOfTree[strongNode->numOutOfTree];
            return out;
        }
        else if (node_get_label(arc_get_from(strongNode->outOfTree[i], ctx->nodesList)) == (ctx->highestStrongLabel - 1))
        {
            node_set_next_arc(strongNode, i);
            out = strongNode->outOfTree[i];
            *weakNode = arc_get_from(out, ctx->nodesList);
            --strongNode->numOutOfTree;
            strongNode->outOfTree[i] = strongNode->outOfTree[strongNode->numOutOfTree];
            return out;
        }
    }

    node_set_next_arc(strongNode, node_get_num_out_of_tree(strongNode));
    return NULL;
}

static void checkChildren(SolveContext * restrict ctx, Node *curNode)
{
    for (; curNode->nextScan != NODE_NONE; curNode->nextScan = ctx->nodesList[curNode->nextScan].next)
    {
        if (node_get_label(&ctx->nodesList[curNode->nextScan]) == node_get_label(curNode))
            return;
    }
    --ctx->labelCount[node_get_label(curNode)];
    node_set_label(curNode, node_get_label(curNode) + 1);
    ++ctx->labelCount[node_get_label(curNode)];
    ++ctx->numRelabels;
    node_set_next_arc(curNode, 0);
}

static void simpleInitialization(SolveContext * restrict ctx)
{
    uint i, size;
    Arc *tempArc;

    size = ctx->nodesList[ctx->source].numOutOfTree;
    for (i = 0; i < size; ++i)
    {
        tempArc = ctx->nodesList[ctx->source].outOfTree[i];
        arc_set_flow(tempArc, arc_get_capacity(tempArc));
        node_add_excess(arc_get_to(tempArc, ctx->nodesList), arc_get_capacity(tempArc));
    }

    size = ctx->nodesList[ctx->sink].numOutOfTree;
    for (i = 0; i < size; ++i)
    {
        tempArc = ctx->nodesList[ctx->sink].outOfTree[i];
        arc_set_flow(tempArc, arc_get_capacity(tempArc));
        node_add_excess(arc_get_from(tempArc, ctx->nodesList), -arc_get_capacity(tempArc));
    }

    node_set_excess(&ctx->nodesList[ctx->source], 0);
    node_set_excess(&ctx->nodesList[ctx->sink],   0);

    for (i = 0; i < ctx->numNodes; ++i)
    {
        if (isExcess(node_get_excess(&ctx->nodesList[i])) > 0)
        {
            node_set_label(&ctx->nodesList[i], 1);
            ++ctx->labelCount[1];
            addToStrongBucket(&ctx->nodesList[i], &ctx->strongRoots[1], ctx->nodesList);
        }
    }

    node_set_label(&ctx->nodesList[ctx->source], ctx->numNodes);
    node_set_label(&ctx->nodesList[ctx->sink],   0);
    ctx->labelCount[0] = (ctx->numNodes - 2) - ctx->labelCount[1];
}

static Node *getHighestStrongRoot(SolveContext * restrict ctx)
{
    uint i;
    Node *strongRoot;

    for (i = ctx->highestStrongLabel; i > 0; --i)
    {
        if (ctx->strongRoots[i].start != NODE_NONE)
        {
            ctx->highestStrongLabel = i;
            if (ctx->labelCount[i - 1])
            {
                strongRoot = &ctx->nodesList[ctx->strongRoots[i].start];
                ctx->strongRoots[i].start = strongRoot->next;
                strongRoot->next = NODE_NONE;
                return strongRoot;
            }

            while (ctx->strongRoots[i].start != NODE_NONE)
            {
                ++ctx->numGaps;
                strongRoot = &ctx->nodesList[ctx->strongRoots[i].start];
                ctx->strongRoots[i].start = strongRoot->next;
                liftAll(ctx, strongRoot);
            }
        }
    }

    if (ctx->strongRoots[0].start == NODE_NONE)
        return NULL;

    while (ctx->strongRoots[0].start != NODE_NONE)
    {
        strongRoot = &ctx->nodesList[ctx->strongRoots[0].start];
        ctx->strongRoots[0].start = strongRoot->next;
        node_set_label(strongRoot, 1);
        --ctx->labelCount[0];
        ++ctx->labelCount[1];
        ++ctx->numRelabels;
        addToStrongBucket(strongRoot, &ctx->strongRoots[node_get_label(strongRoot)], ctx->nodesList);
    }

    ctx->highestStrongLabel = 1;
    strongRoot = &ctx->nodesList[ctx->strongRoots[1].start];
    ctx->strongRoots[1].start = strongRoot->next;
    strongRoot->next = NODE_NONE;
    return strongRoot;
}

static void processRoot(SolveContext * restrict ctx, Node *strongRoot)
{
    Node *temp, *strongNode = strongRoot, *weakNode;
    Arc *out;
    Node *nodesList = ctx->nodesList;

    strongRoot->nextScan = strongRoot->childList;

    if ((out = findWeakNode(ctx, strongRoot, &weakNode)))
    {
        merge(ctx, weakNode, strongNode, out);
        pushExcess(ctx, strongRoot);
        return;
    }

    checkChildren(ctx, strongRoot);

    while (strongNode)
    {
        while (strongNode->nextScan != NODE_NONE)
        {
            temp = &nodesList[strongNode->nextScan];
            strongNode->nextScan = temp->next;
            strongNode = temp;
            strongNode->nextScan = strongNode->childList;

            if ((out = findWeakNode(ctx, strongNode, &weakNode)))
            {
                merge(ctx, weakNode, strongNode, out);
                pushExcess(ctx, strongRoot);
                return;
            }

            checkChildren(ctx, strongNode);
        }

        if (strongNode->parent != NODE_NONE)
        {
            strongNode = &nodesList[strongNode->parent];
            checkChildren(ctx, strongNode);
        }
        else
        {
            strongNode = NULL;
        }
    }

    addToStrongBucket(strongRoot, &ctx->strongRoots[node_get_label(strongRoot)], nodesList);
    ++ctx->highestStrongLabel;
}

static void pseudoflowPhase1(SolveContext * restrict ctx)
{
    Node *strongRoot;
    while ((strongRoot = getHighestStrongRoot(ctx)))
        processRoot(ctx, strongRoot);
}

static void createMemoryStructures(SolveContext * restrict ctx)
{
    uint from, to, i;
    double capacity;

    for (i = 0; i < ctx->numNodes; ++i)
        createOutOfTree(&ctx->nodesList[i]);

    for (i = 0; i < ctx->numArcs; i++)
    {
        to       = arc_get_to(&ctx->arcList[i], ctx->nodesList)->number;
        from     = arc_get_from(&ctx->arcList[i], ctx->nodesList)->number;
        capacity = arc_get_capacity(&ctx->arcList[i]);

        if (!((ctx->source == to) || (ctx->sink == from) || (from == to)))
        {
            if ((ctx->source == from) && (to == ctx->sink))
            {
                arc_set_flow(&ctx->arcList[i], capacity);
            }
            else if (to == ctx->sink)
            {
                addOutOfTreeNode(&ctx->nodesList[to], &ctx->arcList[i]);
            }
            else
            {
                addOutOfTreeNode(&ctx->nodesList[from], &ctx->arcList[i]);
            }
        }
    }

    if ((ctx->strongRoots = (Root *)malloc(ctx->numNodes * sizeof(Root))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    if ((ctx->labelCount = (uint *)malloc(ctx->numNodes * sizeof(uint))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }

    for (i = 0; i < ctx->numNodes; ++i)
    {
        initializeRoot(&ctx->strongRoots[i]);
        ctx->labelCount[i] = 0;
    }
}

static void freeMemorySolve(SolveContext * restrict ctx)
{
    uint i;
    for (i = 0; i < ctx->numNodes; ++i)
        freeRoot(&ctx->strongRoots[i]);

    free(ctx->strongRoots);
    ctx->strongRoots = NULL;

    for (i = 0; i < ctx->numNodes; ++i)
    {
        if (ctx->nodesList[i].outOfTree)
        {
            free(ctx->nodesList[i].outOfTree);
            ctx->nodesList[i].outOfTree = NULL;
        }
    }

    free(ctx->labelCount);
    ctx->labelCount = NULL;
}

/*************************************************************************
Sort helpers (no global state)
*************************************************************************/

static inline void quickSort(Arc **arr, const uint first, const uint last)
{
    int i = 0, j, L = first, R = last, beg[MAX_LEVELS], end[MAX_LEVELS], temp = 0;
    Arc *swap;

    if ((R - L) <= 5)
    {
        for (i = R; (i > L); --i)
        {
            swap = NULL;
            for (j = L; j < i; ++j)
            {
                if (isExcess(arc_get_flow(arr[j]) - arc_get_flow(arr[j+1])) < 0)
                {
                    swap     = arr[j];
                    arr[j]   = arr[j+1];
                    arr[j+1] = swap;
                }
            }
            if (!swap) return;
        }
        return;
    }

    beg[0] = first;
    end[0] = last + 1;

    while (i >= 0)
    {
        L = beg[i];
        R = end[i] - 1;

        if (L < R)
        {
            swap = arr[L];
            while (L < R)
            {
                while ((isExcess(arc_get_flow(arr[R]) - arc_get_flow(swap)) >= 0) && (L < R)) R--;
                if (L < R) { arr[L] = arr[R]; L++; }
                while ((isExcess(arc_get_flow(arr[L]) - arc_get_flow(swap)) <= 0) && (L < R)) L++;
                if (L < R) { arr[R] = arr[L]; R--; }
            }
            arr[L]   = swap;
            beg[i+1] = L + 1;
            end[i+1] = end[i];
            end[i++] = L;

            if ((end[i] - beg[i]) > (end[i-1] - beg[i-1]))
            {
                temp = beg[i]; beg[i] = beg[i-1]; beg[i-1] = temp;
                temp = end[i]; end[i] = end[i-1]; end[i-1] = temp;
            }
        }
        else
        {
            i--;
        }
    }
}

static inline void sort(Node *current)
{
    if (node_get_num_out_of_tree(current) > 1)
        quickSort(current->outOfTree, 0, node_get_num_out_of_tree(current) - 1);
}

static inline void minisort(Node *current)
{
    Arc *temp = current->outOfTree[node_get_next_arc(current)];
    uint i, size = node_get_num_out_of_tree(current);
    double tempflow = arc_get_flow(temp);

    for (i = node_get_next_arc(current) + 1;
         ((i < size) && (isExcess(tempflow - arc_get_flow(current->outOfTree[i])) < 0));
         ++i)
    {
        current->outOfTree[i-1] = current->outOfTree[i];
    }
    current->outOfTree[i-1] = temp;
}

/*************************************************************************
Graph reading
*************************************************************************/

static void readGraphSuper(HpfInstance *inst, const double * restrict arcMatrix)
{
    if ((inst->nodeListSuper = (Node *)malloc(inst->numNodesSuper * sizeof(Node))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }

    if ((inst->nodeBreakpoints = (double *)malloc(inst->numNodesSuper * sizeof(double))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }

    if ((inst->arcListSuper = (Arc *)malloc(inst->numArcsSuper * sizeof(Arc))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }

    /* scratch arenas — numNodesSuper is the upper bound for all recursion levels */
    if ((inst->nodeMap = (int *)malloc(inst->numNodesSuper * sizeof(int))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    if ((inst->sourceAdjacentArcIndices = (int *)malloc(inst->numNodesSuper * sizeof(int))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    if ((inst->sinkAdjacentArcIndices = (int *)malloc(inst->numNodesSuper * sizeof(int))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    if ((inst->pdifferenceCache = (char *)malloc(inst->numNodesSuper * sizeof(char))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    if ((inst->pdiffListCache = (uint *)malloc(inst->numNodesSuper * sizeof(uint))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }

    for (int i = 0; i < (int)inst->numNodesSuper; ++i)
    {
        initializeNode(&inst->nodeListSuper[i], (uint)i);
        node_set_original_index(&inst->nodeListSuper[i], i);
        inst->nodeBreakpoints[i] = inst->lambdaHigh;
    }

#ifdef VERBOSE
    printf("c source is %d sink is %d\n", inst->sourceSuper, inst->sinkSuper);
#endif
    inst->nodeBreakpoints[inst->sourceSuper] = inst->lambdaLow;
    inst->nodeBreakpoints[inst->sinkSuper]   = inst->lambdaHigh;

    for (int i = 0; i < (int)inst->numArcsSuper; ++i)
        initializeArc(&inst->arcListSuper[i]);

    if (inst->lambdaLow == inst->lambdaHigh)
        inst->useParametricCut = 0;

    for (int i = 0; i < (int)inst->numArcsSuper; ++i)
    {
        int    from               = (int)arcMatrix[i * 4 + 0];
        int    to                 = (int)arcMatrix[i * 4 + 1];
        double constantCapacity   = arcMatrix[i * 4 + 2];
        double multiplierCapacity = arcMatrix[i * 4 + 3];

        arc_set_constant(&inst->arcListSuper[i], constantCapacity);
        arc_set_multiplier(&inst->arcListSuper[i], multiplierCapacity);
        arc_set_from_idx(&inst->arcListSuper[i], (uint)from, inst->nodeListSuper);
        arc_set_to_idx(&inst->arcListSuper[i],   (uint)to,   inst->nodeListSuper);

        double valueLow  = constantCapacity + inst->lambdaLow  * multiplierCapacity;
        double valueHigh = constantCapacity + inst->lambdaHigh * multiplierCapacity;
        if (valueLow < 0.0 || valueHigh < 0.0)
            inst->roundNegativeCapacity = 1;

        node_inc_num_adjacent(&inst->nodeListSuper[from]);
        node_inc_num_adjacent(&inst->nodeListSuper[to]);

        if (multiplierCapacity != 0.0)
            ++inst->numParametricArcs;
    }

    /* Check symmetric structure: every parametric arc must connect sourceSuper→i or i→sinkSuper,
     * and for each node i the source arc must have capacity f_i(λ) while the sink arc has -f_i(λ).
     * Two-pass to handle any arc ordering: pass 1 records source arcs, pass 2 checks sink arcs. */
    inst->isSymmetric = 1;
    {
        double * restrict sourceM = (double *)calloc(inst->numNodesSuper, sizeof(double));
        double * restrict sourceC = (double *)calloc(inst->numNodesSuper, sizeof(double));
        char   * restrict hasSrc  = (char   *)calloc(inst->numNodesSuper, sizeof(char));
        if (!sourceM || !sourceC || !hasSrc) { printf("Out of memory\n"); exit(0); }

        /* Pass 1: record source-arc (m, c) per node; flag non-source/sink parametric arcs. */
        for (int i = 0; i < (int)inst->numArcsSuper; ++i)
        {
            double m = arc_get_multiplier(&inst->arcListSuper[i]);
            if (m == 0.0) continue;
            int from = node_get_original_index(arc_get_from(&inst->arcListSuper[i], inst->nodeListSuper));
            int to   = node_get_original_index(arc_get_to(&inst->arcListSuper[i],   inst->nodeListSuper));
            if (from == (int)inst->sourceSuper && to >= 0)
            {
                sourceM[to] = m;
                sourceC[to] = arc_get_constant(&inst->arcListSuper[i]);
                hasSrc[to]  = 1;
            }
            else if (to != (int)inst->sinkSuper)
            {
                inst->isSymmetric = 0;
            }
        }

        /* Pass 2: verify each sink arc negates its node's source arc. */
        for (int i = 0; i < (int)inst->numArcsSuper && inst->isSymmetric; ++i)
        {
            double m = arc_get_multiplier(&inst->arcListSuper[i]);
            if (m == 0.0) continue;
            int from = node_get_original_index(arc_get_from(&inst->arcListSuper[i], inst->nodeListSuper));
            int to   = node_get_original_index(arc_get_to(&inst->arcListSuper[i],   inst->nodeListSuper));
            if (to == (int)inst->sinkSuper && from >= 0)
            {
                double c = arc_get_constant(&inst->arcListSuper[i]);
                if (!hasSrc[from] || m != -sourceM[from] || c != -sourceC[from])
                    inst->isSymmetric = 0;
            }
        }

        free(sourceM); free(sourceC); free(hasSrc);
    }
}

static int cmp_arc_breakpoint(const void *l, const void *r)
{
    const Arc *la = *(const Arc **)l;
    const Arc *ra = *(const Arc **)r;
    double a_bp = -arc_get_constant(la) / arc_get_multiplier(la);
    double b_bp = -arc_get_constant(ra) / arc_get_multiplier(ra);
    return (a_bp > b_bp) - (a_bp < b_bp);
}

static void sortParamArcList(HpfInstance *inst)
{
    qsort(inst->paramArcList, inst->numParametricArcs, sizeof(Arc *), cmp_arc_breakpoint);
}

#ifdef VERBOSE
static void debugPrintParamArcList(const HpfInstance *inst)
{
    printf("c Printing parametric Arcs\n");
    for (int i = 0; i < (int)inst->numParametricArcs; ++i)
        printf("c %d -b/a = %lf/%lf = %lf\n", i,
            -arc_get_constant(inst->paramArcList[i]),
             arc_get_multiplier(inst->paramArcList[i]),
            -arc_get_constant(inst->paramArcList[i]) / arc_get_multiplier(inst->paramArcList[i]));
}
#endif

static void allocateParamArcList(HpfInstance *inst)
{
    int idx = 0;
    if ((inst->paramArcList = (Arc **)malloc(inst->numParametricArcs * sizeof(Arc *))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }

    for (int i = 0; i < (int)inst->numArcsSuper; ++i)
    {
        uint from = arc_get_from(&inst->arcListSuper[i], inst->nodeListSuper)->number;
        uint to   = arc_get_to(&inst->arcListSuper[i],   inst->nodeListSuper)->number;

        if ((from == inst->sourceSuper || to == inst->sinkSuper)
                && arc_get_multiplier(&inst->arcListSuper[i]) != 0.0)
        {
#ifdef VERBOSE
            printf("c add arc %d->%d with a=%lf b=%lf to parametric arcs\n",
                from, to,
                arc_get_multiplier(&inst->arcListSuper[i]),
                arc_get_constant(&inst->arcListSuper[i]));
#endif
            inst->paramArcList[idx++] = &inst->arcListSuper[i];
        }
    }
}

static int cmp_double(const void *a, const void *b)
{
    double x = *(const double *)a;
    double y = *(const double *)b;
    if (x < y) return -1;
    if (x > y) return  1;
    return 0;
}

static void prepareOutput(const HpfInstance *inst, int *numBreakpoints,
    double **cuts, double **breakpoints, int stats[5])
{
    int i, j;

    stats[0] = (int)inst->numArcScans;
    stats[1] = (int)inst->numMergers;
    stats[2] = (int)inst->numPushes;
    stats[3] = (int)inst->numRelabels;
    stats[4] = (int)inst->numGaps;

    double *tmp;
    if ((tmp = (double *)malloc(inst->numNodesSuper * sizeof(double))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    for (i = 0; i < (int)inst->numNodesSuper; i++) tmp[i] = inst->nodeBreakpoints[i];
    qsort(tmp, inst->numNodesSuper, sizeof(double), cmp_double);

    int count = 0;
    double prev = tmp[0] - 10.0;
    for (i = 0; i < (int)inst->numNodesSuper; i++)
    {
        if (tmp[i] != prev && tmp[i] > inst->lambdaLow && tmp[i] < inst->lambdaHigh)
        { count++; prev = tmp[i]; }
    }

    double *bpPtr;
    if ((bpPtr = (double *)malloc(count * sizeof(double))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    *numBreakpoints = 0;
    prev = tmp[0] - 10.0;
    for (i = 0; i < (int)inst->numNodesSuper; i++)
    {
        if (tmp[i] != prev && tmp[i] > inst->lambdaLow && tmp[i] < inst->lambdaHigh)
        { bpPtr[(*numBreakpoints)++] = tmp[i]; prev = tmp[i]; }
    }
    free(tmp);
    *breakpoints = bpPtr;

    double *cutsPtr;
    if ((cutsPtr = (double *)malloc(inst->numNodesSuper * sizeof(double))) == NULL)
    { printf("Could not allocate memory.\n"); exit(0); }
    for (j = 0; j < (int)inst->numNodesSuper; j++) cutsPtr[j] = inst->nodeBreakpoints[j];
    *cuts = cutsPtr;
}

/*************************************************************************
Arc copy helpers for contracted problem construction
*************************************************************************/

/* Copy arc old (from oldNodeList) into newArc (nodes in newNodeList).
   Uses inst->nodeMap which must be populated before calling. */
static void copyArcNew(HpfInstance * restrict inst, const Arc * restrict old, Arc * restrict newArc,
    const Node * restrict oldNodeList, Node * restrict newNodeList, const double lambda)
{
    initializeArc(newArc);
    arc_set_constant(newArc, arc_get_constant(old));
    arc_set_multiplier(newArc, arc_get_multiplier(old));

    double cap = arc_get_multiplier(old) * lambda + arc_get_constant(old);
    if (cap < 0)
    {
        if (inst->roundNegativeCapacity) cap = 0;
        else { printf("Negative capacity for lambda=%lf.\n", lambda); exit(0); }
    }
    arc_set_capacity(newArc, cap);

    uint newFromIdx = (uint)inst->nodeMap[arc_get_from(old, oldNodeList)->number];
    uint newToIdx   = (uint)inst->nodeMap[arc_get_to(old,   oldNodeList)->number];
    arc_set_from_idx(newArc, newFromIdx, newNodeList);
    arc_set_to_idx(newArc,   newToIdx,   newNodeList);

    node_inc_num_adjacent(arc_get_from(newArc, newNodeList));
    node_inc_num_adjacent(arc_get_to(newArc,   newNodeList));
}

/* Merge arc old's symbolic capacity into already-existing arc newArc. */
static void copyArcAdd(HpfInstance * restrict inst, const Arc * restrict old, Arc * restrict newArc, const double lambda)
{
    double additional = arc_get_multiplier(old) * lambda + arc_get_constant(old);
    if (additional < 0)
    {
        if (inst->roundNegativeCapacity) additional = 0;
        else { printf("Negative capacity for lambda=%lf.\n", lambda); exit(0); }
    }
    arc_set_capacity(newArc, arc_get_capacity(newArc) + additional);
    arc_add_constant(newArc, arc_get_constant(old));
    arc_add_multiplier(newArc, arc_get_multiplier(old));
}

/*************************************************************************
CutProblem lifecycle
*************************************************************************/

static void destroyProblem(CutProblem *problem, const int destroySourceSetIndicator)
{
    if (problem->sourceSet) { free(problem->sourceSet); problem->sourceSet = NULL; }
    if (problem->sinkSet)   { free(problem->sinkSet);   problem->sinkSet   = NULL; }
    if (problem->nodeList)  { free(problem->nodeList);  problem->nodeList  = NULL; }
    if (problem->arcList)   { free(problem->arcList);   problem->arcList   = NULL; }
    if (destroySourceSetIndicator && problem->optimalSourceSetIndicator)
    {
        free(problem->optimalSourceSetIndicator);
        problem->optimalSourceSetIndicator = NULL;
    }
}

/*************************************************************************
Contracted problem construction
*************************************************************************/

static void initializeContractedProblem(HpfInstance * restrict inst, CutProblem * restrict problem,
    const Node * restrict nodeListProblem, const uint numNodesProblem,
    const Arc * restrict arcListProblem, const uint numArcsProblem,
    const double lambdaValue, const char * restrict solutionLow, const char * restrict solutionHigh,
    double intervalLow, double intervalHigh)
{
    uint i, newIndexTo, newIndexFrom;
    uint currentNode      = 2;
    uint currentSourceSet = 0;
    uint currentSinkSet   = 0;
    uint currentArc       = 0;

    problem->cutValue               = 0;
    problem->solved                 = 0;
    problem->optimalSourceSetIndicator = NULL;
    problem->lambdaValue            = lambdaValue;
    problem->numSourceSet           = 0;
    problem->numSinkSet             = 0;
    problem->numNodesInList         = 2;

    /* classify each parent node */
    for (i = 0; i < numNodesProblem; i++)
    {
        int origIdx = node_get_original_index(&nodeListProblem[i]);
        if (origIdx == -1 || origIdx == (int)inst->sourceSuper
                || (origIdx >= 0 && solutionLow[origIdx] == 1))
        {
            inst->nodeMap[i] = 0;
            problem->numSourceSet++;
        }
        else if (origIdx == -2 || origIdx == (int)inst->sinkSuper
                || (origIdx >= 0 && solutionHigh[origIdx] == 0))
        {
            inst->nodeMap[i] = 1;
            problem->numSinkSet++;
        }
        else
        {
            inst->nodeMap[i] = (int)currentNode;
            ++currentNode;
            problem->numNodesInList++;
        }
    }

    if ((problem->nodeList = (Node *)malloc(numNodesProblem * sizeof(Node))) == NULL)
    { printf("Out of memory\n"); exit(0); }
    if ((problem->sourceSet = (Node *)malloc(numNodesProblem * sizeof(Node))) == NULL)
    { printf("Out of memory\n"); exit(0); }
    if ((problem->sinkSet = (Node *)malloc(numNodesProblem * sizeof(Node))) == NULL)
    { printf("Out of memory\n"); exit(0); }

    for (i = 0; i < problem->numNodesInList; i++) initializeNode(&problem->nodeList[i], i);
    for (i = 0; i < problem->numSourceSet;   i++) initializeNode(&problem->sourceSet[i], i);
    for (i = 0; i < problem->numSinkSet;     i++) initializeNode(&problem->sinkSet[i], i);

    node_set_original_index(&problem->nodeList[0], -1); /* artificial super-source */
    node_set_original_index(&problem->nodeList[1], -2); /* artificial super-sink   */

    for (i = 0; i < numNodesProblem; i++)
    {
        if (inst->nodeMap[i] > 1)
            node_set_original_index(&problem->nodeList[inst->nodeMap[i]],
                node_get_original_index(&nodeListProblem[i]));
        else if (inst->nodeMap[i] == 0)
        {
            node_set_original_index(&problem->sourceSet[currentSourceSet],
                node_get_original_index(&nodeListProblem[i]));
            currentSourceSet++;
        }
        else
        {
            node_set_original_index(&problem->sinkSet[currentSinkSet],
                node_get_original_index(&nodeListProblem[i]));
            currentSinkSet++;
        }
    }

    for (i = 0; i < problem->numNodesInList; i++)
    {
        inst->sourceAdjacentArcIndices[i] = -1;
        inst->sinkAdjacentArcIndices[i]   = -1;
    }

    if ((problem->arcList = (Arc *)malloc(numArcsProblem * sizeof(Arc))) == NULL)
    { printf("Out of memory\n"); exit(0); }

    for (i = 0; i < numArcsProblem; i++)
    {
        newIndexFrom = (uint)inst->nodeMap[arc_get_from(&arcListProblem[i], nodeListProblem)->number];
        newIndexTo   = (uint)inst->nodeMap[arc_get_to(&arcListProblem[i],   nodeListProblem)->number];

        if (newIndexFrom == newIndexTo || newIndexTo == 0
                || newIndexFrom == 1
                || (newIndexFrom == 0 && newIndexTo == 1))
        {
            /* dropped: self-loop, back-to-source, sink-to-interior, or direct s-t */
        }
        else if (newIndexFrom == 0)
        {
            /* 0 = always-positive (merge), 1 = piecewise (separate), 2 = always-zero (skip) */
            int arc_class = 0;
            if (inst->roundNegativeCapacity)
            {
                double m = arc_get_multiplier(&arcListProblem[i]);
                double c = arc_get_constant(&arcListProblem[i]);
                if (m == 0.0)
                {
                    if (c <= 0.0) arc_class = 2;
                }
                else
                {
                    double zc = -c / m;
                    if (zc > intervalLow && zc < intervalHigh)
                        arc_class = 1;
                    else if ((m > 0.0 && zc >= intervalHigh) || (m < 0.0 && zc <= intervalLow))
                        arc_class = 2;
                }
            }
            if (arc_class == 2) { /* skip always-zero */ }
            else if (arc_class == 1)
            {
                /* piecewise: always add as separate arc, never merge */
                copyArcNew(inst, &arcListProblem[i], &problem->arcList[currentArc],
                    nodeListProblem, problem->nodeList, lambdaValue);
                ++currentArc;
            }
            else if (inst->sourceAdjacentArcIndices[newIndexTo] != -1)
            {
                copyArcAdd(inst, &arcListProblem[i],
                    &problem->arcList[inst->sourceAdjacentArcIndices[newIndexTo]], lambdaValue);
            }
            else
            {
                inst->sourceAdjacentArcIndices[newIndexTo] = (int)currentArc;
                copyArcNew(inst, &arcListProblem[i], &problem->arcList[currentArc],
                    nodeListProblem, problem->nodeList, lambdaValue);
                ++currentArc;
            }
        }
        else if (newIndexTo == 1)
        {
            int arc_class = 0;
            if (inst->roundNegativeCapacity)
            {
                double m = arc_get_multiplier(&arcListProblem[i]);
                double c = arc_get_constant(&arcListProblem[i]);
                if (m == 0.0)
                {
                    if (c <= 0.0) arc_class = 2;
                }
                else
                {
                    double zc = -c / m;
                    if (zc > intervalLow && zc < intervalHigh)
                        arc_class = 1;
                    else if ((m > 0.0 && zc >= intervalHigh) || (m < 0.0 && zc <= intervalLow))
                        arc_class = 2;
                }
            }
            if (arc_class == 2) { /* skip always-zero */ }
            else if (arc_class == 1)
            {
                /* piecewise: always add as separate arc, never merge */
                copyArcNew(inst, &arcListProblem[i], &problem->arcList[currentArc],
                    nodeListProblem, problem->nodeList, lambdaValue);
                ++currentArc;
            }
            else if (inst->sinkAdjacentArcIndices[newIndexFrom] != -1)
            {
                copyArcAdd(inst, &arcListProblem[i],
                    &problem->arcList[inst->sinkAdjacentArcIndices[newIndexFrom]], lambdaValue);
            }
            else
            {
                inst->sinkAdjacentArcIndices[newIndexFrom] = (int)currentArc;
                copyArcNew(inst, &arcListProblem[i], &problem->arcList[currentArc],
                    nodeListProblem, problem->nodeList, lambdaValue);
                ++currentArc;
            }
        }
        else
        {
            copyArcNew(inst, &arcListProblem[i], &problem->arcList[currentArc],
                nodeListProblem, problem->nodeList, lambdaValue);
            ++currentArc;
        }
    }

    problem->numArcs = currentArc;
}

static void initializeParametricCut(HpfInstance *inst,
    CutProblem *lowProblem, CutProblem *highProblem)
{
    char *all_sink, *all_source;

    if ((all_sink = (char *)malloc(inst->numNodesSuper * sizeof(char))) == NULL)
    { printf("Out of memory\n"); exit(0); }
    if ((all_source = (char *)malloc(inst->numNodesSuper * sizeof(char))) == NULL)
    { printf("Out of memory\n"); exit(0); }

    for (uint i = 0; i < inst->numNodesSuper; i++) { all_sink[i] = 0; all_source[i] = 1; }

    initializeContractedProblem(inst, lowProblem,
        inst->nodeListSuper, inst->numNodesSuper,
        inst->arcListSuper,  inst->numArcsSuper,
        inst->lambdaLow, all_sink, all_source,
        inst->lambdaLow, inst->lambdaHigh);

    if (inst->useParametricCut == 1)
        initializeContractedProblem(inst, highProblem,
            inst->nodeListSuper, inst->numNodesSuper,
            inst->arcListSuper,  inst->numArcsSuper,
            inst->lambdaHigh, all_sink, all_source,
            inst->lambdaLow, inst->lambdaHigh);

    free(all_sink);
    free(all_source);
}

static void addBreakpoint(HpfInstance * restrict inst, const double lambdaValue, const char * restrict sourceSetIndicator)
{
    for (uint i = 0; i < inst->numNodesSuper; i++)
        if (sourceSetIndicator[i] && inst->nodeBreakpoints[i] > lambdaValue)
            inst->nodeBreakpoints[i] = lambdaValue;
}

/* Like addBreakpoint but iterates only the pre-computed index list of difference
 * nodes rather than all N nodes.  Used at internal recursive call sites where the
 * "always-source" (S_low) nodes are guaranteed to be correctly handled by the
 * subsequent left-branch recursion and the top-level epilogue. */
static void addBreakpointList(HpfInstance * restrict inst, const double lambdaValue,
    const char * restrict sourceSetIndicator, const uint listCount)
{
    const uint * restrict idxList = inst->pdiffListCache;
    double * restrict bp = inst->nodeBreakpoints;
    for (uint i = 0; i < listCount; i++) {
        uint idx = idxList[i];
        if (sourceSetIndicator[idx] && bp[idx] > lambdaValue)
            bp[idx] = lambdaValue;
    }
}

/*************************************************************************
Cut evaluation
*************************************************************************/

static void evaluateCut(CutProblem *problem)
{
    uint i;
    for (i = 0; i < problem->numArcs; ++i)
    {
        int fromIdx = node_get_original_index(arc_get_from(&problem->arcList[i], problem->nodeList));
        int toIdx   = node_get_original_index(arc_get_to(&problem->arcList[i],   problem->nodeList));
        if ((fromIdx == -1 || problem->optimalSourceSetIndicator[fromIdx] == 1)
                && (toIdx == -2 || problem->optimalSourceSetIndicator[toIdx] == 0))
            problem->cutValue += arc_get_capacity(&problem->arcList[i]);
    }
}

/* Compute cut function over an explicit arc list (used for parent arcs in parametricCut). */
static void computeCutFunctionFromArcs(const char * restrict indicator,
    const Arc * restrict arcList, const uint numArcs, const Node * restrict nodeList,
    double * restrict outA, double * restrict outB)
{
    double a = 0.0, b = 0.0;
    for (uint i = 0; i < numArcs; i++)
    {
        const Arc *arc = &arcList[i];
        int fromIdx = node_get_original_index(arc_get_from(arc, nodeList));
        int toIdx   = node_get_original_index(arc_get_to(arc,   nodeList));
        int fromInSource = (fromIdx == -1 || (fromIdx >= 0 && indicator[fromIdx] == 1));
        int toInSink     = (toIdx   == -2 || (toIdx   >= 0 && indicator[toIdx]   == 0));
        if (fromInSource && toInSink) { a += arc_get_multiplier(arc); b += arc_get_constant(arc); }
    }
    *outA = a; *outB = b;
}


/*************************************************************************
solveProblem
*************************************************************************/

static void solveProblem(HpfInstance * restrict inst, CutProblem * restrict problem,
    const uint maximalSourceSet,
    const char * restrict parentSolutionLow, const char * restrict parentSolutionHigh)
{
    uint i;
    char *tempSourceSet;
    int ownArcList = 0;

    SolveContext ctx;
    memset(&ctx, 0, sizeof(ctx));
    ctx.highestStrongLabel = 1;

    ctx.nodesList = problem->nodeList;
    ctx.numNodes  = problem->numNodesInList;
    ctx.numArcs   = problem->numArcs;
    problem->cutValue = 0.0;

    /* trivial problem: every node already in source or sink set */
    if (ctx.numNodes == 2)
    {
        if ((problem->optimalSourceSetIndicator =
                (char *)malloc(inst->numNodesSuper * sizeof(char))) == NULL)
        { printf("Out of memory\n"); exit(0); }

        if (parentSolutionLow != NULL)
            memcpy(problem->optimalSourceSetIndicator, parentSolutionLow,
                   inst->numNodesSuper * sizeof(char));

        for (i = 0; i < problem->numSourceSet; i++)
            if (node_get_original_index(&problem->sourceSet[i]) >= 0)
                problem->optimalSourceSetIndicator[node_get_original_index(&problem->sourceSet[i])] = 1;

        for (i = 0; i < problem->numSinkSet; i++)
            if (node_get_original_index(&problem->sinkSet[i]) >= 0)
                problem->optimalSourceSetIndicator[node_get_original_index(&problem->sinkSet[i])] = 0;

        for (i = 0; i < problem->numArcs; i++)
        {
            if (node_get_original_index(arc_get_from(&problem->arcList[i], problem->nodeList)) == -1
                    && node_get_original_index(arc_get_to(&problem->arcList[i], problem->nodeList)) == -2)
                problem->cutValue += arc_get_capacity(&problem->arcList[i]);
        }

        problem->solved = 1;
        return;
    }

    if (maximalSourceSet == 1)
    {
        ctx.source = 1;
        ctx.sink   = 0;

        if ((ctx.arcList = (Arc *)malloc(ctx.numArcs * sizeof(Arc))) == NULL)
        { printf("Out of memory\n"); exit(0); }
        ownArcList = 1;

        for (i = 0; i < ctx.numArcs; i++)
        {
            initializeArc(&ctx.arcList[i]);
            /* reverse from/to */
            arc_set_from_idx(&ctx.arcList[i],
                arc_get_to_idx(&problem->arcList[i], problem->nodeList),
                problem->nodeList);
            arc_set_to_idx(&ctx.arcList[i],
                arc_get_from_idx(&problem->arcList[i], problem->nodeList),
                problem->nodeList);
            arc_set_capacity(&ctx.arcList[i], arc_get_capacity(&problem->arcList[i]));
        }
    }
    else
    {
        ctx.source  = 0;
        ctx.sink    = 1;
        ctx.arcList = problem->arcList;
    }

    createMemoryStructures(&ctx);
    simpleInitialization(&ctx);
    pseudoflowPhase1(&ctx);

    if ((tempSourceSet = (char *)malloc(inst->numNodesSuper * sizeof(char))) == NULL)
    { printf("Out of memory\n"); exit(0); }

    if (parentSolutionLow != NULL)
        memcpy(tempSourceSet, parentSolutionLow, inst->numNodesSuper * sizeof(char));

    if (maximalSourceSet == 1)
    {
        for (i = 2; i < ctx.numNodes; ++i)
        {
            int origIdx = node_get_original_index(&ctx.nodesList[i]);
            tempSourceSet[origIdx] = (node_get_label(&ctx.nodesList[i]) >= ctx.numNodes) ? 0 : 1;
        }
    }
    else
    {
        for (i = 2; i < ctx.numNodes; ++i)
        {
            int origIdx = node_get_original_index(&ctx.nodesList[i]);
            tempSourceSet[origIdx] = (node_get_label(&ctx.nodesList[i]) >= ctx.numNodes) ? 1 : 0;
        }
    }

    for (i = 0; i < problem->numSourceSet; i++)
        if (node_get_original_index(&problem->sourceSet[i]) >= 0)
            tempSourceSet[node_get_original_index(&problem->sourceSet[i])] = 1;

    for (i = 0; i < problem->numSinkSet; i++)
        if (node_get_original_index(&problem->sinkSet[i]) >= 0)
            tempSourceSet[node_get_original_index(&problem->sinkSet[i])] = 0;

    problem->optimalSourceSetIndicator = tempSourceSet;
    evaluateCut(problem);

    if (ownArcList) { free(ctx.arcList); ctx.arcList = NULL; }

    problem->solved = 1;
    freeMemorySolve(&ctx);

    /* flush local stats into instance */
    inst->numArcScans += ctx.numArcScans;
    inst->numPushes   += ctx.numPushes;
    inst->numMergers  += ctx.numMergers;
    inst->numRelabels += ctx.numRelabels;
    inst->numGaps     += ctx.numGaps;
}

/*************************************************************************
Source-set utilities
*************************************************************************/

static uint differenceSourceSetsCount(HpfInstance * restrict inst,
    char ** restrict ppdifference,
    const char * restrict lowOptimalSourceIndicator, const char * restrict highOptimalSourceIndicator)
{
    *ppdifference = inst->pdifferenceCache;
    char * restrict pd = inst->pdifferenceCache;
    uint count = 0;
    for (uint i = 0; i < inst->numNodesSuper; i++) {
        char d = highOptimalSourceIndicator[i] - lowOptimalSourceIndicator[i];
        pd[i] = d;
        count += (uint)d;
    }
    return count;
}

/* Second pass: collect indices of diff nodes from the already-filled pdifferenceCache.
 * Called only on the non-base path after confirming diff_count > 0.
 * pdifferenceCache is hot in L1 from the previous differenceSourceSetsCount call. */
static void buildDiffList(HpfInstance * restrict inst, const uint diff_count)
{
    const char * restrict pd = inst->pdifferenceCache;
    uint * restrict dl = inst->pdiffListCache;
    uint j = 0;
    for (uint i = 0; i < inst->numNodesSuper && j < diff_count; i++)
        if (pd[i]) dl[j++] = i;
}

double evaluateCutFunction(const HpfInstance * restrict inst,
    const char * restrict S, const double lambda)
{
    double sum = 0.0;
    for (int i = 0; i < (int)inst->numArcsSuper; ++i)
    {
        int from = node_get_original_index(arc_get_from(&inst->arcListSuper[i], inst->nodeListSuper));
        int to   = node_get_original_index(arc_get_to(&inst->arcListSuper[i],   inst->nodeListSuper));
        if (S[from] && !S[to])
        {
            double val = arc_get_constant(&inst->arcListSuper[i])
                       + arc_get_multiplier(&inst->arcListSuper[i]) * lambda;
            if (val > 0.0) sum += val;
        }
    }
    return sum;
}

static double computePiecewiseIntersect(const HpfInstance * restrict inst,
    const char * restrict lpS, const char * restrict hpS,
    const double lambda_0, const double lambda_1)
{
    double res = 1.0 / 0.0;
    double a_l = 0, b_l = 0, a_h = 0, b_h = 0;
    double arc_constant, arc_multiplier, arc_bp;
    int from, to, i;

    for (i = 0; i < (int)inst->numArcsSuper; ++i)
    {
        from           = node_get_original_index(arc_get_from(&inst->arcListSuper[i], inst->nodeListSuper));
        to             = node_get_original_index(arc_get_to(&inst->arcListSuper[i],   inst->nodeListSuper));
        arc_constant   = arc_get_constant(&inst->arcListSuper[i]);
        arc_multiplier = arc_get_multiplier(&inst->arcListSuper[i]);
        arc_bp         = -arc_constant / arc_multiplier;

        int active_now = ((arc_multiplier > 0.0 && arc_bp <= lambda_0)
                || (arc_multiplier < 0.0 && arc_bp > lambda_0)
                || arc_multiplier == 0.0);
        if (!active_now) continue;

        if (lpS[from] && !lpS[to]) { a_l += arc_multiplier; b_l += arc_constant; }
        if (hpS[from] && !hpS[to]) { a_h += arc_multiplier; b_h += arc_constant; }
    }

    for (i = 0; i < (int)inst->numParametricArcs; ++i)
    {
        arc_constant   = arc_get_constant(inst->paramArcList[i]);
        arc_multiplier = arc_get_multiplier(inst->paramArcList[i]);
        arc_bp         = -arc_constant / arc_multiplier;
        if (arc_bp > lambda_0) break;
    }

    double lambda_prev = lambda_0;
    double lambda_next;

    for (; i <= (int)inst->numParametricArcs;)
    {
        lambda_next = (i < (int)inst->numParametricArcs)
            ? -arc_get_constant(inst->paramArcList[i]) / arc_get_multiplier(inst->paramArcList[i])
            : lambda_1;
        if (lambda_next > lambda_1) lambda_next = lambda_1;

        double denom = a_l - a_h;
        if (fabs(denom) > 0.0)
        {
            double lambda_star = (b_h - b_l) / denom;
            if (lambda_star >= lambda_prev && lambda_star < lambda_next)
                return lambda_star;
        }

        if (lambda_next == lambda_1) break;
        if (i == (int)inst->numParametricArcs) break;

        while (i < (int)inst->numParametricArcs)
        {
            arc_constant   = arc_get_constant(inst->paramArcList[i]);
            arc_multiplier = arc_get_multiplier(inst->paramArcList[i]);
            arc_bp         = -arc_constant / arc_multiplier;
            if (arc_bp > lambda_next) break;

            from = node_get_original_index(arc_get_from(inst->paramArcList[i], inst->nodeListSuper));
            to   = node_get_original_index(arc_get_to(inst->paramArcList[i],   inst->nodeListSuper));

            int in_lp_cut  = lpS[from] && !lpS[to];
            int in_hp_cut  = hpS[from] && !hpS[to];
            double sign    = (arc_multiplier > 0) ? 1.0 : -1.0;

            if (in_lp_cut) { a_l += arc_multiplier * sign; b_l += arc_constant * sign; }
            if (in_hp_cut) { a_h += arc_multiplier * sign; b_h += arc_constant * sign; }
            ++i;
        }
        lambda_prev = lambda_next;
    }

    return res;
}

/* Fast intersect for symmetric instances (isSymmetric=1).
 * Operates on the passed arcList/nodeList, which shrinks at each recursive level of
 * parametricCut (contracted sub-problem), falling back to arcListSuper at depth 0.
 * Contracted super-source (originalIndex -1) and super-sink (-2) are handled as
 * always-in-S and never-in-S respectively. */
static double computeIntersectSymmetric(const HpfInstance * restrict inst,
    const char * restrict lpS, const char * restrict hpS,
    const double lambda_0, const double lambda_1,
    const Arc * restrict arcList, const uint numArcs,
    const Node * restrict nodeList)
{
    const char * restrict pd = inst->pdifferenceCache;
    double delta_a = 0.0, delta_b = 0.0;

    for (int i = 0; i < (int)numArcs; ++i)
    {
        int from = node_get_original_index(arc_get_from(&arcList[i], nodeList));
        int to   = node_get_original_index(arc_get_to(&arcList[i],   nodeList));

        /* Contracted super-source (origIdx -1) and super-sink (-2) are never diff nodes.
         * Guard pd[] access — it is only valid for non-negative originalIndex values. */
        int from_is_diff = (from >= 0) && pd[from];
        int to_is_diff   = (to   >= 0) && pd[to];
        if (!from_is_diff && !to_is_diff) continue;

        double m = arc_get_multiplier(&arcList[i]);
        double c = arc_get_constant(&arcList[i]);

        int active;
        if (m == 0.0) active = 1;
        else {
            double bp = -c / m;
            active = (m > 0.0) ? (bp <= lambda_0) : (bp > lambda_0);
        }
        if (!active) continue;

        /* Resolve lpS/hpS membership for contracted sentinels:
         * super-source (-1) is always in S; super-sink (-2) is never in S. */
        int from_lp = (from == -1) ? 1 : (from == -2) ? 0 : (lpS[from] == 1);
        int from_hp = (from == -1) ? 1 : (from == -2) ? 0 : (hpS[from] == 1);
        int to_lp   = (to   == -1) ? 1 : (to   == -2) ? 0 : (lpS[to]   == 1);
        int to_hp   = (to   == -1) ? 1 : (to   == -2) ? 0 : (hpS[to]   == 1);

        int in_lp = (from_lp && !to_lp);
        int in_hp = (from_hp && !to_hp);
        if (in_lp == in_hp) continue;

        double sign = in_lp ? 1.0 : -1.0;
        delta_a += sign * m;
        delta_b -= sign * c;
    }

    if (delta_a == 0.0) return 1.0 / 0.0;
    double lambda_star = delta_b / delta_a;
    if (lambda_star >= lambda_0 && lambda_star < lambda_1) return lambda_star;
    return 1.0 / 0.0;
}

/*************************************************************************
Recursive parametric cut
*************************************************************************/

static void parametricCut(HpfInstance * restrict inst,
    CutProblem * restrict lowProblem, CutProblem * restrict highProblem,
    const Node * restrict parentNodeList, const uint parentNumNodes,
    const Arc * restrict parentArcList, const uint parentNumArcs)
{
    char *pdifference;

    if (lowProblem->lambdaValue >= highProblem->lambdaValue)
    {
        addBreakpoint(inst, lowProblem->lambdaValue, highProblem->optimalSourceSetIndicator);
        return;
    }

    uint diff_count = differenceSourceSetsCount(inst, &pdifference,
            lowProblem->optimalSourceSetIndicator,
            highProblem->optimalSourceSetIndicator);
    if (diff_count <= 0)
    {
        addBreakpoint(inst, lowProblem->lambdaValue, highProblem->optimalSourceSetIndicator);
        return;
    }

    double lambdaIntersect;
    if (inst->roundNegativeCapacity)
    {
        lambdaIntersect = inst->isSymmetric
            ? computeIntersectSymmetric(inst,
                lowProblem->optimalSourceSetIndicator,
                highProblem->optimalSourceSetIndicator,
                lowProblem->lambdaValue, highProblem->lambdaValue,
                parentArcList, parentNumArcs, parentNodeList)
            : computePiecewiseIntersect(inst,
                lowProblem->optimalSourceSetIndicator,
                highProblem->optimalSourceSetIndicator,
                lowProblem->lambdaValue, highProblem->lambdaValue);
    }
    else
    {
        double lowA, lowB, highA, highB;
        computeCutFunctionFromArcs(lowProblem->optimalSourceSetIndicator,
            parentArcList, parentNumArcs, parentNodeList, &lowA, &lowB);
        computeCutFunctionFromArcs(highProblem->optimalSourceSetIndicator,
            parentArcList, parentNumArcs, parentNodeList, &highA, &highB);
        double denom = lowA - highA;
        lambdaIntersect = (denom != 0.0) ? (highB - lowB) / denom : 1.0 / 0.0;
    }

#ifdef VERBOSE
    printf("c intersection at %lf\n", lambdaIntersect);
#endif

    if (lambdaIntersect <= lowProblem->lambdaValue || lambdaIntersect >= highProblem->lambdaValue)
    {
        double bp = (lambdaIntersect >= highProblem->lambdaValue)
            ? highProblem->lambdaValue : lowProblem->lambdaValue;
        addBreakpoint(inst, bp, highProblem->optimalSourceSetIndicator);
        return;
    }

    CutProblem minimalIntersect;
    initializeContractedProblem(inst, &minimalIntersect,
        parentNodeList, parentNumNodes,
        parentArcList,  parentNumArcs,
        lambdaIntersect,
        lowProblem->optimalSourceSetIndicator,
        highProblem->optimalSourceSetIndicator,
        lowProblem->lambdaValue, highProblem->lambdaValue);
    solveProblem(inst, &minimalIntersect, 0,
        lowProblem->optimalSourceSetIndicator,
        highProblem->optimalSourceSetIndicator);

    buildDiffList(inst, diff_count);
    addBreakpointList(inst, lambdaIntersect, minimalIntersect.optimalSourceSetIndicator,
                      diff_count);

    parametricCut(inst, lowProblem, &minimalIntersect,
        minimalIntersect.nodeList, minimalIntersect.numNodesInList,
        minimalIntersect.arcList,  minimalIntersect.numArcs);

    parametricCut(inst, &minimalIntersect, highProblem,
        minimalIntersect.nodeList, minimalIntersect.numNodesInList,
        minimalIntersect.arcList,  minimalIntersect.numArcs);

    destroyProblem(&minimalIntersect, 1);
}

/*************************************************************************
Arc comparator for pre-sort
*************************************************************************/

static int cmpArc(const void *a, const void *b)
{
    uint mgcNum = 10;
    uint a_from = ((const Arc *)a)->from >> mgcNum;
    uint a_to   = ((const Arc *)a)->to   >> mgcNum;
    uint b_from = ((const Arc *)b)->from >> mgcNum;
    uint b_to   = ((const Arc *)b)->to   >> mgcNum;
    if (a_from > b_from) return  1;
    if (b_from > a_from) return -1;
    if (a_to   > b_to)   return  1;
    if (b_to   > a_to)   return -1;
    a_from = ((const Arc *)a)->from; a_to = ((const Arc *)a)->to;
    b_from = ((const Arc *)b)->from; b_to = ((const Arc *)b)->to;
    if (a_from > b_from) return  1;
    if (b_from > a_from) return -1;
    if (a_to   > b_to)   return  1;
    if (b_to   > a_to)   return -1;
    return 0;
}

/*************************************************************************
Public entry point — signature identical to original libhpf.h
*************************************************************************/

void hpf_solve(int numNodesIn, int numArcsIn, int sourceIn, int sinkIn,
    double *arcMatrix, double lambdaRange[2], int roundNegativeCapacityIn,
    int *numBreakpoints, double **cuts, double **breakpoints,
    int stats[5], double times[3])
{
    HpfInstance inst;
    hpf_instance_init(&inst);

    double readStart, readEnd, initStart, initEnd, solveStart, solveEnd;

    readStart = clock();
    inst.numNodesSuper = (uint)numNodesIn;
    inst.numArcsSuper  = (uint)numArcsIn;
    inst.sourceSuper   = (uint)sourceIn;
    inst.sinkSuper     = (uint)sinkIn;
    inst.lambdaLow     = lambdaRange[0];
    inst.lambdaHigh    = lambdaRange[1];
    inst.roundNegativeCapacity = 0;
    if (inst.lambdaLow == inst.lambdaHigh) inst.useParametricCut = 0;

    readGraphSuper(&inst, arcMatrix);
    readEnd = clock();

    initStart = clock();
    qsort(inst.arcListSuper, inst.numArcsSuper, sizeof(Arc), cmpArc);
    if (inst.roundNegativeCapacity)
    {
#ifdef VERBOSE
        printf("c will round negative capacities to zero\n");
#endif
        allocateParamArcList(&inst);
        sortParamArcList(&inst);
#ifdef VERBOSE
        debugPrintParamArcList(&inst);
#endif
    }

    CutProblem lowProblem, highProblem;
    initializeParametricCut(&inst, &lowProblem, &highProblem);
    initEnd = clock();

    solveStart = clock();
    if (inst.useParametricCut == 1)
    {
        solveProblem(&inst, &lowProblem,  0, NULL, NULL);
        destroyProblem(&lowProblem,  0);
        solveProblem(&inst, &highProblem, 0, NULL, NULL);
        destroyProblem(&highProblem, 0);

        parametricCut(&inst, &lowProblem, &highProblem,
            inst.nodeListSuper, inst.numNodesSuper,
            inst.arcListSuper,  inst.numArcsSuper);
        addBreakpoint(&inst, lowProblem.lambdaValue,  lowProblem.optimalSourceSetIndicator);
        addBreakpoint(&inst, highProblem.lambdaValue, highProblem.optimalSourceSetIndicator);

        destroyProblem(&lowProblem,  1);
        destroyProblem(&highProblem, 1);
    }
    else
    {
#ifdef VERBOSE
        printf("Solving problem with lambda value %.15lf\n", lowProblem.lambdaValue);
#endif
        solveProblem(&inst, &lowProblem, 0, NULL, NULL);
        addBreakpoint(&inst, lowProblem.lambdaValue, lowProblem.optimalSourceSetIndicator);
        destroyProblem(&lowProblem, 1);
    }
    solveEnd = clock();

    times[0] = (readEnd   - readStart)  / CLOCKS_PER_SEC;
    times[1] = (initEnd   - initStart)  / CLOCKS_PER_SEC;
    times[2] = (solveEnd  - solveStart) / CLOCKS_PER_SEC;

    prepareOutput(&inst, numBreakpoints, cuts, breakpoints, stats);

#ifdef VERBOSE
    printf("Stats: [%d, %d, %d, %d, %d]\n",
        stats[0], stats[1], stats[2], stats[3], stats[4]);
    printf("times: [%lf, %lf, %lf]\n", times[0], times[1], times[2]);
    printf("Num breakpoints: %d\n", *numBreakpoints);
#endif

    hpf_instance_destroy(&inst);
}
