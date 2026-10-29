.PHONY: all clean

all:
	$(MAKE) -C src/pseudoflow/c

clean:
	$(MAKE) -C src/pseudoflow/c clean
