OPT = -O4 -g 
CFLAGS = -c -fpic -Wall -std=gnu99 $(OPT)
LDFLAGS = --static

SOURCES = libhpf.c
TARGET = ../libhpf.so
HEADERS = $(SOURCES:.c=.h)
OBJECTS = $(SOURCES:.c=.o)

.PHONY : all clean
all: $(TARGET)

clean:
	rm -f $(OBJECTS) $(TARGET)

$(TARGET): $(OBJECTS)
	$(CC) $(LDFLAGS) -o $(TARGET) $(OBJECTS)

%.o: %.c
	$(CC) $(CFLAGS) $< -o $@
