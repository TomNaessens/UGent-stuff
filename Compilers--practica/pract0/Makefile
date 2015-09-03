CC=gcc
CCFLAGS=-g

OBJS = main.o hash_table.o

main: $(OBJS)
	$(CC) -o $@ $(CCFLAGS) $(OBJS)

# Phony target: doesn't actually produce a file
.PHONY: clean
clean:
	rm -f main *.o

# Wildcard rule
%.o: %.c
	$(CC) $(CCFLAGS) -o $@ -c $<
