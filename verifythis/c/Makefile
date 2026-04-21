CC = cc
CFLAGS = -Wall -Wextra -O2

all: test_ada

test_ada: test_ada.c ada.c bonus.c
	$(CC) $(CFLAGS) -o $@ $^

test: test_ada
	./test_ada

clean:
	rm -f test_ada
