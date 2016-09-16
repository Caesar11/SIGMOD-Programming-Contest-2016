all: main 

main: main.cpp
	g++ main.cpp -o main -std=c++11 -Ofast -ltbb -ljemalloc -msse4.2

clean:
	rm -rf main