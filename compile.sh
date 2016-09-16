#!/bin/bash

# DIR=$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )
# echo ${DIR}
# pip install --user ${DIR}/src/packages/*
cd src
g++ main.cpp -o main  -std=c++11 -O3 -ljemalloc -ltbb -msse4.2

