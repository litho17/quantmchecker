#!/bin/sh

grep -ERnIi -- 'Map<|Set<|Queue<|Stack<|Vector<|Buffer<|Deque<|List<' $1 | grep = | grep new
grep -RnIi "StringBuilder" $1 | grep = | grep new
