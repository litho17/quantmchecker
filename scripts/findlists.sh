#!/bin/sh

grep -ERnIi -- 'Map<|Set<|Queue<|Stack<|Vector<|Buffer<|Deque<|List<' $1 | grep =
grep -RnIi "Builder" $1 | grep "= new"
