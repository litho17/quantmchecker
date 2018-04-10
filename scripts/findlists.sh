#!/bin/sh

grep -ERnIi -- 'Map<|Set<|Queue<|Stack<|Vector<|Builder|Buffer<|Deque<|List<' $1 | grep =
