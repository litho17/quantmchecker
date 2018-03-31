#!/bin/sh

grep -RnIi "@ListInv" $1
grep -RnIi "@Summary" $1
grep -RnIi "@SideEffect" $1
