#!/bin/sh

grep -RnIi "@Inv" $1
grep -RnIi "@Summary" $1
grep -RnIi "@SideEffect" $1
