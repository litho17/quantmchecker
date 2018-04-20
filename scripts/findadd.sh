#!/bin/sh

grep -ERnIi -- '\.add\(|\.put\(|\.append\(|\.offer\(|\.push\(' $1
