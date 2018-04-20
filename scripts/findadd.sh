#!/bin/sh

grep -ERnIi -- '.add\(|.put\(|.append\(|.offer\(' $1
