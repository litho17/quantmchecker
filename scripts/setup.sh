#!/bin/sh

checkerdir="$HOME/Documents/workspace/quantmchecker"
LIB="$checkerdir/lib"
class_files_location="$checkerdir/target/scala-2.12/classes"

echo "Setting up java native library path..."
# export PATH=$checker_framework_bin:$PATH
export LD_LIBRARY_PATH=$LIB:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$LIB:$DYLD_LIBRARY_PATH

pwd=`pwd`
cd "$class_files_location"
echo "Jarring the latest class files to ~/Desktop..."
jar -cvf qc.jar plv &> /dev/null
mv qc.jar $HOME/Desktop/
cd "$pwd"