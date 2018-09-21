#!/bin/sh

echo "Benchmark: textcrunchr_1"
#./scripts/textcrunchr_1.sh

echo "Benchmark: braidit_1"
#./scripts/braidit_1.sh

./scripts/setup.sh

echo "Benchmark: jrecruiter"
cd ~/Google\ Drive/tianhans-papers-repo/repo/jrecruiter
mvn -e compile

echo "Benchmark: spring-petclinic"
cd ~/Google\ Drive/tianhans-papers-repo/repo/spring-petclinic
mvn -e compile

echo "Benchmark: jforum3"
cd ~/Google\ Drive/tianhans-papers-repo/repo/jforum3
mvn -e compile