#!/bin/sh

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
