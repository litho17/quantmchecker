#!/bin/sh

lib="./lib/test"
echo "Verifying textcrunchr_1...\n\n"
./scripts/run.sh $lib src/test/java/textcrunchr_1/com
echo "Verifying braidit_1...\n\n"
./scripts/run.sh $lib src/test/java/braidit_1/com
echo "Verifying withmi_1...\n\n"
./scripts/run.sh $lib src/test/java/withmi_1/com
echo "Verifying calculator_1...\n\n"
./scripts/run.sh $lib src/test/java/calculator_1/com
echo "Verifying battleboats_1...\n\n"
./scripts/run.sh $lib src/test/java/battleboats_1/com
echo "Verifying image_processor_1...\n\n"
./scripts/run.sh $lib src/test/java/image_processor/com
echo "Verifying smartmail_1...\n\n"
./scripts/run.sh $lib src/test/java/smartmail
echo "Verifying powerbroker_1...\n\n"
./scripts/run.sh $lib src/test/java/powerbroker_1/edu
echo "Verifying snapbuddy_1...\n\n"
./scripts/run.sh $lib src/test/java/SnapBuddy_1/com

