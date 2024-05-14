#!/usr/bin/env bash

pushd $(dirname "$0")/../json-schema/

echo "-----------------------------------------------------"
echo "Testing JSON schema"
echo "-----------------------------------------------------"
python3 test.py

echo "-----------------------------------------------------"
echo "Testing JSON validation script"
echo "-----------------------------------------------------"
python3 validate.py ../test/json/ModCounter.json
python3 validate.py ../test/json/StateProgression.json

popd