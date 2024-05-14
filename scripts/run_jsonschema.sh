#!/usr/bin/env bash

pushd /home/json-schema/

echo "-----------------------------------------------------"
echo "Testing JSON schema"
echo "-----------------------------------------------------"
python3 test.py

echo "-----------------------------------------------------"
echo "Testing JSON validation script"
echo "-----------------------------------------------------"
python3 validate.py ../moxi-mc-flow/test/json/ModCounter.json
python3 validate.py ../moxi-mc-flow/test/json/StateProgression.json

popd