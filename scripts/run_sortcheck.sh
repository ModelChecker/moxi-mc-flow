#!/usr/bin/env bash

pushd $(dirname "$0")/../test/

echo "-----------------------------------------------------"
echo "Testing MoXI sort checker"
echo "-----------------------------------------------------"
python3 test.py sortcheck.json

popd