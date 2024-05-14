#!/usr/bin/env bash

pushd $(dirname "$0")/../test/

echo "-----------------------------------------------------"
echo "Testing smv2moxi"
echo "-----------------------------------------------------"
python3 test.py smv2moxi.json

echo "-----------------------------------------------------"
echo "Testing moxi2btor"
echo "-----------------------------------------------------"
python3 test.py moxi2btor.json

echo "-----------------------------------------------------"
echo "Testing smv2btor"
echo "-----------------------------------------------------"
python3 test.py smv2btor.json

popd