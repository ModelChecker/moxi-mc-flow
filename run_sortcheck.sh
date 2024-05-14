#!/usr/bin/env bash

pushd /home/moxi-mc-flow/test/

echo "-----------------------------------------------------"
echo "Testing MoXI sort checker"
echo "-----------------------------------------------------"
python3 test.py sortcheck.json

popd