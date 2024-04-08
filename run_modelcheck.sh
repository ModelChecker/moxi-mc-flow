#!/usr/bin/env bash

pushd /home/moxi-mc-flow/test/

echo "-----------------------------------------------------"
echo "Testing btormc"
echo "-----------------------------------------------------"
python3 test.py mc-moxi-btormc.json
python3 test.py mc-smv-btormc.json

echo "-----------------------------------------------------"
echo "Testing avr"
echo "-----------------------------------------------------"
python3 test.py mc-moxi-avr.json
python3 test.py mc-smv-avr.json

echo "-----------------------------------------------------"
echo "Testing pono"
echo "-----------------------------------------------------"
python3 test.py mc-moxi-pono.json
python3 test.py mc-smv-pono.json

echo "-----------------------------------------------------"
echo "Testing witness translation"
echo "-----------------------------------------------------"
python3 test.py mc-moxi-witness.json
python3 test.py mc-smv-witness.json

popd