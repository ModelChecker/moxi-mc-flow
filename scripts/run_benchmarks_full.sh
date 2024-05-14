#!/usr/bin/env bash

pushd /home/moxi-mc-flow/benchmarks/

# Any process over 8GB virtual memory will be killed ("memout")
ulimit -v 8000000

mkdir results_full

python3 benchmark.py btormc bmc --results results_full/btormc-bmc.csv
python3 benchmark.py avr bmc --results results_full/avr-bmc.csv
python3 benchmark.py avr kind --results results_full/avr-kind.csv
python3 benchmark.py pono bmc --results results_full/pono-bmc.csv
python3 benchmark.py pono kind --results results_full/pono-kind.csv
python3 benchmark.py nuxmv bmc --results results_full/nuxmv-bmc.csv 
python3 benchmark.py nuxmv kind --results results_full/nuxmv-kind.csv

python3 check.py logs/ results_full/

popd