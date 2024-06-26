#!/usr/bin/env bash

pushd $(dirname "$0")/../benchmarks/

# Any process over 8GB virtual memory will be killed ("memout")
ulimit -v 8000000

mkdir results_short

python3 benchmark.py btormc bmc --results results_short/btormc-bmc.csv --timeout 5 --nprocs 4
python3 benchmark.py avr bmc --results results_short/avr-bmc.csv --timeout 5 --nprocs 4
python3 benchmark.py avr kind --results results_short/avr-kind.csv --timeout 5 --nprocs 4
python3 benchmark.py pono bmc --results results_short/pono-bmc.csv --timeout 5 --nprocs 4
python3 benchmark.py pono kind --results results_short/pono-kind.csv --timeout 5 --nprocs 4
python3 benchmark.py nuxmv bmc --results results_short/nuxmv-bmc.csv --timeout 5 --nprocs 4
python3 benchmark.py nuxmv kind --results results_short/nuxmv-kind.csv --timeout 5 --nprocs 4

python3 check.py logs/ results_short/

popd