#!/bin/bash

CONTRIB_DIR="$(dirname $0)"

$CONTRIB_DIR/setup-avr.sh
if [[ $? -ne 0 ]]; then 
    exit 1
fi

$CONTRIB_DIR/setup-boolector.sh
if [[ $? -ne 0 ]]; then 
    exit 1
fi

$CONTRIB_DIR/setup-btor2tools.sh
if [[ $? -ne 0 ]]; then 
    exit 1
fi

$CONTRIB_DIR/setup-nuXmv.sh
if [[ $? -ne 0 ]]; then 
    exit 1
fi

$CONTRIB_DIR/setup-pono.sh
if [[ $? -ne 0 ]]; then 
    exit 1
fi

