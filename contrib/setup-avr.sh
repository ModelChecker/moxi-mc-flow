#!/bin/bash
source "$(dirname $0)/setup-utils.sh"

pushd $DEPS_DIR
git clone https://github.com/aman-goel/avr.git
pushd avr/
git checkout hwmcc20

if [[ $? -ne 0 ]]; then 
    echo "Failed installing AVR"
    exit 1
fi

popd
popd