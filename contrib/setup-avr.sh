#!/bin/bash
source "$(dirname $0)/setup-utils.sh"

pushd $DEPS_DIR
git clone https://github.com/aman-goel/avr.git
pushd avr/
git checkout hwmcc20
popd
popd