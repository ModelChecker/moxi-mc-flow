#!/bin/bash
source "$(dirname $0)/setup-utils.sh"
PANDA_DIR="$SRC_DIR/PANDA"

pushd "$PANDA_DIR/rgl2"
touch makefile.deps
make
popd

pushd "$PANDA_DIR/PANDAcore"
make
popd

