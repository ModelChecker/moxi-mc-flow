#!/bin/bash
set -euo pipefail
source "$(dirname $0)/setup-utils.sh"
PANDA_DIR="$SRC_DIR/PANDA"

pushd "$PANDA_DIR/rgl2"
mkdir -p objs
make librgl.a
popd

pushd "$PANDA_DIR/PANDAcore"
make
popd
