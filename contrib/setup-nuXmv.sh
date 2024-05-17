#!/bin/bash
source "$(dirname $0)/setup-utils.sh"

pushd $DEPS_DIR
wget https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.0.0-linux64.tar.gz
tar -xvf download.php?file=nuXmv-2.0.0-linux64.tar.gz
cp nuXmv-2.0.0-Linux/bin/nuXmv .
popd