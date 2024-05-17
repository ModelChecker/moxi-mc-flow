#!/bin/bash
source "$(dirname $0)/setup-utils.sh"

pushd $DEPS_DIR
git clone https://github.com/Boolector/boolector.git
pushd boolector
./contrib/setup-lingeling.sh
./contrib/setup-btor2tools.sh
./configure.sh 
pushd build 
make
cp bin/btormc ../../
popd
popd
popd