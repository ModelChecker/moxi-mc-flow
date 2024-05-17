#!/bin/bash
source "$(dirname $0)/setup-utils.sh"

pushd $DEPS_DIR
git clone https://github.com/Boolector/btor2tools.git
pushd btor2tools
./configure.sh --static
pushd build
make

if [[ $? -ne 0 ]]; then 
    echo "Failed building btor2tools"
    exit 1
fi

cp bin/catbtor ../../
popd
popd
popd