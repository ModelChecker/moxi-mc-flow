#!/bin/bash
source "$(dirname $0)/setup-utils.sh"

pushd $DEPS_DIR
git clone https://github.com/stanford-centaur/pono.git
mv pono pono-dir
pushd pono-dir
git checkout hwmcc2020
./contrib/setup-bison.sh 
./contrib/setup-smt-switch.sh # install gmp and JRE
./contrib/setup-btor2tools.sh
sed -i '199,203 s/^/#/' CMakeLists.txt
./configure.sh --static
pushd build
make

if [[ $? -ne 0 ]]; then 
    echo "Failed building pono"
    echo "Are GMP and JRE installed?"
    exit 1
fi

cp pono ../../
popd
popd
popd