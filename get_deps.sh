#!/bin/bash
if [[ $(uname) == "Linux" ]]; then
    if [  -n "$(uname -a | grep Ubuntu)" ]; then
        sudo apt update
        sudo apt install -y git autoconf libgmp3-dev curl cmake gcc-multilib xutils-dev flex bison default-jre
    elif [  -n "$(uname -a | grep arch)" ]; then
        sudo pacman -S --noconfirm git autoconf gmp curl cmake flex bison
    fi
else
    echo "Currently, only Linux is supported."
    exit 1
fi

mkdir -p deps
pushd deps/

# AVR
git clone https://github.com/aman-goel/avr.git
pushd avr/
git checkout hwmcc20
popd

# Boolector
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

# btor2tools
git clone https://github.com/Boolector/btor2tools.git
pushd btor2tools
./configure.sh --static
pushd build
make
cp bin/catbtor ../../
popd
popd

# Pono
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
cp pono ../../
popd
popd

# nuXmv
wget https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.0.0-linux64.tar.gz
tar -xvf download.php?file=nuXmv-2.0.0-linux64.tar.gz
cp nuXmv-2.0.0-Linux/bin/nuXmv .

popd