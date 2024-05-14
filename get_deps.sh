#!/bin/bash

# AVR
git clone git@github.com:aman-goel/avr.git
pushd avr/
git checkout hwmcc20
popd

# Boolector
git clone git@github.com:Boolector/boolector.git
pushd boolector
./contrib/setup-lingeling.sh
./contrib/setup-btor2tools.sh
./configure.sh 
pushd build 
make
popd
popd

# btor2tools
git clone git@github.com:Boolector/btor2tools.git
pushd btor2tools
./configure.sh
pushd build
make
popd
popd

# make sure to run on Ubuntu
git clone https://github.com/stanford-centaur/pono.git
cd pono
git checkout hwmcc2020
./contrib/setup-bison.sh 
./contrib/setup-smt-switch.sh # install gmp and JRE
./contrib/setup-btor2tools.sh
sed -i '199,203 s/^/#/' CMakeLists.txt
./configure.sh
cd build
make

# PANDA deps
sudo apt-get install gcc-multilib xutils-dev

# nuXmv
wget https://nuxmv.fbk.eu/theme/download.php?file=nuXmv-2.0.0-linux64.tar.gz
tar -xvf download.php?file=nuXmv-2.0.0-linux64.tar.gz