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

# Pono (CAV artifact)
# wget https://figshare.com/ndownloader/files/28213749
# tar -xvf 28213749
# mv pono-paper-artifact pono
# pushd pono
# docker build --no-cache -t pono-artifact ./docker
# popd

# make sure to run on Ubuntu
# sudo apt-get install libgmp-dev default-jre
# git clone https://github.com/stanford-centaur/pono.git
# cd pono
# git checkout hwmcc2020
# ./contrib/setup-bison.sh 
# ./contrib/setup-smt-switch.sh # install gmp and JRE
# ./contrib/setup-btor2tools.sh
# sed -i '199,203 s/^/#/' CMakeLists.txt
# ./configure.sh
# cd build
# make