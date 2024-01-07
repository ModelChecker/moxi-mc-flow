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

# Pono (CAV artifact)
# wget https://figshare.com/ndownloader/files/28213749
# tar -xvf 28213749
# mv pono-paper-artifact pono
# pushd pono
# docker build --no-cache -t pono-artifact ./docker
# popd

