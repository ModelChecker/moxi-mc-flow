# moxi-mc-flow

Translators from SMV to MoXI to BTOR2 and their witnesses. 

![Toolchain](toolchain.png "Toolchain")

## Requirements

The following programs/packages are required to run the toolchain and install all the dependencies:

- Python 3.11 (or later)
- jsonschema (Python pip package)
- make
- curl
- cmake
- Flex (for Pono)
- Bison (for Pono)
- GMP (for Pono)
- JRE (for Pono)

The build method has been tested on Ubuntu 20.04 LTS. The dependencies (except Python 3.11 and jsonschema) can be
installed on Ubuntu via:

    sudo apt-get install build-essential curl cmake flex bison libgmp3-dev default-jre

## Building

To build the artifact, run `./contrib/setup-all.sh` to install all depencencies, then install
[Docker](https://docs.docker.com/engine/install/) and run

    docker build . -t moxi-mc-flow:artifact

to build the Docker image and save it with name `moxi-mc-flow:artifact`. 

## Running the translators

To run the `translate.py` script, feed in a file with a `.smv`, `.moxi`, or
`.json` file extension and select language to translate to (moxi, moxi-json, or
btor2). You can ask catbtor or sortcheck.py to validate the output with the
`--validate` flag. Some example invocations (from `/home/moxi-mc-flow`):

    python3 translate.py test/smv/Delay.smv moxi --output Delay.moxi --validate

    python3 translate.py test/smv/Delay.smv btor2 --output Delay.btor2 --validate

    python3 translate.py test/moxi/QF_BV/ThreeBitCounter.moxi btor2 --output ThreeBitCounter.btor2 --validate

You can also cast Int types to bit vectors of specified widths if using a logic
with Int sorts, for example:

    python3 translate.py test/moxi/QF_LIA/TrafficLightEnum2.moxi btor2 --output TrafficLightEnum2.btor2 --validate --intwidth 64 

Refer to the usage information for more options:

    python3 translate.py --help

## Running a model checker

To run the `modelcheck.py` script, feed it a `.smv`, `.moxi`, or `.json` file
and a backend solver to use for model checking. The supported backends are AVR,
Pono, and BtorMC. See the notes about witness generation.

    python3 modelcheck.py test/smv/Delay.smv btormc --output Delay.smv.witness

    python3 modelcheck.py test/moxi/Delay.moxi btormc --output Delay.moxi.witness

The script runs the BMC algorithm of the selected model checker by default, the
`--kind` flag will set the checker to use it's k-induction algorithm (see notes
about btormc with kind):

    python3 modelcheck.py test/smv/QF_BV/lup.1.prop1-func-interl.btor.smv pono --kind --output lup.1.prop1-func-interl.btor.smv.witness

You can ask the script to copy back all intermediate translation files with the
`--copyback` option:

    python3 modelcheck.py test/smv/Delay.smv btormc --output Delay.smv.out --copyback

Refer to the usage information for more options:

    python3 modelcheck.py --help
