CAV'24 Submission #3209 Symbolic Model-Checking Intermediate-Language Tool Suite

Chris Johannsen, Karthik Nukala, Rohit Dureja, Ahmed Irfan, Natarajan Shankar,
Cesare Tinelli, Moshe Y. Vardi and Kristin Yvonne Rozier

-------------------------------------------------------------------------------
Abstract

MoXI (Model eXchange Interlingua) is an intermediate language for SMT-based
model checking. moxi-mc-flow is a toolchain that translates SMV -> MoXI ->
BTOR2, and any resulting witnesses back to the source language. By default, the
toolchain provides scripts for automatically translating files to BTOR2, then
model checking them with either AVR, Pono, or BtorMC, and then translating the
resulting witnesses back to the source language. The toolchain also provides a
reference sort checker for MoXI files, as well as a JSON schema that can be used
to validate MoXI files in a JSON format. 

-------------------------------------------------------------------------------
Getting Started

1. Install Docker (or a compatible alternative) on your machine. Docker is free
and open-source and can be downloaded from [https://www.docker.com]

2. Import the included tarball From a terminal shell in the same directory as
the downloaded artifact, the `moxi.tar` file can be imported with the command:
    `docker load < moxi.tar`

3. Start the container The tarball loads an "image" from which "containers" can
be run. View the loaded images with `docker images` then start a new container
(or instance of the image) with:
    `docker run -it --rm moxi-mc-flow:artifact`
the flags `-it` give you an interactive terminal with the container while `--rm`
removes the container (but not the image) when you exit. If you'd rather keep a
persistent container to save changes, remove this flag.

4. You will now have a bash shell at the home directory of the artifact.

Note: If you removed the `--rm` flag, after exiting the shell the container will
still be running in the background until you issue a `docker stop` command for
the container

-------------------------------------------------------------------------------
Smoke Test

The script `/home/scripts/run_modelcheck.sh` executes
`/home/moxi-mc-flow/modelcheck.py` on a subset of SMV benchmarks and MoXI files
and checks that the result is as expected. This script exercises all three
provided scripts, translating SMV -> MoXI -> BTOR2 and back, and uses all
available model checkers. To run this, execute:

    ./scripts/run_modelcheck.sh

Every test should output [PASS], meaning that the sat/unsat result is as
expected and, in some cases, the generated witness is as expected. The expected
results/files can be found in the `moxi-mc-flow/test/` directory, in the `.json`
test config files and `.expect` files.

-------------------------------------------------------------------------------
Requirements

The following dependencies have been installed on the docker container for use
by the artifact:
    - AVR (https://github.com/aman-goel/avr, `hwmcc2020` branch, 
                                                            commit: c13e626)
    - Pono (https://github.com/stanford-centaur/pono, `hwmcc2020` branch, 
                                                            commit: 6fdc160)
    - Boolector (https://github.com/Boolector/boolector, commit: 6603ed7b)
    - btor2tools (https://github.com/Boolector/btor2tools, commit: 8775f9a)
    - nuXmv (https://nuxmv.fbk.eu/download.html, 64-bit x86 Linux version 2.0)
All are technically optional, but at least one of AVR, Pono, and Boolector must
be installed in order to perform model checking, btor2tools must be installed to
validate BTOR2 programs, and nuXmv is required for benchmarking.

The following python package(s) have been installed via `pip` for the JSON
schema validator:
    - jsonschema

All replication steps (except for experimental evaluation) should take less than
ten minutes to complete. The full experimental evaluation runs a set of 960
model-checking benchmarks with seven different backend combinations and a
timeout of one hour for each benchmark. This script took ~3 days to complete on
a 50 core server. We provide a version of this script with a 5 second timeout
that took ~5 hours to complete on a machine with an 8 core Intel(R) Core(TM)
i7-6700K CPU @ 4.00GHz and 32 GB memory. 

-------------------------------------------------------------------------------
Organization

|- Home directory
|   |
|   |- avr/               AVR (model checker)
|   |
|   |- LICENSE/           License information
|   |
|   |- moxi-mc-flow/      Source for the translation scripts
|   |   |
|   |   |- benchmarks/    Files for experimental data
|   |   |
|   |   |- src/           Translators source code
|   |   |
|   |   |- test/          Test and example files for each script
|   |   |
|   |   |- modelcheck.py  Model checking script
|   |   |
|   |   |- sortcheck.py   MoXI reference sort checking script
|   |   |
|   |   |- translate.py   Translation script
|   |
|   |- scripts/           Useful scripts for running tests
|   |   |
|   |   |- run_benchmarks_full.sh   Full benchmarking script (1 hour timeout)
|   |   |
|   |   |- run_benchmarks_short.sh  Short benchmarking script (5 sec timeout)
|   |   |
|   |   |- run_jsonschema.sh        JSON schema testing script
|   |   |
|   |   |- run_modelcheck.sh        modelcheck.py test script (**smoke test**)
|   |   |
|   |   |- run_sortcheck.sh         sortcheck.py test script
|   |   |
|   |   |- run_translate.sh         translate.py test script
|   |
|   |- btormc             BtorMC binary (model checker)
|   |
|   |- catbtor            catbtor binary for validating BTOR2 programs
|   |
|   |- nuXmv              nuXmv version 2.0 binary (model checker)
|   |
|   |- pono               Pono binary (model checker)
|   |
|   |- README.txt         Artifact replication and evaluation instructions

-------------------------------------------------------------------------------
Replication Instructions (Functional badge)

--------------------------------------
Supported Language Features

The script `run_translate.sh` executes a test suite to verify claims regarding
supported features in SMV/MoXI. It executes `translate.py` on a set of files and
diffs that output against an expected output, then executes `modelcheck.py` on a
set of files and diffs the resulting witness against an expected output
(`.expect` files in `test/`). 

The following is a list of SMV language features claimed in the paper and the
test files (relative to `moxi-mc-flow/`) that exercise said feature:

- VAR:       test/smv/QF_BV/ken-imp.c.smv
- IVAR:      test/smv/QF_BV/ken-imp.c.smv
- FROZENVAR: test/smv/var.smv
- DEFINE:    test/smv/QF_BV/ken-imp.c.smv
- ASSIGN:    test/smv/assign.smv
- INIT:      test/smv/QF_BV/ken-imp.c.smv
- TRANS:     test/smv/QF_BV/ken-imp.c.smv
- INVAR:     test/smv/assign.smv
- INVARSPEC: test/smv/QF_BV/ken-imp.c.smv
- LTLSPEC:   test/smv/LTLSPEC/counter.smv
- FAIRNESS/JUSTICE: test/smv/LTLSPEC/short.smv (see line 15 of short.moxi.expect)

The Delay.smv example (Fig. 4) from the paper is also tested against each stage
of the translation.

For a MoXI example with a wide collection of supported features, see
`test/moxi/QF_BV/ThreeBitCounter.moxi`. See
`test/moxi/QF_BV/DoubleDelayTwoCheck.moxi` for how multiple check system
commands and `test/moxi/QF_BV/DoubleDelayTwoQuery.moxi` for how multiple queries
are handled.

--------------------------------------
Reference Sort Checker

`run_sortcheck.sh` sort checks all the files in `moxi-mc-flow/examples/moxi/`,
which include directories for the following logics sortcheck.py supports: QF_BV,
QF_ABV, QF_LIA, QF_LRA, QF_NIA, QF_NRA.

--------------------------------------
JSON Schema

The script `run_validate.sh` executes the script `json-schema/schema_test.py` to
exercise the defined JSON schema.

--------------------------------------
Experimental Evaluation

The scripts `run_benchmarks_full.sh`/`run_benchmarks_short.sh` execute the
script `benchmarks/benchmark.py` for each of the following solver/algorithm
combinations:

    - avr kind
    - avr bmc
    - pono bmc
    - pono kind
    - btormc bmc
    - nuXmv bmc
    - nuXmv kind

`run_benchmarks_full.sh` runs the script with the 8 hour timeout reported in the
paper and `run_benchmarks_short.sh` runs the script with a much shorter 5 second
timeout. For the avr/pono/btormc runs, the scripts use the `modelcheck.py`
script to run the solver/algorithm over each smv file in benchmarks. They report
the file, result, and time for each run. After running each benchmark, it then
runs `check.py` to verify no solvers disagreed on a result, i.e., one claimed
sat/unsat and another claimed the opposite for a benchmark. 

Keep in mind that the results are meant to be relative to nuXmv, i.e., they show
that the toolchain provided is correct and performant *with respect to* nuXmv.
So, though many tests with not finish within the timeout or memout limits, the
data show that the avr, btormc, and pono scripts agree with and solve a similar
number of sat/unsat instances compared to nuXmv.

By default, the script uses 4 processes. If you omit the flag, the script will
use as many processes as there are cores available. You can change this by
editing the --nprocs option in `scripts/run_benchmarks_short.sh`, for example:

    python3 benchmark.py btormc bmc --results results_full/btormc-bmc.csv --nprocs 2

The script uses the nuXmv binary at `/home/nuXmv` to test the nuXmv versions
with the commands listed in `benchmarks/nuxmv-kind.cmd` and
`benchmarks/nuxmv-bmc.cmd` respectively. 

-------------------------------------------------------------------------------
Running the Toolchain (Reusable badge)

To run the `translate.py` script, simply feed in a file with a `.smv`, `.moxi`,
or `.json` file extension and select language to translate to (moxi, moxi-json,
or btor2). You can ask catbtor or sortcheck.py to validate the output with the
`--validate` flag. You may need to point the script to the location of `catbtor`
with the `catbtor` flag. Some example invocations (from `/home/moxi-mc-flow`):

    python3 translate.py test/smv/Delay.smv moxi --output Delay.moxi --validate

    python3 translate.py test/smv/Delay.smv btor2 --output Delay.btor2 --validate --catbtor ../catbtor

    python3 translate.py test/moxi/QF_BV/ThreeBitCounter.moxi btor2 --output ThreeBitCounter.btor2 --validate --catbtor ../catbtor

You can also cast Int types to bit vectors of specified widths if using a logic
with Int sorts, for example:

    python3 translate.py test/moxi/QF_LIA/TrafficLightEnum2.moxi btor2 --output TrafficLightEnum2.btor2 --validate --catbtor ../catbtor --intwidth 64 

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

All three of `translate.py`, `modelcheck.py` and `sortcheck.py` provide
descriptive help messages via the `-h`/`--help` flag.

-------------------------------------------------------------------------------
Notes

- We do not support the CONSTANT and COMPASSION SMV features. This claim will be
removed from the final version.

- No model checker (avr, pono, btormc) supports the justice keyword in BTOR2,
but we do support the translation. So, a file with a `:fairness` formula will
run properly with `translate.py`, but not with `modelcheck.py`.

- Only btormc is supported for full SMV/MoXI witness translation -- the other
model checkers do not support outputting full traces (i.e., traces that output
every variable at every time step) which is necessary for our translation.
`btorsim` could be used to generate a full trace from a compact trace, but does
not output correct BTOR2 witnesses (the headers are incorrect).

- AVR does not always output witnesses correctly for arrays -- we skip the file
`test/smv/QF_ABV/FIFOs` for AVR for this reason.

- :queries are unsupported in translating to BTOR2 -- we're unaware of a way to
require a BTOR2 program to output the same model for multiple traces across
runs.

- The timeout time for benchmarking is only for the model checker call. For
example, with a timeout of 10, a call to modelcheck.py could take 12 seconds if
the translation took 3 seconds and the model checking call took 9 seconds.

- Memouts are reported based on the underlying process being killed due to the
call to `ulimit -v 8000000` in each benchmarking script.

- We do not benchmark btormc using kind since there is a bug in its
implementation (https://github.com/Boolector/boolector/issues/220)

--------------------------------------------------------------------------------
Support

If you believe you have found a case of unsound output from any script, please
run the script with the debug level 1 (`--debug 1`) and provide the output to
the authors for analysis. For example:

    python3 translate.py test/smv/Delay.smv moxi --output Delay.moxi --validate --debug 1 

The debug output contains no identifying information, please ask the chairs to
assist in passing along you anonymized feedback. Thank you.