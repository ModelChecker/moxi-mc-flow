# IlToBtor2Python

Repository for python translators from nuXmv to MCIL to BTOR2. To translate, use the `translate.py` script. For example:

    python3 translate.py examples/smv/nuxmv/invgen/QF_BV/apache-escape-absolute.c.smv btor2 --output out

To run model checking on any example, run the `get_deps.sh` script to fetch the HWMCC20 versions of `avr` and `pono`, as well as the latest version of `boolector` (for `btormc`). Then run the `modelcheck.py` script. For example:

    python3 modelcheck.py --btormc --avr --pono examples/smv/nuxmv/invgen/QF_BV/apache-escape-absolute.c.smv --copyback --output out