# IlToBtor2Python

Repository for python translators from nuXmv to MCIL to BTOR2 and their witnesses. 

## Translation
To translate, use the `translate.py` script. For example:

```bash
python3 translate.py examples/mcil/QF_BV/ThreeBitCounter.mcil btor2 --output ThreeBitCounter.btor2
```
```bash
python3 translate.py examples/smv/nuxmv/invgen/QF_BV/apache-escape-absolute.c.smv mcil --output apache-escape-absolute.c.mcil
```

Refer to the usage for more information:
```bash
usage: translate.py [-h] [--output OUTPUT] [--validate] [--pickle] [--catbtor CATBTOR]
                    [--sortcheck SORTCHECK] [--intwidth INTWIDTH]
                    input {mcil,mcil-json,btor2}

positional arguments:
  input                 input program to translate, language is inferred from file extension
  {mcil,mcil-json,btor2}
                        target language

options:
  -h, --help            show this help message and exit
  --output OUTPUT       target location; should be a directory if targetlang is 'btor2', a
                        filename otherwise
  --validate            validate output; uses catbtor if targetlan is btor2, sortcheck.py if
                        targetlang is mcil or mcil-json
  --pickle              if targetlang is `btor2`, dump pickled BTOR2; needed for witness
                        translations
  --catbtor CATBTOR     path to catbtor for BTOR2 validation
  --sortcheck SORTCHECK
                        path to sortcheck.py for MCIL validation
  --intwidth INTWIDTH   bit width to translate Int types to when translating to BTOR2
```

## Model Checking
To run model checking on a file, run the `get_deps.sh` script to fetch the HWMCC20 versions of `avr` and the latest version of `boolector` (for `btormc`). Then use the `modelcheck.py` script. For example, to model check an MCIL file using `btormc`:
```bash
python modelcheck.py examples/mcil/QF_BV/ThreeBitCounter.mcil btormc --output ThreeBitCounter.witness
```

To model check the same file using `avr` with k-induction:
```bash
python modelcheck.py examples/mcil/QF_BV/ThreeBitCounter.mcil avr --output ThreeBitCounter.witness --kind
```

To copy back all translated (intermediate) files:
```bash
python modelcheck.py examples/mcil/QF_BV/ThreeBitCounter.mcil btormc --output ThreeBitCounter --copyback
```

To model check an SMV file:
```bash
python modelcheck.py examples/smv/nuxmv/beem/QF_BV/adding.1.prop1-back-serstep.btor.smv btormc --output adding.1.prop1-
back-serstep.btor.smv.witness
```

Refer to the usage for more information:
```bash
usage: modelcheck.py [-h] [--output OUTPUT] [--avr-path AVR_PATH]
                     [--btormc-path BTORMC_PATH] [--translate-path TRANSLATE_PATH]
                     [--copyback] [--intwidth INTWIDTH] [--catbtor CATBTOR]
                     [--sortcheck SORTCHECK] [--kmax KMAX] [--timeout TIMEOUT] [--kind]
                     [--cpp] [--debug] [--quiet]
                     input {btormc,avr}

positional arguments:
  input                 input program to model check via translation to btor2
  {btormc,avr, pono}    model checker to use

options:
  -h, --help            show this help message and exit
  --output OUTPUT       location of output check-system response
  --avr-path AVR_PATH   path to avr directory
  --btormc-path BTORMC_PATH
                        path to btormc binary
  --pono-path PONO_PATH
                        path to btormc binary
  --translate-path TRANSLATE_PATH
                        path to translate.py script
  --copyback            copy all intermediate translations and results to output location
  --intwidth INTWIDTH   bit width to translate Int types to (default=32)
  --catbtor CATBTOR     path to catbtor for BTOR2 validation
  --sortcheck SORTCHECK
                        path to sortcheck.py for MCIL validation
  --kmax KMAX           max bound for BMC (default=1000)
  --timeout TIMEOUT     timeout in seconds (default=3600)
  --kind                enable k-induction
  --cpp                 runs cpp on input if SMV
  --debug               output debug messages
  --quiet               silence output
```