# Testing

To run tests, use the `test.py` script. It requires a directory of `.smv` as input, then takes flags denoting which tests to run: 

1. `nuxmv2mcil`: Runs `translate.py` on each file with target language MCIL.
2. `nuxmv2btor`:  Runs `translate.py` on each file with target language BTOR2.
3. `modelcheck`: Runs `modelcheck.py` on each file.