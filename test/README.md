# Testing

To run tests, use the `test.py` script. The scripts requires a set of files that should pass, a set of files that should fail, and a test to run. 

The sets of files can either be a directory or a file that lists absolute paths of files. For example, to generate your own such a list of files, use 
```bash
find ../examples/mcil -type f > pass/sortcheck.txt
```
The directories `pass` and `fail` include such files, relative to `test/`.

The usage below lists the supported tests:
```bash
usage: test.py [-h] [--translate TRANSLATE] [--modelcheck MODELCHECK]
               [--sortcheck SORTCHECK] [--catbtor CATBTOR]
               [--resultsdir RESULTSDIR] [--timeout TIMEOUT]
               passfiles failfiles
               {nuxmv2btor,nuxmv2mcil,mcil2btor,sortcheck,modelcheck}

positional arguments:
  passfiles             directory of or file that lists input files that
                        should pass
  failfiles             directory of or file that lists input files that
                        should fail
  {nuxmv2btor,nuxmv2mcil,mcil2btor,sortcheck,modelcheck}
                        test to run

options:
  -h, --help            show this help message and exit
  --translate TRANSLATE
                        path to translate.py
  --modelcheck MODELCHECK
                        path to modelcheck.py
  --sortcheck SORTCHECK
                        path to sortcheck.py
  --catbtor CATBTOR     path to catbtor
  --resultsdir RESULTSDIR
                        directory to output test logs and copyback data
  --timeout TIMEOUT     max seconds before timeout
```

Example invocations:

```bash
python test.py pass/mcil2btor.txt fail/mcil2btor.txt mcil2btor --resultsdir results-mcil2btor
```

```bash
touch empty
python test.py ../examples/mcil empty sortcheck --resultsdir results-sortcheck
```