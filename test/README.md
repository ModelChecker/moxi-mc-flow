# Testing

To run tests, use the `test.py` script. The script takes a `.json` file as a
config that tells it what commands to run and what the expected output should
be. For example:

    python3 test.py mc-moxi-pono.json
    python3 test.py sortcheck.json
    python3 test.py smv2btor.json

The JSON configuration files require a single JSON object that has a python
"script" to define what to use for each test, an optional array of options to
run with each test, and an array that defines the tests to run. Each test is a
JSON object with an optional extra set of options to pass to the script, defined
as an array "options", then an input file, a path to a desired output location,
and some expected output. The expected outputs can be one of three forms:

1. "expected_returncode": an integer value that is compared the returncode of
   the script executed on the input.
2. "expected_stdout": a path to a file that is diffed with the stdout of the
   script executed on the input.
3. "expected_output": an array of pairs of files, where the first file has the
   expected contents and the second is the path to the actua output. This is
   usually the same as the path given in the "output" attribute.

Altogether, a file is of the form:

    {
        "script": "path/to/script",
        "options": ["list", "of", "options"],
        "tests": [
            "options": ["test-specific", "options"],
            "input": "path/to/input/relative/to/test.py",
            "output": "path/to/deisired/output/relative/to/test.py",
            "expected_returncode": 0,
            "expected_stdout": "diffed with stdout",
            "expected_output": [
                ["path/to/expected/output",
                 "path/to/actual/output (likely to same as output above)"]
            ]
        ]
    }

The script will print each instruction run and if that test passes or not. If
the test fails, the result of the diff is printed to stdout.