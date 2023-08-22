import json, os
from jsonschema import validate, exceptions, RefResolver

# TODO: turn this into a main.py file, stringing together entire translation

# testing utils

CRED    = '\33[31m'
CGREEN  = '\33[32m'
CEND    = '\033[0m'


def should_pass(instance, schema, name=None, resolver=None):
    try:
        validate(instance=instance, schema=schema, resolver=resolver)
    except exceptions.ValidationError as ve:
        print(CRED, "FAILED: expected a pass, but failed -- ERROR MESSAGE \n", ve, CEND)
        return

    if name == None:
        print(CGREEN, "PASSED", CEND)
    else:
        print(name, "-", CGREEN, "PASSED", CGREEN, CEND)
    return

path_to_schema = "/Users/local/IL-JSON/schema" # replace this!

resolver = RefResolver("file://%s/" % path_to_schema, {})

il_file = open("/Users/local/IL-JSON/schema/il.json")
il_schema = json.load(il_file)

counter_smv = json.load(open("counter.json"))

should_pass(instance=counter_smv, schema=il_schema, name="counter_smv", resolver=resolver)