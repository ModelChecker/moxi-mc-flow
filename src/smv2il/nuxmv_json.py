import json, os, argparse
from jsonschema import validate, exceptions, RefResolver

import nuxmv_pyparser as nuXmvsource_2_nuxmvAST
import translate as nuXmvAST_2_ILAST
import to_json as ILAST_2_ILJSON

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

path_to_schema = "/Users/local/ILToBtor2Python/json-schema/schema" # replace this!

resolver = RefResolver("file://%s/" % path_to_schema, {})

il_file = open("/Users/local/ILToBtor2Python/json-schema/schema/il.json") # replace this!
il_schema = json.load(il_file)

def translate(nuxmv: str, json_filename: str):
    nuxmv_file = open(nuxmv)

    nuxmv_ast = nuXmvsource_2_nuxmvAST.parse(nuxmv_file)
    il_ast = nuXmvAST_2_ILAST.translate_parse_tree(nuxmv_ast, print_ast=True)

    ILAST_2_ILJSON.ast_to_json_to_file(il_ast, json_filename, print_json=True)
    
    il_json_object = json.load(open(json_filename))
    should_pass(instance=il_json_object, schema=il_schema, name=json_filename, resolver=resolver)


if __name__ == '__main__':
    argparser = argparse.ArgumentParser(
                           prog='nuXmv/NuSMV to JSON translator',
                           description='Main file translating an input nuXmv/NuSMV file (.smv) into a JSON object corresponding to its IL representation'
   )

    argparser.add_argument('nuxmv')
    argparser.add_argument('json')

    args = argparser.parse_args()

    translate(args.nuxmv, args.json)