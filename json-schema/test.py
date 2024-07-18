import json
import os

import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning)

from jsonschema import validate, exceptions, RefResolver

CRED    = '\33[31m'
CGREEN  = '\33[32m'
CEND    = '\033[0m'

# resolving directories and file/schema refs
dirname = os.path.dirname(__file__)
schemas_dirname = dirname + "/schema/"
resolver = RefResolver("file://%s/" % schemas_dirname, {})

enum_sort_file = open("schema/declare-enum-sort.json")
enum_sort_schema = json.load(enum_sort_file)

declare_sort_file = open("schema/declare-sort.json")
declare_sort_schema = json.load(declare_sort_file)

define_sort_file = open("schema/define-sort.json")
define_sort_schema = json.load(define_sort_file)

declare_const_file = open("schema/declare-const.json")
declare_const_schema = json.load(declare_const_file)

expr_file = open("schema/term.json")
expr_schema = json.load(expr_file)

declare_fun_file = open("schema/declare-fun.json")
declare_fun_schema = json.load(declare_fun_file)

define_fun_file = open("schema/define-fun.json")
define_fun_schema = json.load(define_fun_file)

set_logic_file = open("schema/set-logic.json")
set_logic_schema = json.load(set_logic_file)

define_system_file = open("schema/define-system.json")
define_system_schema = json.load(define_system_file)

check_system_file = open("schema/check-system.json")
check_system_schema = json.load(check_system_file)

moxi_file = open("schema/moxi.json")
moxi_schema = json.load(moxi_file)

# ====================================================================

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

def should_fail(instance, schema, name=None, resolver=None):
    try:
        validate(instance=instance, schema=schema, resolver=resolver)
    except exceptions.ValidationError:
        if name == None:
            print(CGREEN, "PASSED", CEND)
        else:
            print(name, "-", CGREEN, "PASSED", CEND)
        return
    
    print(CRED, "FAILED: expected a fail, but passed", CEND)

def test_all(tsnp_tuples, resolver=None, heading=None):
    if heading != None:
        print("--* Testing", heading, "*--")
    for (test, schema, name, p) in tsnp_tuples:
        if p:
            should_pass(test, schema, name, resolver)
        else:
            should_fail(test, schema, name, resolver)

# ====================================================================

# declare-sort tests
ds_test1 = {"command": "declare-sort", "symbol": "A", "arity": 0}
ds_test2 = {"command": "declare-sort", "symbol": "Set", "arity": 1}
ds_test3 = {"command": "declare-sort", "symbol": "Array", "arity": 2}
ds_fail1 = {"command": "declare-sort", "symbol": 3, "arity": 3}
ds_fail2 = {"command": "declare-sort", "symbol": "A", "arity": -1}

declare_sort_tests = [
    (ds_test1, declare_sort_schema, "ds_test1", True),
    (ds_test2, declare_sort_schema, "ds_test2", True),
    (ds_test3, declare_sort_schema, "ds_test3", True),
    (ds_fail1, declare_sort_schema, "ds_fail1", False),
    (ds_fail2, declare_sort_schema, "ds_fail2", False)
]

test_all(declare_sort_tests, heading="declare-sort", resolver=resolver)

# enum-sort tests
es_test1 = {"command": "declare-enum-sort", "symbol": "enum1", "values": ["foo", "bar"]} # should pass
es_test2 = {"command": "declare-enum-sort", "symbol": "enum1", "values": ["foo", 7]} # should fail - 7 not string
es_test3 = {"command": "declare-enum-sort", "symbol": "enum1", "age": ["foo", "bar"]} # should fail - age not valid

declare_enum_sort_tests = [
    (es_test1, enum_sort_schema, "es_test1", True),
    (es_test2, enum_sort_schema, "es_test2", False),
    (es_test3, enum_sort_schema, "es_test3", False)
]

test_all(declare_enum_sort_tests, heading="declare-enum-sort")

# define-sort tests
dfs_test1 = {
    "command": "define-sort", 
    "symbol": "NestedSet", 
    "parameters": [ "X" ], 
    "definition": 
    {
        "identifier": "Set", 
        "parameters": [ 
            {
                "identifier": "Set", 
                "parameters": [ {"identifier": "X"} ]
            } 
        ]
    } 
}

dfs_test2 = {
    "command": "define-sort", 
    "symbol": "Array2", 
    "parameters": [ "X", "Y" ], 
    "definition":
    {
        "identifier": "Array", 
        "parameters": [
            {"identifier": "X"},
            {
                "identifier": "Array", 
                "parameters": [
                    {"identifier": "X"},
                    {"identifier": "Y"}
                ]
            }
        ]
    } 
}

define_sort_tests = [
    (dfs_test1, define_sort_schema, "dfs_test1", True),
    (dfs_test2, define_sort_schema, "dfs_test2", True)
]

test_all(define_sort_tests, heading="define-sort", resolver=resolver)

# declare-const tests
dcs_test1 = {"command": "declare-const", "symbol": "A", "sort": {"identifier": "A"} }
dcs_test2 = {"command": "declare-const", "symbol": "n", "sort": {"identifier": "Int"} }
dcs_test3 = {"command": "declare-const", "symbol": "bv8", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}} }

declare_const_tests = [
    (dcs_test1, declare_const_schema, "dcs_test1", True),
    (dcs_test2, declare_const_schema, "dcs_test2", True),
    (dcs_test3, declare_const_schema, "dcs_test3", True)
]

test_all(declare_const_tests, heading="declare-const", resolver=resolver)


expr_test1 = { "identifier": "n" }
expr_test2 = { "identifier": "*", "args": [ {"identifier": "n"}, {"identifier": "n"}] }
expr_test3 = { "identifier": "!", "args": [ {"identifier": "n"} ] }
expr_test4 = { 
    "identifier": "*", 
    "args": [ 
        {"identifier": "-", "args": [ {"identifier": "n"} ]}, 
        {"identifier": "n"} 
    ] 
}
expr_test4 = { 
    "identifier": {"symbol": "extract", "indices": [1, 2]}, 
    "args": [{"identifier": "n"}]
}
expr_test5 = {
    "identifier": {
        "symbol": "let",
        "binders": [{"symbol": "x", "term": {"identifier": "+", "args": [{"identifier": 5}, {"identifier": 3}]}}]
    },
    "args": [
        {
            "identifier": "-",
            "args": [{"identifier": "x"}, {"identifier": 1}]
        }
    ]
}
expr_test6 = {
    "identifier": {
        "qualifier": "as", 
        "symbol": "const", 
        "sort": {
            "identifier": "Array", 
            "parameters": [
                {"identifier": {"symbol": "BitVec", "indices": [8]}}, 
                {"identifier": {"symbol": "BitVec", "indices": [4]}}
            ]
        }
    },
    "args": [{"identifier": "#b000"}]
}


expr_tests = [
    (expr_test1, expr_schema, "expr_test1", True),
    (expr_test2, expr_schema, "expr_test2", True),
    (expr_test3, expr_schema, "expr_test3", True),
    (expr_test4, expr_schema, "expr_test4", True),
    (expr_test5, expr_schema, "expr_test5", True),
    (expr_test6, expr_schema, "expr_test6", True)
]

test_all(expr_tests, heading="expr", resolver=resolver)


# define-fun tests
declare_fun_test1 = { 
    "command": "declare-fun", 
    "symbol": "sq", 
    "inputs": [ {"identifier": "Int"} ], 
    "output": {"identifier": "Int"}
}

declare_fun_test2 = {
    "command": "declare-fun", 
    "symbol": "isSqRoot",
    "inputs": [ 
        { "identifier": "Int" }, 
        { "identifier": "Int" } 
    ],
    "output": {"identifier": "Bool"}
}

declare_fun_test3 = {
    "command": "declare-fun",
    "symbol": "f",
    "inputs": [
        { "identifier": "Bool" },
        { "identifier": "Bool" }
    ],
    "output": { "identifier": "Bool" }
}

declare_fun_tests = [
    (declare_fun_test1, declare_fun_schema, "define_fun_test1", True),
    (declare_fun_test2, declare_fun_schema, "define_fun_test2", True),
    (declare_fun_test3, declare_fun_schema, "define_fun_test3", True),
]

test_all(declare_fun_tests, resolver=resolver, heading="define-fun")


# define-fun tests
# (define-fun sq ((n Int)) Int (* n n))
define_fun_test1 = { 
    "command": "define-fun", 
    "symbol": "sq", 
    "inputs": [ { "symbol": "n", "sort": {"identifier": "Int"} }], 
    "output": {"identifier": "Int"}, 
    "body": {
        "identifier" : "*",
        "args": [
            { "identifier": "n" },
            { "identifier": "n" }
        ]
    }
}
# (define-fun isSqRoot ((m Int) (n Int)) Bool (= n (sq m)))
define_fun_test2 = {
    "command": "define-fun", 
    "symbol": "isSqRoot",
    "inputs": [ 
        { "symbol": "m", "sort": {"identifier": "Int"} }, 
        { "symbol": "n", "sort": {"identifier": "Int"} } 
    ],
    "output": {"identifier": "Bool"},
    "body": { 
        "identifier" : "=",
        "args": [
            { "identifier": "n" },
            { "identifier": "sq", "args": [ {"identifier": "m"}] }
        ]
    }
}
# (define-fun max ((m Int) (n Int)) Int (ite (> m n) m n))
define_fun_test3 = {
    "command": "define-fun", 
    "symbol": "max",
    "inputs": [ {"symbol": "m", "sort": {"identifier": "Int"}}, {"symbol": "n", "sort": {"identifier": "Int"}} ],
    "output": {"identifier": "Int"},
    "body": {
        "identifier": "ite",
        "args": [
            { "identifier": ">", "args": [
                {"identifier": "m"},
                {"identifier": "n"}
            ]},
            {"identifier": "m"},
            {"identifier": "n"}
        ]
    }
}
define_fun_tests = [
    (define_fun_test1, define_fun_schema, "define_fun_test1", True),
    (define_fun_test2, define_fun_schema, "define_fun_test2", True),
    (define_fun_test3, define_fun_schema, "define_fun_test3", True)
]

test_all(define_fun_tests, resolver=resolver, heading="define-fun")

# set-logic tests
set_logic_test1 = {"command": "set-logic", "logic": "QF_BV" }
set_logic_tests = [
    (set_logic_test1, set_logic_schema, "set_logic_test1", True)
]

test_all(set_logic_tests, heading="set-logic")

def_system_test1 = {
    "command": "define-system",
    "symbol": "system1",
    "input": [],
    "output": [],
    "local": [
        { 
            "symbol": "request",
            "sort": {"identifier": "Request"}
        },
        {
            "symbol": "state",
            "sort": {"identifier": "State"}
        }
    ],
    "init": { 
       "identifier": "=", "args": [
                        { "identifier": "state" },
                        { "identifier": "ready" }
                    ]
    },
    "trans": { "identifier": "ite", 
                "args": [ 
                    { "identifier": "and", "args": [ 
                        { 
                            "identifier": "=", "args": [ 
                                {"identifier": "state"}, 
                                {"identifier": "ready"} 
                            ]
                        },
                        {
                            "identifier": "=", "args": [
                                {"identifier": "request"},
                                {"identifier": "Tr"}
                            ]
                        }
                    ]
                    }, 
                    { "identifier": "=", "args": [
                        {"identifier": "state'"},
                        {"identifier": "busy"}
                    ]}, 
                    { "identifier": "or", "args": [
                        { "identifier": "=", "args": [
                        {"identifier": "state'"},
                        {"identifier": "ready"}
                    ]},
                    { "identifier": "=", "args": [
                        {"identifier": "state'"},
                        {"identifier": "busy"}
                    ]}
                    ]}]
            },
    "inv": { "identifier": "true"},
    "subsys": [ 
        {
             "symbol":  "A",
             "target" : { 
                "symbol" : "system2",
                "arguments": [
                    "request",
                    "state"
                ]
            } 
        }
       
    ]
}

def_system_test2 = {
    "command": "define-system",
    "symbol": "Cnt",
    "input": [
        {
            "symbol": "in", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}}
        }
    ],
    "output": [
        {
            "symbol": "out", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}}
        }
    ],
    "init": {
        "identifier": "=", 
        "args": [
            {"identifier": "out"}, 
            {"identifier": "#b00000001"}]
    },
    "trans": {
        "identifier": "=", 
        "args": [
            {"identifier": "out'"}, 
            {"identifier": "bvadd", "args": [
                {"identifier": "out"}, 
                {"identifier": "bvsmod", "args": [
                    {"identifier": "in"},
                    {"identifier": "#b00000011"}
                ]}
            ]}
        ]
    }
}

define_system_tests = [
    (def_system_test1, define_system_schema, "def_system_test1", True),
    (def_system_test2, define_system_schema, "def_system_test2", True)
]

test_all(define_system_tests, resolver=resolver, heading="define-system")


check_system_test1 = {
    "command": "check-system",
    "symbol": "main",
    "assumption": [
        {
            "symbol": "a",
            "formula": {
                "identifier": "and",
                "args": [
                    {"identifier": "p"},
                    {"identifier": "q"}
                ]
            }
        }
    ],
    "reachable": [
        {
            "symbol": "rch1",
            "formula": {
                "identifier": "=",
                "args": [
                    {"identifier": "a"},
                    {"identifier": "1"}
                ]
            }
        },
        {
            "symbol": "rch2",
            "formula": {
                "identifier": "=",
                "args": [
                    {"identifier": "c"},
                    {"identifier": "d"}
                ]
            }
        }
    ],
    "query": [
        {
            "symbol": "query1",
            "formulas": ["rch1", "rch1"]
        }
    ],
    "queries": [
        [
            {"symbol": "query2", "formulas": ["a", "rch1"]},
            {"symbol": "query3", "formulas": ["a", "rch2"]}
        ],
        [
            {"symbol": "query4", "formulas": ["a", "rch1", "rch2"]}
        ]
    ]
}

check_system_tests = [
    (check_system_test1, check_system_schema, "check_system_test1", True)
]


declare_enum_sort_request = {
    "command": "declare-enum-sort",
    "symbol": "Request",
    "values": [ "Tr", "Fa" ]
}

declare_enum_sort_state = {
    "command": "declare-enum-sort",
    "symbol": "State",
    "values": [ "Ready", "Busy" ]
}

short_moxi = [
    declare_enum_sort_request,
    declare_enum_sort_state,
    def_system_test1,
    check_system_test1
]

std_moxi = [
    {
        "command": "define-system",
        "symbol": "Cnt",
        "input": [
            {
                "symbol": "in", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}}
            }
        ],
        "output": [
            {
                "symbol": "out", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}}
            }
        ],
        "init": {
            "identifier": "=", 
            "args": [
                {"identifier": "out"}, 
                {"identifier": "#b00000001"}]
        },
        "trans": {
            "identifier": "=", 
            "args": [
                {"identifier": "out'"}, 
                {"identifier": "bvadd", "args": [
                    {"identifier": "out"}, 
                    {"identifier": "bvsmod", "args": [
                        {"identifier": "in"},
                        {"identifier": "#b00000011"}
                    ]}
                ]}
            ]
        }
    },
    {
        "command": "check-system",
        "symbol": "Cnt",
        "input": [
            {
                "symbol": "i", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}}
            }
        ],
        "output": [
            {
                "symbol": "o", "sort": {"identifier": {"symbol": "BitVec", "indices": [8]}}
            }
        ],
        "assumption": [
            {
                "identifier": "a",
                "formula": {
                    "identifier": "=",
                    "args": [
                        {"identifier": "i"},
                        {"identifier": "#b00000010"}
                    ]
                }
            }
        ],
        "reachable": [
            {
                "symbol": "rch",
                "formula": {
                    "identifier": "=",
                    "args": [
                        {"identifier": "o"},
                        {"identifier": "#b00001010"}
                    ]
                }
            }
        ],
        "query": [
            {
                "symbol": "q",
                "formulas": ["rch"]
            }
        ]
    }
]


moxi_tests = [
    (short_moxi, moxi_schema, "short_moxi", True),
    (std_moxi, moxi_schema, "short_moxi", True)
]

test_all(moxi_tests, resolver=resolver, heading="il")
