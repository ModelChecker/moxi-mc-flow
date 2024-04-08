# `smv2moxi`

## Introduction
Our development of MoXI intends to enable 
 - translations _from_ richer high-level languages (HL).
 - translations _to_ bare-bones low-level languages (LL).

As a first step towards demonstrating MoXI's viability in this regard, we chose SMV (in particular, [nuXmv 2.0.0](https://nuxmv.fbk.eu/downloads/nuxmv-user-manual.pdf)) as our HL. 

We eventually aim to support other HL languages such as SAL (`.sal`) and sally (`.mcmt`) and we encourage developers of other HLs to contribute their own translators to MoXI.

This document provides a high-level overview of the constructs we support and how someone writing SMV interested in using `smv2moxi` can expect these constructs to appear in MoXI.

## Translation

This section mimics the structure of the nuXmv manual, with the intention of being useful to developers using SMV. As such, we assume familiarity with symbolic model checking and the SMV language in general.

[NOTE!] `smv2moxi` assumes that input SMV specifications are well-typed according to nuXmv's typechecker and only performs the translation on well-typed/well-formed SMV specifications. We offer no guarantees on any other specifications.

We target the SMT theories `QF_ABV` and `QF_LIA` in this translation. We leave others as future work.

### Types
#### Booleans
SMV boolean values `TRUE`/`FALSE` are translated into corresponding MoXI `Bool`s (inherited from SMT-LIB).
#### Enumeration Types
SMV enumerations, declared via 

`color : {RED, GREEN, BLUE}` 

are declared in MoXI as

`(declare-enum-sort [fresh-enum-type] (RED GREEN BLUE))`

where `color` then becomes a module variable of type `fresh-enum-type`. SMV conflates these notions, thereby removing the need for `fresh-enum-type`.  
#### Word
SMV constructs 

`word[X]`/`unsigned word[X]`/`signed word[X]` 

are translated into MoXI's `(_ BitVec X)`, which is inherited from SMT-LIB.

We remove all `signed`/`unsigned` distinctions because we know that the input specification is type-correct
according to the SMV semantics, so there's no need to preserve/enforce these.
#### Integer
We translate SMV `integer`s into MoXI's `Int` type (again inherited from SMT-LIB).
#### Real
We don't support SMV `real`s in this release of `smv2moxi`.
#### Clock
We don't support SMV's TTS (Timed Transition System) fragment.
#### Array/IntArray
Given an SMV type `elemtype` that translates into `ET` in MoXI, SMV's 

`array x..y of elemtype` and `array integer of elemtype`

translates to MoXI's 

`(Array Int ET)` 

inheriting again from SMT-LIB (in particular, the [theory of arrays](https://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml).)
#### WordArray
Given an SMV type `elemtype` that translates into `ET` in MoXI, SMV's

`array word[X] of elemtype`

translates to MoXI's

`(Array (_ BitVec X) ET)`

which again inherits from SMT-LIB.

#### Set Types
We don't support SMV set types in this release of `smv2moxi` - this is future work.

### Expressions
SMV expression translation is generally straightforward, in that all expressions that work on supported types are supported. 

Notable exclusions are type-casting/conversion operations and set operations, alongside base functions such as `sin`/`cos` (since they aren't represented in any existing SMT theory). All of these constitute future work.

### Definition of the FSM
#### Variable Declarations
Base types (`boolean`/`word`/`integer`/`array`) all appear in `(define-system ...)` declarations.

Enumeration types are dealt with by introducing `(define-enum-sort ...)` and creating an instance of the defined type.

Module declarations `foo : bar(...)` are dealt with separately.

In this section, we only consider base + enumeration types.

* State Variables: These are declared in SMV as
`VAR name : type`, which `smv2moxi` uses to populate the `:output` field of the `(define-system ...)` command.
* Input Variables: These are declared in SMV as `IVAR name : type`, which `smv2moxi` uses to populate the `:input` field of the `(define-system ...)` command.
* Frozen Variables: These are declared in SMV as `FROZENVAR name : type`, which also populate the `:output` field of the `(define-system ...)` command, with an additional obligation in the transition formula `:trans`, stating that `(= name' name)` (the frozen property, ensuring the declared variable maintains its value over the transitions of the system).

#### DEFINE Declarations
`DEFINE` declarations correspond to let-bindings in MoXI.

That is, 

```
MODULE main
DEFINE 
    CONJ := a & b;
VAR
    a : boolean;
    b : boolean;
INIT
    CONJ = false;
```

translates to

```
(set-logic QF_ABV)
(define-system main 
   :input () 
   :output ((a Bool) (b Bool)) 
   :local () 
   :init (= (let ((CONJ (and a b))) CONJ) 
            false) 
   :trans true 
   :inv true )
```

[NOTE!] The usage of `DEFINE` in SMV is far less constrained.
For example, `DEFINE` declarations can contain forward references to yet-to-be-defined modules and can name `DEFINE` declarations occurring in yet-to-be-defined modules. We restrict ourselves to the most simplistic usecase (context-sensible macros/let-bindings) for the time being. We anticipate supporting the general case in future releases of `smv2moxi`.

### Array DEFINE Declarations
We don't support this since it's an experimental feature in nuXmv (as of 2.0.0).

### Function (FUN) Declarations
SMV's `FUN` declarations correspond to uninterpreted function declarations, which we invoke in MoXI using `(declare-fun ...)`.

Given the following SMV fragment,
```
FUN
    into : boolean -> word[1];
    out : word[1] -> boolean;
```

We can translate this into

```
(declare-fun into (Bool) (_ BitVec 1))
(declare-fun out (Bool) (_ BitVec 1))
```

### INIT Constraints
We translate SMV `INIT` declarations directly as `:init` options in the MoXI `(define-system ...)`.

### INVAR Constraints
We translate SMV `INVAR` declarations directly as `:inv` options in the MoXI `(define-system ...)`.

### TRANS Constraints
We translate SMV `TRANS` declarations directly as `:trans` options in the MoXI `(define-system ...)`.

### ASSIGN Constraints
`ASSIGN` declarations in SMV can have one of the following forms:
1) `foo := bar`: in this case, we introduce constraint `(= foo bar)` as an `:inv` option in the `(define-system ...)`.
2) `init(foo) := bar`: in this case, we introduce constraint `(= foo bar)` as an `:init` option in the `(define-system ...)`
3) `next(foo) := bar`: in this case, we introduce constraint `(= foo' bar)` as a `:trans` option in the `(define-system ...)`

### FAIRNESS Constraints
`FAIRNESS` and `JUSTICE` constraints in SMV are translated into the `:fairness` option in MoXI's `(check-system ...)`.

We do not support `COMPASSION` constraints - we leave this for future work.

### MODULE Declarations

Each SMV `MODULE` corresponds to a single MoXI `(define-system ...)` command and depending on whether it has any specifications (`LTLSPEC`/`INVARSPEC`/`FAIRNESS`/`JUSTICE`), an additional `(check-system ...)` command.

One feature of `smv2moxi` is that the module hierarchy is preserved - that is,
an input SMV specification with a super/submodule relationship
```
MODULE sub1 ...
MODULE sub2 ...
MODULE sub3 ...
MODULE super
VAR
    s1 : sub1(...);
    s2 : sub2(...);
    s3 : sub3(...);
```

will have its hierarchical structure preserved by `smv2moxi`

``` 
(define-system super
    ...
    :subsys (s1 (sub1 ...))
    :subsys (s2 (sub2 ...))
    :subsys (s3 (sub3 ...))
)
```

### MODULE Instantiations/References of Module Components/Misc. Module Stuff
The usage of submodules and their internal components by a supermodule is mediated entirely by MoXI local variables, which serve as the "wiring" of sorts.

That is, all the input/output variables of the submodules are declared in the supermodule as local variables, assigned their respective values, and passed into the submodule.

For example,
```
MODULE bar(intgr, bln)
VAR
    res1 : word[1];
    res2 : array word[1] of word[2];
...

MODULE foo
VAR
    a : integer;
    b : boolean;
    sub_bar : bar(a, b)
```

turns into

```
(define-system bar
    :input ((intgr Int) (bln Bool))
    :output ((res1 (_ BitVec 1)) (res2 (Array (_ BitVec 1) (_ BitVec 2))))
    ...
)

(define-system foo
    :output ((a Int) (b Bool))
    :local ((b.intgr Int) (b.bln Bool) 
            (b.res1 (_ BitVec 1)) (b.res2 (Array (_ BitVec 1) (_ BitVec 2))))
    :subsys (sub_bar (bar b.intgr b.bln b.res1 b.res2))
)
```

This enables `foo` to make use of variables of its submodules.

### Specifications (LTLSPEC/INVARSPEC)
* For handling `LTLSPEC`, we make use of [PANDA](https://link.springer.com/chapter/10.1007/978-3-642-21437-0_31) to encode LTL specifications and generate SMV modules.
* We translate `INVARSPEC p` (a reachability query) to the `:reachable` option of MoXI's `(check-system ...)`. 