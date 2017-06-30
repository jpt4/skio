## A Relational SKI Combinator Calculus Interpreter

### Introduction
A naive, purely relational interpreter for the SKI Combinator Calculus, written in miniKanren.

### Compatibility
This project is developed against Chez Scheme v9.4-1, and the copy of Will Byrd's miniKanren-with-symbolic-constraints included in this repository. It has not been tested under any other configuration.

### Setup
git clone [this-repository]

[launch Chez Scheme]

\> (load "skio.scm")

### Contents
````skio```` interprets input expressions regardless of parenthesization, converting them to left-associative normal form if necessary, and is best used for forward evaluation.

````skio-syn```` elides the left-associativity preprocessor, thus requiring fully parenthesized input expressions, to allow for greater variety during reverse expression synthesis.

````laso```` converts expressions to their fully left-associative, parenthesized forms.

````io````, ````ko````, and ````so```` each perform a single step of the eponymous reduction on fully left-associative expressions; useful for checking manual derivations. 

An input expressions is a quoted (potentially nested) list of symbols, including the reserved symbols ````S````, ````K````, and ````I````.

For forward evaluation with `skio`, set ````run```` to produce a single answer, i.e. ````(run 1 (q) (skio EXP q))````

### Examples
Booleans:
\> (define T 'K)
\> T
K
\> (run 1 (q) (skio `(,T a b) q))
(a)
\> (define F '(S K))
\> (run 1 (q) (skio `(,F a b) q))
(b)






