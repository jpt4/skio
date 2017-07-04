## A Relational SKI Combinator Calculus Interpreter

### Introduction
A naive, purely relational interpreter for the SKI Combinator Calculus, written in miniKanren.

### Compatibility
This project is developed against Chez Scheme v9.4-1, and the copy of Will Byrd's miniKanren-with-symbolic-constraints included in this repository. It has not been tested under any other configuration.

### Setup
$ git clone [this-repository]

$ cd [clone directory]

$ [launch Chez Scheme]

\> (load "skio.scm")

### Contents
`skio` interprets input expressions regardless of parenthesization, converting them to left-associative normal form if necessary, and is best used for forward evaluation.

`skio-syn` elides the left-associativity preprocessor, thus requiring fully parenthesized input expressions, to allow for greater variety during reverse expression synthesis.

`laso` converts expressions to their fully left-associative, parenthesized forms.

`io`, `ko`, and `so` each perform a single step of the eponymous reduction on fully left-associative expressions; useful for checking manual derivations. 

An input expression is a quoted (potentially nested) list of symbols, including the reserved symbols `S`, `K`, and `I`.

For both `skio` and `skio-syn`, the number of results requested must be included, e.g. `(skio EXP NUM)`. Because the evaluation order of miniKanren is unspecified, the most reduced answer may not be the first produced, especially for expressions which simulate recursion.

### Examples
`> (skio '(S I I a) 1)`

`((a a))`

`> (skio '(S I I (S I I)) 1)`

`((((S I) I) ((S I) I)))`

`> (skio '(S (K a) (S I I) b) 1)`

`((a (b b)))`

`> (define beta '(S (K a) (S I I)))`

`> beta`

`(S (K a) (S I I))`

`> (define exp (list 'S 'I 'I beta))`

`> exp`

`(S I I (S (K a) (S I I)))`

`> (skio exp 3)`

`((((S I) I) ((S (K a)) ((S I) I)))`

`  (((S I) I) ((S (K a)) ((S I) I)))`

`    (((S (K a)) ((S I) I)) ((S (K a)) ((S I) I))))`

`> (skio-syn 'a 10)`

(a

(I a)

((K a) _.0)

(I (I a))

(I ((K a) _.0))

((K (I a)) _.0)

(I (I (I a))) 

((K ((K a) _.0)) _.1) 

(I (I ((K a) _.0)))

(((S K) _.0) a))







