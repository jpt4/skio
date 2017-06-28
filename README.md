## A Relational SKI Combinator Calculus Interpreter

### Introduction
A naive, purely relational interpreter for the SKI Combinator Calculus, written entirely in miniKanren.

### Compatibility
This project was developed against Chez Scheme v9.4-1, and the copy of Will Byrd's miniKanren-with-symbolic-constraints included in this repository. It has not been tested under any other environment.

### Setup
git clone [this-repository]

[launch Chez Scheme]

> (load "skio.scm")

### Use
````skio```` interprets input expressions regardless of parenthesization, converting them to left-associative normal form if necessary, and is best used for forward evaluation.

````skio-aux```` requires fully parenthesized inpute expressions, but is more performant for reverse evaluation, i.e. input expression synthesis.

````laso```` converts expressions to their fully left-associative, parenthesized forms.

````io````, ````ko````, and ````so```` each perform a single step of the eponymous reduction on fully left-associative expressions; useful for checking manual derivations. 

### Examples
Booleans:
> (define T 'K)
> T
K
> (run 1 (q) (skio `(,T a b) q))
(a)
> (define F '(S K))
> (run 1 (q) (skio `(,F a b) q))
(b)






