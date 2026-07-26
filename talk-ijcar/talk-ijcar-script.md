# Script for IJCAR talk


# pg.1   
*Satisfiability modulo theories*: deciding the satisfiability of (first-order)
formulae wrt. various theories.
  - e.g., cvc5, veriT, z3, etc.
  - ubiquotous in formal methods, verification, automated reasoning. 
  - powerful backends for theorem provers (e.g., Isabelle's `sledgehammer`)
[left: logos for cvc5, veriT, z3] 
[right:isabelle-sledgehammer.png]

# pg.2
*SMT-LIB*: standarized concrete and abstract syntax for interacting with SMT solvers.
[image-prompt: paper stack of PDF pages]

# pg.3
For unsatisfiable formulas, SMT solvers may produce proofs.
- not covered by the SMT-LIB standard.
- many competing proof formats:
  - Alethe, LFSC, ...? [what else??]

# pg.4
*Eunoia* is a logical framework for specifying the proofs and proof systems of SMT solvers.

*Ethos* is a C++ checker for Eunoia proofs. 
[figure:latin definitions of Eunoia and Ethos]

# pg.5
SMT-LIB problem for `p ∧ (¬ p)`:
[listing for the problem]
Eunoia proof script given by `cvc5`:
[listing for proof script]

# pg.6
The proof system of `cvc5` is the *co-operating proof calculus* (CPC). 
Given as a Eunoia signature:
[example of a rule encoding]

# pg.7
*LambdaPi* is an implementation of the λΠ-calculus modulo rewriting.
- successor to Dedukti; logical framework. 
- interactive theorem prover (LSP, tactics, etc.)
- focus on interoperability between automated reasoning tools
