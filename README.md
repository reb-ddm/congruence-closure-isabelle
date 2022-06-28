# Proof-Producing Congruence Closure in Isabelle/HOL

## Dependencies

- Isabelle/HOL
- [Theory `Union_Find`](https://www.isa-afp.org/theories/separation_logic_imperative_hol/#Union_Find) 
from the Archive of Formal Proofs

## Union Find with Explain Operation

- `Explain_Definition.thy` contains the implementation of the Union and the Explain operation.
- `Path.thy` contains the formalisation of paths in the union-find data structure, and various 
lemmas about them, in particular the result that the path between two nodes is unique.
- `Helper_Functions.thy` contains the correctness proofs for the helper functions used by the 
explain operation. Among the additional useful lemmas, there is an induction rule based on apply_unions
and the proof that ufa_invar implies ufe_invar.
- `Explain_Correctness.thy` contains the correctness proofs of explain. It is also proved that the order 
of the parameters in explain does not matter, and that the explain function terminates.

## Congruence Closure Algorithm with Explain Operation

- `CC_Definition.thy` contains the implementation of the congruence closure algorithm, consisting of 
the following three main functions: merge, propagate and are_congruent.
- `CC_Helper_Functions.thy` contains correctness proofs for the helper functions used by the 
congruence closure algorithm.
- `CC_Abstraction.thy` contains an abstract formalisation of congruence closure, and the definition
of all the invariants which are needed for the correctness proof of the algorithm.
- `CC_Invars.thy` contains for each invariant the proof that the invariant is invariant
after merge was executed. There is a missing proof about the termination of propagate.
There is also a proof that the invariants hold for the initial empty data structure.
- `CC_Correctness.thy` contains the correctness proof for the congruence closure algorithm, 
based on the previously defined invariants.
- `CC_Explain.thy` contains the implementation of the explain algorithm for congruence closure.
The correctness proof for explain is not finished, and the termination proof is also missing.
There is a validity proof and an invariant for the additional union find used in the explain
function.
