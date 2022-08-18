# Proof-Producing Congruence Closure in Isabelle/HOL

## Dependencies

- Isabelle/HOL
- [Theory `Union_Find`](https://www.isa-afp.org/theories/separation_logic_imperative_hol/#Union_Find) 
from the Archive of Formal Proofs

## Union Find with Explain Operation

- `Explain_Definition.thy` contains the implementation of the _union_ and the _explain_ operation.
- `Path.thy` contains the formalisation of paths in the union-find data structure, and various 
lemmas about them, in particular the result that the path between two nodes is unique.
- `Helper_Functions.thy` contains the correctness proofs for the helper functions used by the 
_explain_ operation. Among the additional useful lemmas, there is an induction rule based on _apply_unions_
and the proof that _ufa_invar_ implies _ufe_valid_invar_.
- `Explain_Correctness.thy` contains the correctness proofs of _explain_. It is also proved that the order 
of the parameters in _explain_ does not matter, and that the _explain_ function terminates.
- `Examples_Thesis.thy` contains the examples mentioned in the thesis in the chapter about union-find.

## Congruence Closure Algorithm with Explain Operation

- `CC_Definition.thy` contains the implementation of the congruence closure algorithm, consisting of 
the following three main functions: _merge_, _propagate_ and _are_congruent_.
- `CC_Helper_Functions.thy` contains correctness proofs for the helper functions used by the 
congruence closure algorithm.
- `CC_Abstraction.thy` contains an abstract formalisation of congruence closure and the definition
of all the invariants which are needed for the correctness proof of the algorithm.
- `CC_Invars.thy` contains for each invariant the proof that it is an invariant
of _merge_.
There is also a proof that the invariants hold for the initial empty data structure.
- `CC_Termination.thy` contains a proof, which states that _propagate_ terminates.
- `CC_Correctness.thy` contains the correctness proof for the congruence closure algorithm, 
based on the previously defined invariants.
- `CC_Explain.thy` contains the implementation of the _cc_explain_ algorithm for congruence closure.
It is proven that it terminates and that it is valid. An invariant for the additional union find used in the _cc_explain_
function is defined.
- `CC_Explain_Correctness.thy` contains an unfinished proof about the correctness of _cc_explain_.
- `CC_Examples_Thesis.thy` contains the examples mentioned in the thesis in the chapters about congruence closure and _cc_explain_.


