
# Congruence Closure Algorithm with Explain Operation

- `CC_Definition.thy` contains the implementation of the congruence closure algorithm, consisting of 
the following three main functions: _merge_, _propagate_ and *are_congruent*.
- `CC_Helper_Functions.thy` contains correctness proofs for the helper functions used by the 
congruence closure algorithm.
- `CC_Abstraction.thy` contains an abstract formalisation of congruence closure and the definition
of all the invariants which are needed for the correctness proof of the algorithm.
- `CC_Invars.thy` contains for each invariant the proof that it is an invariant
of _merge_.
There is also a proof that the invariants hold for the initial empty data structure.
- `CC_Termination.thy` contains a proof which states that _propagate_ terminates.
- `CC_Correctness.thy` contains the correctness proof for the congruence closure algorithm, 
based on the previously defined invariants.
- `CC_Explain.thy` contains the implementation of the *cc_explain* algorithm for congruence closure.
It is proven that it terminates and that it is valid. An invariant for the additional union find used in the *cc_explain*
function is defined.
- `CC_Examples_Thesis.thy` contains the examples mentioned in the thesis in the chapters about congruence closure and *cc_explain*.
- `CC_Explain_Helper_Lemmata` contains lemmata about *lowest_common_ancestor* and *explain_along_path* as well as induction rules for *explain_along_path* and *cc_explain_aux*.
- `CC_Definition2` defines the extended *congruence_closure_t* record with the timestamps for the edges of the proof forest.
The *merge* function is modified correspondingly and there is a proof about the equivalence of the original *merge* function and the modified *merge_t* function.
- `CC_Explain2_Definition` contains an alternative definition of the *cc_explain* function, without the additional union-find. An induction rule for *explain_along_path2* is defined, and there are some lemmata about the relation between *explain_along_path* and *explain_long_path2*.
- `CC_Explain2_Termination` contains the definitions and proofs of invariants of *merge_t* that show the correctness of the timestamps. The invariant proof is still unfinished. Using these invariants, the termination of *cc_explain2* is proven and an induction rule is defined for *cc_explain2*. 
- `CC_Explain2_Correctness` contains the correctness proof of *cc_explain2*.
- `CC_Explain_Explain2_Equivalence` defines an invariant of *cc_explain* that characterizes the relation between the additional union-find and the pending list. 
Using this invariant, the equivalence of *cc_explain* and *cc_explain2* is proven. From this theorem and the correctness of *cc_explain2*, it follows that *cc_explain* is also correct.
    