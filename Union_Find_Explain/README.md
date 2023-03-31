
# Union Find with Explain Operation

- `Explain_Definition.thy` contains the implementation of the _union_ and the _explain_ operation.
- `Path.thy` contains the formalisation of paths in the union-find data structure, and various 
lemmas about them, in particular the result that the path between two nodes is unique.
- `Helper_Functions.thy` contains the correctness proofs for the helper functions used by the 
_explain_ operation. Among the additional useful lemmas, there is an induction rule based on _apply_unions_
and the proof that _ufa_invar_ implies _ufe_valid_invar_.
- `Explain_Correctness.thy` contains the correctness proofs of _explain_. It is also proved that the order 
of the parameters in _explain_ does not matter, and that the _explain_ function terminates.
- `Examples_Thesis.thy` contains the examples mentioned in the thesis in the chapter about union-find.