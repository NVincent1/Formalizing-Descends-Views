# Formalizing Descends Views
Formalizing Descend's views in Rocq and proving properties that we want them to have

`Proof.v` contains the definition of a function that transforms a re-indexing function into a view, and a theorem that proves that, for an injective re-indexing function, this view holds the property that we want (defined in this file as well).

`Tactic.v` contains tactics for proof automation for this property (use examples are in `Examples_automation.v`).\\
TODO: Look for possibilities for automation of injectivity proof, or why such automation would not be possible.

The folder `Execution_resources` contains a formalization of Descend's execution resources, and proofs that the formalization is correct.

The file `execution_resources_and_views.v` contains a first attempt to formalize the interactions between execution resources and views by providing a property on a view `v` and an execution resource `e` that should hold if, and only if, `v[[e]]` can be called.
