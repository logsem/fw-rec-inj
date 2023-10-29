Require Export IxFree.Base.
Require Export IxFree.Connectives.
Require Export IxFree.Relations.
Require Export IxFree.Contractive.
Require Export IxFree.Fixpoint.

Module TacticSynonyms.
  Tactic Notation "reflexivity"            := first [reflexivity    | creflexivity].
  Tactic Notation "symmetry"               := first [symmetry       | csymmetry].
  Tactic Notation "transitivity" constr(c) := first [transitivity c | ctransitivity c].
  Tactic Notation "etransitivity"          := first [etransitivity  | cetransitivity].
End TacticSynonyms.
