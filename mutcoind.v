(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List. Import ListNotations.

Require Import bipartite.

Section MutCoInd.

  (** data structures for coinductive refutations *)

  Open Scope type_scope.

  (* mutually defined coinductive refutations *)
  (* a witnessed refutable has a refutable premiss for every applicable rule.  *)
  (* a witnessed refuting rule has one premiss that is witnessed refutable  *)
  CoInductive wr_seq: S ->  Type :=
  | all_r : forall (s:S), (forall (r:R), In r (fst B s) -> wr_rule r) -> wr_seq s
  with wr_rule: R -> Type :=
  | one_s : forall (r:R),  { s:S & In s (snd B r) * wr_seq s }  -> wr_rule r .

End MutCoInd.
