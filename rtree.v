(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List. Import ListNotations.

Require Import bipartite mutcoind.

Section Rtree.

  (** coinductive refutations and their translations *)

  Open Scope type_scope.

  (* refutation trees defined in terms of functional lists for first translation step *)

  (* for the root sequent, give the list of applicable rules, and recursively a refutation for one premiss *)
  CoInductive rtree : Type :=
  | rt_grow: forall (s:S)(l: list R), (forall r: R, In r l -> rtree) -> rtree.
  
  (* root of a bogus refutation  tree *)
  Definition rt_root (b: rtree) :=
    match b with rt_grow  s _ _ => s end.

  (* well formedness of bogus refutation trees *)
  (* note that this is the dual definition of well formedness of proof trees *)
  CoInductive rt_wf: rtree -> Prop :=
  |  rt_grow_wf: forall s l f,
      (forall (r:R), In r (fst B s) -> In r l) ->
      (forall (r:R) (w: In r l), rt_wf (f r w) /\ In (rt_root (f r w)) (snd B r)) -> rt_wf (rt_grow s l f).

  (* an example of a refutation tree if we need one *)
  CoFixpoint my_rt(s: S) : rtree :=
    rt_grow  s [] (fun r w => my_rt s).
  
  (* mapping of mutually defined refutations to non-mutually defined ones *)
  (* tech: need to inline functions as guardedness checker baulks otherwise *)
  CoFixpoint wr_seq_to_rtree (s: S)(u: wr_seq s) : rtree :=
    match u with all_r s f => (*  f has type (forall  (r:R), In r (rules s) -> wr_rule  r) *)
      rt_grow s (fst B s) (fun r w => match (f r w) with one_s r (existT _ s (w, u))  => wr_seq_to_rtree s u end)
    end.

  (* tech: convenient to show that wr_seq_to_rtree is equal to its unfolding as simpl does not necessarily reduce *)
  Lemma wr_unfold (s: S)(r: wr_seq s):
   wr_seq_to_rtree s r =  match r with all_r s f => (*  f has type (forall  (r:R), In r (rules s) -> wr_rule r) *)
     rt_grow s (fst B s) (fun r w => match (f r w) with one_s r (existT _ s (w, u))  => wr_seq_to_rtree s u end) end.
  Proof.
    destruct r as [s f].
    replace (wr_seq_to_rtree s (all_r s f)) with
            (match (wr_seq_to_rtree s (all_r s f)) with rt_grow s l f => rt_grow s l f end).
    simpl.
    reflexivity.
    destruct (wr_seq_to_rtree s (all_r s f)).
    reflexivity.
  Qed.

  (* proof of well formedness of translation and root preservation split into two as coinductoin can't prove conjunction *)
  Lemma wr_to_rt_wf_root: forall (s:S)(r: wr_seq s), rt_root (wr_seq_to_rtree s r) = s.
  Proof.
    intros s r; destruct r as [s f]; reflexivity.
  Qed.

  (* well formedness of tree using lemma for root *)
  Lemma wr_to_rt_wf_tree: forall (s:S)(r: wr_seq s), rt_wf  (wr_seq_to_rtree s r).
  Proof.
    cofix CI.
    intros s; destruct r as [s f].
    (* simpl doesn't reduce function definition. need nudge from above *)
    rewrite -> (wr_unfold s (all_r s f)).
    apply (rt_grow_wf s).
    intros r H_r; exact H_r.
    intros r w.
    destruct (f r w) as [r [s0 [w0 u0] ]] eqn:E_frw.
    split.
    apply (CI s0 u0). (* (us_to_brt_wf_tree s0 u0). *)
    rewrite -> (wr_to_rt_wf_root s0 u0).
    exact w0.
  Qed.

  Lemma wr_to_rt_wf: forall (s:S)(r: wr_seq s), let rt := wr_seq_to_rtree s r in rt_wf rt /\ rt_root rt = s.
  Proof.
    intros s r.
    split.
    apply (wr_to_rt_wf_tree s r).
    apply (wr_to_rt_wf_root s r).
  Qed.

End Rtree.
