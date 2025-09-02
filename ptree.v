(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List.

Require Import bipartite mutind.


Section Ptree.

  (** proof trees and translation from mutually inductive proofs that preserves well-formedness *)
  
  (* proof trees defined in terms of functional lists *)
  Inductive  ptree  : Type :=
  | pt_grow: S -> forall (l: list S), (forall s0:S, In s0 l -> ptree) ->  ptree.

  (* root of a proof tree *)
  Definition pt_root  (b: ptree) :=
    match b with pt_grow s _ _ => s end.

  (* well formedness of ptrees *)
  Inductive ptree_wf: ptree -> Prop :=
  | grow_wf: forall s l f,
      (exists (r:R), In r (fst B s) /\ forall (s':S), In s' (snd B r) -> In s' l) /\
      (forall (s':S)(w: In s' l), ptree_wf (f s' w) /\ pt_root (f s' w) = s') -> ptree_wf (pt_grow s l f).
  
  (* translation from mutually inductive trees to non-mutually inductive trees *)
  (* tech: need to inline as termination checker baulks on non-anonymous, elsewhere defined functions *)
  (* tech: need convoy patter style double match to keep type checker happy *)
  Fixpoint wp_seq_to_ptree (s:S)(p: wp_seq s): ptree  :=
    match p with one_r s (existT _ r (w, j)) => (* r:R  w: In r (rules s)  j: j_rule B r *)
    match j with all_s r f => (* f: forall s', In s' (prems r) -> j_rule B s') *)
      pt_grow s (snd B r) (fun s0 (w: In s0 (snd B r)) => wp_seq_to_ptree s0 (f s0 w)) end end.

  (* translation between ex sequents and bogus trees delivers well formed trees *)
  (* tech: need mutually dependent lemmas as induction principle for mutually inductive types sucks *)
  Lemma wp_seq_to_ptree_wf (s:S)(p: wp_seq s): let pt := (wp_seq_to_ptree s p) in ptree_wf pt /\ pt_root pt = s
  with j_rule_to_ptree_list_wf (r:R)(j: wp_rule r): match j with all_s r f => 
    forall s' (w: In s' (snd B r)), let p' := (wp_seq_to_ptree s'  (f s' w)) in  ptree_wf p' /\ pt_root p' = s' end.
  Proof.
    destruct p as [rules s  [r [H_r_in_rules j]]].
    simpl.
    destruct j as [prems r f] eqn:E_u.
    simpl.
    split.
    (* well formedness *)
    specialize (j_rule_to_ptree_list_wf r j).
    apply (grow_wf s (prems r) ).
    split.
    (* have correct rule application *)
    exists r.
    split.
    subst rules. assumption.
    subst prems. easy.
    (* show that all subtrees are wellformed *)
    rewrite -> E_u in j_rule_to_ptree_list_wf.    
    simpl in j_rule_to_ptree_list_wf.
    assumption.
    reflexivity.
    (* l2 *)
    destruct j as [prems r f] eqn:E_u.
    simpl.
    intros s w.
    refine (wp_seq_to_ptree_wf s _).
  Qed.
  
End Ptree.
