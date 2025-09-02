(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List Program. Import ListNotations.

Require Import bipartite lemmas mutind ptree.

Section PtreesWf.

  (** well founded relations on ptrees and lists of ptrees for termination proofs *)

  (* well founded recursion pattern on ptree: cut a subtree or recurse on leftmost subtree *)
  Definition pt_cut_lft (ps p: ptree) : Prop := exists s s0 ss f,
    (ps = pt_grow s ss (fl_tl s0 ss f) /\ p = pt_grow s (s0::ss) f) \/
    (ps = fl_hd s0 ss f /\ p = pt_grow s (s0::ss) f).

  (* args of recursive calls need to be related to function arg so pt_cut_lft supports recursion pattern like this:
     phi pt_grow s [] f =>        <something>
     phi pt_grow s (s0::ss) f =>  <term involving phi (fl_hd s0 ss f) and phi (pt_grow s ss (fl_tl s0 ss f)> *)
  
  (* inversion lemmas give smaller arg in for recursive calls  witnessed by well foundedness *)
  Definition pt_cut_lft_inv_cut s s0 ss f (a: Acc pt_cut_lft (pt_grow s (s0::ss) f)):
    Acc pt_cut_lft (pt_grow s ss (fl_tl s0 ss f)) :=
    match a with Acc_intro _ H => H (pt_grow s ss (fl_tl s0 ss f))
      (ex_intro _ s (ex_intro _ s0 (ex_intro _ ss (ex_intro _ f (or_introl (conj eq_refl eq_refl))))))
    end.

  (* second inversion lemma *)
  Definition pt_cut_lft_inv_lft s s0 ss f (a: Acc pt_cut_lft (pt_grow s (s0::ss) f)) : Acc pt_cut_lft (fl_hd s0 ss f) :=
    match a with Acc_intro _ H => H (fl_hd s0 ss f)
     (ex_intro _ s (ex_intro _ s0 (ex_intro _ ss (ex_intro _ f (or_intror (conj eq_refl eq_refl))))))
    end.

  (* example: count the nodes of a prooftree *)
  Open Scope nat_scope.
  Fixpoint pt_num_nodes_aux (pt: ptree)(w: Acc pt_cut_lft  pt) :  nat :=
    match pt return (Acc pt_cut_lft  pt) -> nat with
    | pt_grow s [] f => (fun _ => 1)
    | pt_grow s (s0::ss) f => fun w =>  pt_num_nodes_aux (fl_hd s0 ss f) (pt_cut_lft_inv_lft  s s0 ss f w) +
                                        pt_num_nodes_aux (pt_grow s ss (fl_tl s0 ss f)) (pt_cut_lft_inv_cut s s0 ss f w)
    end w.
  Close Scope nat_scope.

  (* local tatics to extract and invert equalities between inductive types *)
  Ltac extract x  x' from y := assert (x = x') by (injection y; easy || dependent destruction y; easy); subst x'.
  Ltac align x  x' from  y :=let f := fresh in
                             assert  (f: x = x') by (injection y; easy || dependent destruction y; easy); inversion f.
  Ltac eq_prod x y from H := assert (x = y) by
        ((apply (f_equal fst) in H; simpl in H; assumption) || (apply (f_equal snd) in H; simpl in H; assumption)); subst y.

  (* well foundedness of pt_cut_lft to allow recursive definitions *)
  Lemma pt_cut_lft_wf : well_founded pt_cut_lft.
  Proof.
    unfold well_founded.
    intro p.
    induction p as [s l f IHf].
    generalize dependent l.
    intro l.
    induction l as [| s0 ss IHss].
    intros f. intros H_all_subs.
    apply Acc_intro.
    intros p_sub H_psub.
    destruct H_psub as [s' [s0' [ss' [f' [[H_cut_ps H_cut_p] | [H_lft_ps H_lft_p]]]]]].
    (* case cut subtree *)
    align  ([]: list S) (s0'::ss') from H_cut_p.
    (* case go left *)
    align  ([]: list S) (s0'::ss') from H_lft_p.                                   
    (* l = s0::ss *)
    intros f IHf.
    apply Acc_intro.
    intros p_sub H_psub.
    destruct H_psub as [s' [s0' [ss' [f' [[H_cut_ps H_cut_p] | [H_lft_ps H_lft_p]]]]]].
    (* case cut subtree *)
    extract s s' from H_cut_p. extract s0 s0' from H_cut_p. extract ss ss' from H_cut_p. extract f f' from H_cut_p.
    clear H_cut_p. subst p_sub.
    refine  (IHss (fl_tl s0 ss f) _).
    intros s1 w.
    unfold fl_tl.
    apply (IHf s1 (or_intror w)).
    (* lft case *)
    extract s s' from H_lft_p. extract s0 s0' from H_lft_p. extract ss ss' from H_lft_p. extract f f' from H_lft_p.
    clear H_lft_p. subst p_sub.
    unfold fl_hd.
    apply (IHf s0 (or_introl eq_refl)).
  Qed.

  (* well foundedness can now be used to compute nodes *)
  Example pt_num_nodes (pt: ptree) :  nat := pt_num_nodes_aux pt (pt_cut_lft_wf pt).

  (* for similar recursion pattern, list of all subtrees of a ptree *)
  Definition pt_nodes (p: ptree) := match p with pt_grow s l f => map_in l f end.
  
  (* promised recursion pattern on lists of ptrees: go down on leftmost tree or drop leftmost tree *)
  Definition lpt_cut_lft (lps lp: list ptree) : Prop :=
    (exists p0, lp = p0::lps) \/ (exists p0 ps,  lps = pt_nodes p0 /\ lp = p0::ps).

  (* inversion lemmas to witness decrease in recursive call *)
  Definition lpt_cut_lft_inv_cut p0 ps (a: Acc lpt_cut_lft (p0::ps)) : Acc lpt_cut_lft ps :=
    match a with Acc_intro _ H => H ps (or_introl (ex_intro _ p0 eq_refl)) end.

  (* second inversion lemma *)
  Definition lpt_cut_lft_inv_lft p0 ps (a: Acc lpt_cut_lft (p0::ps)) : Acc lpt_cut_lft (pt_nodes p0) :=
    match a with Acc_intro _ H => H (pt_nodes p0) (or_intror (ex_intro _ p0 (ex_intro _ ps (conj eq_refl eq_refl)))) end.

  (* similar example as before: nodes in a list of proof trees *)
  Open Scope nat_scope.
  Fixpoint lpt_nodes_aux (l: list ptree)(w: Acc lpt_cut_lft l) := match l return (Acc lpt_cut_lft l) -> nat with
  | [] => fun _ => 0                                                                   
  | p0::ps => fun w => 1 + lpt_nodes_aux ps           (lpt_cut_lft_inv_cut p0 ps w) +
                           lpt_nodes_aux (pt_nodes p0)(lpt_cut_lft_inv_lft p0 ps w)
  end w.                                                                                        
  Close Scope nat_scope.
  
  (* auxilary lemma to prove well foundedness of above relation by well founded recursion on trees *)
  (* tech: uses well foundedness of corresponding relation on proof trees *)
  Lemma lpt_cut_lft_wf_aux : forall (p: ptree), Acc lpt_cut_lft (pt_nodes p).
  Proof.
    intro p. induction p  as [p IHp] using (well_founded_induction  pt_cut_lft_wf).
    apply Acc_intro.
    intros lps H_lps.
    destruct H_lps as [H_cut | H_lft].
    (* cut a subtree *)
    destruct H_cut as [p0 H_p0].
    destruct p as [s l f].
    (* show that l is of form s0::ss *)
    destruct l as [| s0 ss].
    (* l = emp is impossible *)
    simpl in H_p0. inversion H_p0.
    (* have l = s0::ss *)
    simpl in H_p0.
    extract (map_in ss (fl_tl s0 ss f)) lps from H_p0.
    specialize (IHp (pt_grow s ss (fl_tl s0 ss f))).
    unfold pt_nodes in IHp.
    apply IHp.
    unfold pt_cut_lft.
    exists s.
    exists s0.
    exists ss.
    exists f.
    left.
    easy.
    (* phew. case go to subnodes *)
    destruct H_lft as [p0 [ ps [ H_lps H_ps]]].
    subst lps.
    apply (IHp p0).
    unfold pt_cut_lft.
    destruct p as [s l f].
    (* case l = [] is impossible *)
    destruct l as [| s0 ss].
    simpl in H_ps.
    inversion H_ps.
    (* have l = s0::ss *)
    simpl in H_ps.
    extract (fl_hd s0 ss f) p0 from H_ps.
    exists s.
    exists s0.
    exists ss.
    exists f.
    right; easy.
  Qed.

  (* well foundedness of lpt_cut_lft for well founded recursive definition on list ptree *)
  Lemma lpt_cut_lft_wf: well_founded lpt_cut_lft.
  Proof.
    unfold well_founded.
    intro l; induction l as [| p0 ps IHps].
    (* empty list *)
    apply Acc_intro.
    intros lps H_lps.
    destruct H_lps as [[p' H_p'] |[p' [ps' [H_lps  H_p]]]].
    (* case cut first tree *)
    inversion H_p'.
    (* case go down subtree *)
    inversion H_p.
    (* case l = p0::ps *)
    apply Acc_intro.
    intros lps H_lps.
    destruct H_lps as [H_cut | H_lft].
    (* case cut first tree is IH *)
    destruct H_cut as [p' H_p'].
    extract ps lps from H_p'.
    assumption.
    (* case go down to subtree *)
    destruct H_lft as [p' [ps' [H_lps  H_p]]].
    rewrite -> H_lps.
    apply (lpt_cut_lft_wf_aux p').
  Qed.

  (* example: instantiation of the node counting function *)
  Example lpt_nodes (l: list ptree) : nat := lpt_nodes_aux l (lpt_cut_lft_wf l).

End PtreesWf.
