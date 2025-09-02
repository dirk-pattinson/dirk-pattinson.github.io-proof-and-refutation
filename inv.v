(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List Program. Import ListNotations.
Require Import bipartite lemmas mutind.

Section Invariance.

  (* invariance lemmas for fixpoint computation: iteration does not lose sequents *)
                                             
  (* tatics to extract and subst equalities from equalities between products *)
  Ltac eq_prod x y from H := assert (x = y) by
        ((apply (f_equal fst) in H; simpl in H; assumption) || (apply (f_equal snd) in H; simpl in H; assumption)); subst y.

  (* and from dependent equalities. this should be provable without dependent destruction though *)
  Ltac extract x  x' from y := assert (x = x') by (injection y; easy || dependent destruction y; easy); subst x'.
  
  (* four invariance lemmas: iter does not `lose' sequents. *)
  Lemma iter_inv_lr_1: forall (l: list S)(pl: list proof)(nrl: list (sref (p_roots pl)))(npl: list proof),
       projT1 (iter_w l pl) = (nrl, npl) -> forall s, In s l -> {In s (s_roots (p_roots pl) nrl)} +  {In s (p_roots npl)}.
  Proof.
    intros l pl. induction l as [| s0 ss IHss].
    (* l = [] *)
    intros nrl npl H_iter s H_s_in_emp. inversion H_s_in_emp.
    (* step case l = s0::ss  *)
    intros nrl npl H_iter s H_s_in_roots.
    apply (in_inv_dec S_dec s0 s ss) in H_s_in_roots.
    simpl in H_iter.
    destruct (iter_w ss pl) as [[IHnrl IHnpl] ev].
    specialize (IHss IHnrl IHnpl eq_refl s).
    destruct  (wp_seq_dec3 s0 pl) as [H_s0_wp | H_s0_wsr].
    (* case found new proof *)
    eq_prod IHnrl nrl from H_iter.
    eq_prod (existT (fun s : S => wp_seq s) s0 H_s0_wp :: IHnpl) npl from H_iter.
    simpl.
    destruct H_s_in_roots as [L|R].
    right; intuition.
    specialize (IHss R).
    intuition.
    (* case found new ref *)
    eq_prod (existT (wsr_seq (p_roots pl)) s0 H_s0_wsr :: IHnrl) nrl from H_iter.
    eq_prod IHnpl npl from H_iter.
    simpl.
    intuition.
  Qed.

 
  Lemma iter_inv_lr_2: forall (l: list S)(pl: list proof)(nrl: list (sref (p_roots pl)))(npl: list proof),
        projT1 (iter_w l pl) = (nrl, npl) ->
        forall s, In s (p_roots pl) -> {In s (s_roots (p_roots pl) nrl)} + {In s (p_roots npl)}.
  Proof.
    intros l pl. induction l as [| s0 ss IHss].
    (* l = [] *)
    intros nrl npl H_iter s H_s_in_emp.
    eq_prod pl npl from H_iter.
    intuition.
    (* step case l = s0::ss  *)
    intros nrl npl H_iter s H_s_in_roots.
    simpl in H_iter.
    destruct (iter_w ss pl) as [[IHnrl IHnpl] ev].
    specialize (IHss IHnrl IHnpl eq_refl s).
    destruct  (wp_seq_dec3 s0 pl) as [H_s0_wp | H_s0_wsr].
    (* case found new proof *)
    eq_prod IHnrl nrl from H_iter.
    eq_prod (existT (fun s : S => wp_seq s) s0 H_s0_wp :: IHnpl) npl from H_iter.
    simpl.
    intuition.
    (* case found new ref *)
    eq_prod (existT (wsr_seq (p_roots pl)) s0 H_s0_wsr :: IHnrl) nrl from H_iter.
    eq_prod IHnpl npl from H_iter.
    simpl.
    intuition.
  Qed.

  Lemma iter_inv_rl_1: forall (l: list S)(pl: list proof)(nrl: list (sref (p_roots pl)))(npl: list proof),
    projT1 (iter_w l pl) = (nrl, npl) ->
    forall s, In s (s_roots (p_roots pl) nrl) -> {In s l} + {In s (p_roots pl)}.
  Proof.
    intros l pl. induction l as [| s0 ss IHss].
    (* l = [] *)
    intros nrl npl H_iter s H_s_in_emp.
    eq_prod ([]: list (sref(p_roots pl)))  nrl from H_iter.
    simpl in H_s_in_emp. inversion H_s_in_emp.
    (* step case l = s0::ss  *)
    intros nrl npl H_iter s H_s_in_roots.
    simpl.
    simpl in H_iter.
    destruct (iter_w ss pl) as [[IHnrl IHnpl] ev].
    specialize (IHss IHnrl IHnpl eq_refl s).
    destruct  (wp_seq_dec3 s0 pl) as [H_s0_wp | H_s0_wsr].
    (* case found new proof *)
    eq_prod IHnrl nrl from H_iter.
    eq_prod (existT (fun s : S => wp_seq s) s0 H_s0_wp :: IHnpl) npl from H_iter.
    intuition.
    (* case found new ref *)
    eq_prod (existT (wsr_seq (p_roots pl)) s0 H_s0_wsr :: IHnrl) nrl from H_iter.
    eq_prod IHnpl npl from H_iter.
    assert (H_roots:  In s (s0::(s_roots (p_roots pl) IHnrl))).
    simpl; simpl in H_s_in_roots; assumption.
    destruct (in_inv_dec S_dec s0 s ( s_roots (p_roots pl) IHnrl) H_roots) as [H_hd | H_tl].
    intuition.
    intuition.    
  Qed.


  Lemma iter_inv_rl_2: forall (l: list S)(pl: list proof)(nrl: list (sref (p_roots pl)))(npl: list proof),
    projT1 (iter_w l pl) = (nrl, npl) -> forall s, In s (p_roots npl) -> {In s l} + {In s (p_roots pl)}.
  Proof.
    intros l pl. induction l as [| s0 ss IHss].
    (* l = [] *)
    intros nrl npl H_iter s H_s_in_roots.
    eq_prod pl npl from H_iter.
    intuition.
    (* l = s0::ss *)
    intros nrl npl H_iter s H_s_in_roots.
    simpl.
    simpl in H_iter.
    destruct (iter_w ss pl) as [[IHnrl IHnpl] ev].
    specialize (IHss IHnrl IHnpl eq_refl s).
    destruct (wp_seq_dec3 s0 pl) as [H_wp | H_wsr].
    (* case found new proof *)
    eq_prod (existT (fun s : S => wp_seq s) s0 H_wp :: IHnpl) npl from H_iter.
    eq_prod IHnrl nrl from H_iter.
    simpl in H_s_in_roots.
    assert (H_roots:  In s (s0::(p_roots IHnpl))).
    simpl; simpl in H_s_in_roots; assumption.
    destruct (in_inv_dec S_dec s0 s (p_roots IHnpl) H_roots) as [H_hd | H_tl].
    intuition.
    specialize (IHss H_tl).
    intuition.
    simpl in H_iter.
    eq_prod IHnpl npl from H_iter.
    intuition.
  Qed.

  (* TODO: make more beautiful! *)
  Lemma iter_inv_lr: forall (l: list S)(pl: list proof)(a: Acc lpt_ls_iter l)(npl: list proof)(nrl: list (sref (p_roots npl))),
      iter_fp_acc l pl a = existT _ npl nrl ->  forall s,
      {In s l} + {In s (p_roots pl)} -> {In s (s_roots (p_roots npl) nrl)} + {In s (p_roots npl)}.
  Proof.
    intro l. induction l as [l IHl] using (well_founded_induction_type lpt_ls_iter_wf). 
    intros pl a npl nrl H_eq s H_in.
    (* destruct a to kick simpl *)
    destruct a eqn: H_a.
    simpl in H_eq.
    destruct (iter_w l pl) as ((nrl_prev, npl_prev), e) eqn:H_iter_w.
    assert (H_prev_step:  {In s (s_roots (p_roots pl) nrl_prev)} + {In s (p_roots npl_prev)}).
    destruct H_in as [H_s_in_l | H_s_in_pl ].
    (* case s refuted *)
    apply (iter_inv_lr_1 l pl nrl_prev npl_prev).
    rewrite -> H_iter_w. simpl. reflexivity. assumption.
    (* case s proved *)
    apply (iter_inv_lr_2 l pl nrl_prev npl_prev).
    rewrite -> H_iter_w. simpl. reflexivity. assumption.
    (* case termination *)
    destruct e as [H_lft | H_rgt].

    extract npl_prev npl from H_eq.
    extract ((eq_rect pl (fun x : list proof => list (sref (p_roots x))) nrl_prev npl_prev (proj1' H_lft))) nrl from H_eq.
    destruct H_lft as [H_l1 H_l2].
    simpl.
    simpl in H_l1.
    subst pl.
    simpl.
    assumption.
    (* case recursive call *)
    (* have the following:
       - iter_w l pl = nrl_prev, npl_prev
       - iter_fp_acc (roots nrl_prev, roots npl) = (npl, nrl)
       have statement already for nrl_prev, npl_prev. So use IH *)
    specialize (IHl (s_roots (p_roots pl)  nrl_prev)).
    (* lpt_ls_iter_inv
     : forall (pl : list proof) (nl : list (sref (p_roots pl))) (l : list S),
       Acc lpt_ls_iter l -> length nl < length l -> Acc lpt_ls_iter (s_roots (p_roots pl) nl) *)
    assert (H_smaller: lpt_ls_iter (s_roots (p_roots pl) nrl_prev) l).
    unfold lpt_ls_iter.
    simpl in H_rgt.
    rewrite -> (len_pres pl nrl_prev).
    assumption.
    specialize (IHl H_smaller).
    specialize (IHl npl_prev).
    simpl in H_rgt.
    specialize (IHl (a0 (s_roots (p_roots pl) nrl_prev) (eq_ind_r (fun n : nat => n < length l) H_rgt (len_pres pl nrl_prev)))).
    (*
    specialize (IHl (lpt_ls_iter_inv pl nrl_prev l a H_rgt)).
    *)
    specialize (IHl npl nrl).
    specialize (IHl H_eq).
    specialize (IHl s).
    specialize (IHl H_prev_step).
    assumption.
  Qed.
  
  (* TODO:  eliminate the two applications of the rl-inversion lemmas in base case and recursive case *)
  Lemma iter_inv_rl: forall (l: list S)(pl: list proof)(a: Acc lpt_ls_iter l)(npl: list proof)(nrl: list (sref (p_roots npl))),
    iter_fp_acc l pl a = existT _ npl nrl ->  forall s,
    {In s (s_roots (p_roots npl) nrl)} + {In s (p_roots npl)} -> {In s l} + {In s (p_roots pl)}.
  Proof.
    intro l. induction l as [l IHl] using (well_founded_induction_type lpt_ls_iter_wf). 
    intros pl a npl nrl H_eq s H_in.
    (* destruct a to kick simpl *)
    destruct a eqn: H_a.
    simpl in H_eq.
    destruct (iter_w l pl) as ((nrl_prev, npl_prev), e) eqn:H_iter_w.
    destruct e as [H_lft | H_rgt].
    (* case termination *)
    (* should be that 
       - iter_w l pl = nrl_prev, npl_prev
       - npl_prev = npl
       - nrl_prev = nrl modulo eq_induction *)
    destruct H_lft as [H_pl H_len].
    simpl in H_pl.
    simpl in H_eq.
    extract npl_prev npl from H_eq.
    assert (H_nrl: nrl =  (eq_rect pl (fun x : list proof => list (sref (p_roots x))) nrl_prev npl_prev H_pl)).
    dependent destruction H_eq. reflexivity.
    subst npl_prev.
    simpl in H_nrl.
    subst nrl_prev.
    (* now have after subst:
       - iter_w l pl = nrl, pl
      should be able to use earlier inversion lemmas? *)
    destruct H_in as [H_ref | H_pf].
    (* first case, use inv_rl_1 *)
    (* iter_inv_rl_1
     : forall (l : list S) (pl : list proof) (nrl : list (sref (p_roots pl))) (npl : list proof),
       projT1 (iter_w l pl) = (nrl, npl) -> forall s : S, In s (s_roots (p_roots pl) nrl) -> In s l \/ In s (p_roots pl) *)
    apply (iter_inv_rl_1 l pl nrl pl).
    rewrite -> H_iter_w.
    simpl.
    reflexivity. assumption.
    (* second case, use inv_rl_2 *)
    (* iter_inv_rl_2
     : forall (l : list S) (pl : list proof) (nrl : list (sref (p_roots pl))) (npl : list proof),
       projT1 (iter_w l pl) = (nrl, npl) -> forall s : S, In s (p_roots npl) -> In s l \/ In s (p_roots pl) *)
    apply (iter_inv_rl_2 l pl nrl pl).
    rewrite -> H_iter_w.
    simpl.
    reflexivity. assumption.
   (* base case done. recursive call case ... *)
   (* have the following:
       - iter_w l pl = nrl_prev, npl_prev
       - iter_fp_acc (roots nrl_prev, roots npl) = (npl, nrl)
       have statement already for nrl_prev, npl_prev. So use IH *)
    specialize (IHl (s_roots (p_roots pl)  nrl_prev)).
    (* lpt_ls_iter_inv
     : forall (pl : list proof) (nl : list (sref (p_roots pl))) (l : list S),
       Acc lpt_ls_iter l -> length nl < length l -> Acc lpt_ls_iter (s_roots (p_roots pl) nl) *)
    assert (H_smaller: lpt_ls_iter (s_roots (p_roots pl) nrl_prev) l).
    unfold lpt_ls_iter.
    simpl in H_rgt.
    rewrite -> (len_pres pl nrl_prev).
    assumption.
    specialize (IHl H_smaller).
    specialize (IHl npl_prev).
    simpl in H_rgt.
    specialize (IHl (a0 (s_roots (p_roots pl) nrl_prev) (eq_ind_r (fun n : nat => n < length l) H_rgt (len_pres pl nrl_prev)))).
    (*
    specialize (IHl (lpt_ls_iter_inv pl nrl_prev l a H_rgt)).
    *)
    specialize (IHl npl nrl).
    specialize (IHl H_eq).
    specialize (IHl s).
    specialize (IHl H_in).
    (* now crunch both cases through H_iter_w *)
    (* recall iter_w l pl = nrl_prev, npl_prev. So should be able to use both invariance lemmas (again?) *)
    destruct IHl as [H_nrl_prev | H_npl_prev].
    (* case refutation *)
    (* iter_inv_rl_1
     : forall (l : list S) (pl : list proof) (nrl : list (sref (p_roots pl))) (npl : list proof),
       projT1 (iter_w l pl) = (nrl, npl) -> forall s : S, In s (s_roots (p_roots pl) nrl) -> In s l \/ In s (p_roots pl) *)
    apply (iter_inv_rl_1 l pl nrl_prev npl_prev).
    rewrite -> H_iter_w.
    simpl.
    reflexivity. assumption.
    (* iter_inv_rl_2
     : forall (l : list S) (pl : list proof) (nrl : list (sref (p_roots pl))) (npl : list proof),
       projT1 (iter_w l pl) = (nrl, npl) -> forall s : S, In s (p_roots npl) -> In s l \/ In s (p_roots pl) *)
    apply (iter_inv_rl_2 l pl nrl_prev npl_prev).
    rewrite -> H_iter_w.
    simpl.
    reflexivity. assumption.
  Qed.

  (* every sequent has either a proof or  shallow refutation *)
  Lemma iter_fp_inv_lr (Delta: list S) :
    let (pl, rl) := iter_fp Delta in forall (s:S),  In s Delta -> {In s (s_roots (p_roots pl) rl)} + {In s (p_roots pl)}.
  Proof.
    unfold iter_fp.
    destruct (iter_fp_acc Delta [] (lpt_ls_iter_wf Delta)) as (pl, rl) eqn:H_iter_fp_acc.
    intros s H_s_in_Delta.
    apply (iter_inv_lr  Delta [] (lpt_ls_iter_wf Delta) pl rl).
    rewrite -> H_iter_fp_acc. reflexivity.
    intuition.
  Qed.

  (* the other way around: we don't magically invent sequents *)
  Lemma iter_fp_inv_rl (Delta: list S) :
    let (pl, rl) := iter_fp Delta in forall (s:S), {In s (s_roots (p_roots pl) rl)} + {In s (p_roots pl)} -> In s Delta .
  Proof.
    unfold iter_fp.
    destruct (iter_fp_acc Delta [] (lpt_ls_iter_wf Delta)) as (pl, rl) eqn:H_iter_fp_acc.
    intros s H_s_in_res.
    (* invariance lemma gives disjunction that we eliminate later *)
    assert (H_d:  {In s Delta} + {In s (p_roots [])}).
    apply (iter_inv_rl Delta [] (lpt_ls_iter_wf Delta) pl rl).
    rewrite -> H_iter_fp_acc. reflexivity. assumption.
    destruct H_d as [H_Delta | H_emp].
    assumption. simpl in H_emp. inversion H_emp.
  Qed.

End Invariance.
