(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List. Import ListNotations.
Require Import bipartite lemmas mutind mutcoind inv.

Section PfRef. 

  (* for closed sets, every sequent has either a proof or a refutation *)
  
  (* closed sets of sequents are closed under backward application of proof rules *)
  Definition closed (Delta: list S) := forall s r s', In s Delta -> In r (fst B s) -> In s' (snd B r) -> In s' Delta.

  (* elements of shallow refutalbe sequent lists are shallow refutable *)
  Lemma wsr_sref: forall   (lp: list S)(lr: list (sref lp))(s:S), In s (s_roots lp lr) -> wsr_seq lp s.
  Proof.
    intros lp lr. induction lr as [| r0 rs IHrs].
    (* base case *)
    intros s H_in.
    simpl in H_in.
    inversion H_in.
    (* step case *)
    intros s H_in.
    change (s_roots lp (r0::rs)) with ((s_root lp r0)::(s_roots lp rs)) in H_in.
    destruct (in_inv_dec S_dec (s_root lp r0) s (s_roots lp rs) H_in) as [H_hd | H_tl].
    unfold sref in r0.
    unfold s_root in H_hd.
    destruct r0 as [ s0 H_wsr].
    simpl in H_hd.
    subst s0.
    assumption.
    (* step case *)
    apply IHrs.
    assumption.
  Qed.

  (* for closed sets, shallow refutable sequents are refutable *)
  Lemma wsr_closed: forall (lp: list S)(lr: list (sref lp)), closed (s_roots lp lr ++ lp) ->
                                                             forall (s:S), In s (s_roots lp lr) -> wr_seq s.
  Proof.
    intros lp lr H_closed.
    cofix H_ci.
    intros s H_in.
    apply all_r.
    intros r H_r_applicable.
    apply one_s.
    (* need to tease out unprovabe sequent from H_in ... *)
    assert (H_s_wsr: wsr_seq lp s).
    apply (wsr_sref lp lr s H_in).
    unfold wsr_seq in H_s_wsr.
    destruct  (H_s_wsr r H_r_applicable) as [s' H_s'_r].
    exists s'.
    split.
    intuition.
    assert (H_loop:  In s' (s_roots lp lr ++ lp)).
    (* try and massage H_closed *)
    unfold closed in H_closed.
    specialize (H_closed s r s').
    apply H_closed.
    apply in_or_app. intuition.
    assumption.
    intuition.
    apply (H_ci s').
    apply in_app_or in H_loop.
    destruct H_loop as [H_lp | H_lr].
    assumption.
    intuition.
  Qed.

  (* using invariance lemmas, fixpoint iteration preserves closedness *)
  Lemma iter_fp_closed (Delta: list S): let (pl, rl) := iter_fp Delta in
                                        closed Delta -> closed  ((s_roots (p_roots pl) rl) ++ (p_roots pl)).
  Proof.
    destruct (iter_fp Delta) as [ pl rl ] eqn:H_iter_fp.
    intro H_Delta_closed.
    unfold closed.
    intros s r s' H_in.
    (* apply in_app_or in H_in. *)
    intros H_r_app H_s'_prem.
    assert (H_s_in_Delta: In s Delta).
    pose (H_inv_rl := iter_fp_inv_rl Delta).
    rewrite -> H_iter_fp in H_inv_rl.
    apply H_inv_rl.
    apply (in_app_sumbool S_dec s (s_roots (p_roots pl) rl) ( p_roots pl) H_in).
    (* now use that Delta is closed *)
    unfold closed in H_Delta_closed.
    specialize (H_Delta_closed s r s' H_s_in_Delta H_r_app H_s'_prem).
    pose (H_inv_lr := iter_fp_inv_lr Delta).
    rewrite -> H_iter_fp in H_inv_lr.
    specialize (H_inv_lr s' H_Delta_closed).
    apply in_sumbool_app.
    assumption.
  Qed.

  (* an element of a list of proofs is indeed provable *)
  Lemma plist_pf: forall (s: S)(lp: list proof), In s (p_roots lp) -> wp_seq s.
  Proof.
    intros s lp; induction lp as [| p0 ps IHps].
    intro H_in; simpl in H_in; inversion H_in.
    intro H_in.
    assert (H_in' : In s ((p_root p0)::(p_roots ps))).
    simpl; simpl in H_in; assumption.
    destruct (in_inv_dec S_dec  (p_root p0) s (p_roots ps) H_in') as [H_p0 | H_ps].
    unfold proof in p0.
    destruct p0 as [s0 H_pf].
    simpl in H_p0.
    rewrite <- H_p0; assumption.
    intuition.
  Qed.
   
  (* second main theorem: every sequent has a proof or a refutation *)
  Theorem proof_ref (Delta: list S): closed Delta -> forall (s:S), In s Delta -> (wr_seq s) + (wp_seq s).
  Proof.
    destruct (iter_fp Delta) as [ lp lr ] eqn:H_iter_fp.
    intros H_closed s H_in.
    pose (H_inv := iter_fp_inv_lr Delta).
    rewrite -> H_iter_fp in H_inv.
    specialize (H_inv s H_in).
    (* case refutation *)
    destruct H_inv as [H_ref | H_pf].
    left.
    apply  (wsr_closed (p_roots lp) lr).
    pose (H_cl := iter_fp_closed Delta).
    rewrite -> H_iter_fp in H_cl.
    specialize (H_cl H_closed).
    assumption.
    assumption.
    (* case proof *)
    right.
    apply (plist_pf s lp H_pf).
  Qed.

End PfRef.
