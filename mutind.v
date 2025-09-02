(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List. Import ListNotations.
Require Import bipartite lemmas mutcoind.

Section MutInd. 

  (* mutually inductive proof trees *)

  Open Scope type_scope.
  
  (* a witnessed provable sequent has an applicable rule that is witnessed proving *)
  (* a witnessed proving rule has a witnessed provable sequent for all its premisses  *)
  (* tech: built in and auto generated induction / recurision schemes don't seem to work well with type dependencies. *)
  (* e.g. Scheme ... with ... . Use Fixpoint .. with .. or Lemma ... with ... instead. *)
  Inductive wp_seq: S ->  Type :=
  | one_r : let rules := fst B in forall (s:S), { r:R & In r (rules s) *  wp_rule r} -> wp_seq s
  with wp_rule: R -> Type :=
  | all_s: let prems := snd B in forall (r:R), (forall s:S, In s (prems r) ->  wp_seq s) -> wp_rule r.

  (* convenience notation *)
  Definition proof: Type  := { s:S & wp_seq s}.
  Definition p_root  (p: proof) : S := (projT1 p).
  Definition p_roots (l: list proof) : list S := map p_root l.

  (* a witnessed shallow refutable sequent s has evidence that s cannot be proved in one step from assumptions in l *)
  Definition wsr_seq (l: list S)(s:S)  := forall (r:R), In r (fst B  s) -> { s':S &  In s' (snd B r) /\ ~ (In s' l)}.
  Definition sref (l: list S) := { s & wsr_seq l s }.
  Definition s_root (l: list S)(r: sref l) := projT1 r.
  Definition s_roots (l: list S)(rs: list (sref l)) := map (s_root l) rs.

  (* find a proof with given conclusion *)
  Lemma find_wp_seq (l: list proof)(s:S) : (wp_seq s) + (~(In s (p_roots l))).
  Proof.
    induction l as [|p ps IHps].
    (* l = [] *)
    right; simpl; intuition.
    (* l = p::ps *)
    destruct (S_dec s (p_root p)) as [H_s_eq_root_p | H_s_neq_root_p].
    (* case s = root p: we have a proof *)
    left. unfold proof in p. destruct p as [p_root p_proof].
    simpl in H_s_eq_root_p.
    rewrite -> H_s_eq_root_p.
    apply p_proof.
    (* case s <> root p. We may still have a proof in ps *)
    destruct IHps as [H_proof_in_ps | H_s_not_in_roots_ps].
    (* we have a proof in ps. That's it *)
    left; assumption.
    (* we don't have a proof in ps so cactus *)
    right.
    intro Hin. simpl in Hin.
    destruct Hin as [H_root_p_eq_s | H_s_in_roots_ps].
    symmetry in H_root_p_eq_s; intuition.
    intuition.
  Defined.

 
  (* second way to implement the lemma in programming style with lemmas giving propositional evidence *)
  (* lemma for base case  *)
  Lemma fws_ev_empty: forall (s:S), (~(In s (p_roots []))).
  Proof.
    intros s H_c; unfold p_roots in H_c; unfold map in H_c; inversion H_c.
  Qed.

  (* lemma for step case *)
  Lemma fws_ev_cons (s:S)(p0: proof)(ps: list proof):
      p_root p0 <> s -> ~ (In s (p_roots ps)) -> ~ (In s (p_roots (p0::ps))).
  Proof.
    intros N_p0 N_ps H_c.
    simpl in H_c.
    destruct H_c as [H_p0 | H_ps].
    apply (N_p0 H_p0).
    apply (N_ps H_ps).
  Defined.
  
  (* fixpoint definition using propositional evidence above *)
  Fixpoint find_wp_seq_fix (l: list proof)(s:S) : (wp_seq s) + (~(In s (p_roots l))) :=
    match l with
    | [] => inr (fws_ev_empty s)
    | p0::ps => match S_dec (p_root p0) s with
                | left  E_p0 => inl (eq_rect (projT1 p0) (fun s => wp_seq s) (projT2 p0) s E_p0 )
                | right N_p0 => match find_wp_seq_fix ps s with
                                | inl p => inl (p)
                                | inr N_ps => inr (fws_ev_cons s p0 ps N_p0 N_ps)
                                end
                end
    end.
  (* compare proof terms and how they extract, like so: *)
  (* End Mutind.
    Print find_wp_seq.
    Print find_wp_seq_fix.
    From Coq Require Extraction.
    Extraction Language Haskell.
    Extraction find_wp_seq.
    Extraction find_wp_seq_fix.
  *)
                               
  (* we either have a proof tree for all seqs,  or there is an element in seqs for which we don't *)
  Lemma all_seqs_wp_dec (seqs: list S)(assns: list proof) :
    (forall (s':S), In s' seqs  -> wp_seq s') + { s:S & In s seqs /\ ~ (In s (p_roots assns)) } .
  Proof.
    induction seqs as [| p ps IHps].
    (* prems = [] *)
    left; intros s Hin; inversion Hin.
    (* prems = p::ps *)
     destruct (find_wp_seq assns p) as [H_p_has_proof | H_p_has_nonprovable_prem].
    (* case p has a proof in the list of assumptions *)
    destruct IHps as [H_all_ps_have_proofs | H_one_ps_doesnt_have_proof].
    (* case all elts of ps also have proofs *)
    left; intros s Hin. 
    destruct (in_inv_dec S_dec p s ps Hin) as [H_s_eq_p | H_s_in_ps].
    (* case p = s *)
    rewrite <- H_s_eq_p; apply H_p_has_proof.
    (* case s in ps *)
    specialize (H_all_ps_have_proofs s H_s_in_ps).
    apply H_all_ps_have_proofs.
    (* case one premiss doesn't have a proof *)
    right.
    destruct H_one_ps_doesnt_have_proof as [s [H_s_in_ps H_s_notin_roots]].
    exists s; split.
    simpl; intuition.
    assumption.
    (* case p has a non-provable premiss *)
    right; exists p; split.
    simpl; intuition.
    assumption.
  Defined.

  (* a rule is either witnessed proving, or we can find a premiss for which we're not given a proof *)
  Lemma wp_rule_dec (r: R)(assns: list proof) : let prems := snd B in 
    (wp_rule r) + { s:S &  In s (prems r) /\ ~ (In s (p_roots assns)) }.
  Proof.
    remember (snd B) as prems eqn:H_snd_B_eq_prems; simpl.
    destruct (all_seqs_wp_dec (prems r) assns) as [H_all_prems_provable | H_one_prem_not_provable].
    (* all premisses of r are provable: we have a witnessed proving  rule *)
    left.
    apply all_s.
    rewrite <- H_snd_B_eq_prems. assumption.
    right. assumption.
  Defined.

  (* a list of rules either contains a witnessed proving rule, or each element contains one unprovable premiss *)
  Lemma exists_wp_rule_dec (rules: list R) (assns: list proof) : let prems := snd B in
    { r: R & In r rules * wp_rule r }  + (forall (r:R), In r rules -> { s:S & In s (prems r) /\ ~ (In s (p_roots assns))}).
  Proof.
    remember (snd B) as prems eqn:H_snd_B_eq_prems.
    simpl.
    induction rules as [| r rs IHrs].
    (* rules = [] *)
    right.
    intros r Hin; inversion Hin.
    (* rules = (r::rs) *)
    (* check whether r is witnessed proving *)
    destruct (wp_rule_dec r assns) as [H_r_wp | H_r_not_wp].
    (* if r is universal, we are home *)
    left. exists r. split.
    simpl; intuition; assumption.
    assumption.
    (* if r is not witnessed proving, there may be a witnessed proving  rule in the tail rs *)
    destruct IHrs as [H_wp_rule_in_rs | H_no_wp_rule_in_rs].
    (* have witnessed proving  rule in rs *)
    left.
    destruct H_wp_rule_in_rs as [r0 [H_r0_in_rs H_r0_wp]].
    exists r0.
    split.
    simpl. right; assumption. assumption.
    (* no witnessed proving rule in rs: we hope we have enough negative information *)
    right.
    intros r0 H_r0_in_r_rs.
    destruct (in_inv_dec R_dec r r0 rs H_r0_in_r_rs) as [H_r_eq_r0 | H_r0_in_rs].
    rewrite <- H_snd_B_eq_prems in H_r_not_wp.
    rewrite <- H_r_eq_r0.
    assumption.
    specialize (H_no_wp_rule_in_rs r0 H_r0_in_rs).
    assumption.
  Defined.

  (* a sequent is either witnessed provable from assumptions, or witnessed shallow refutable *)
  Lemma wp_seq_dec (s: S) (assns: list proof):
     (wp_seq s) + (forall (r:R), In r (fst B  s) -> { s':S &  In s' (snd B r) /\ ~ (In s' (p_roots assns))}).
  Proof.
    destruct B as [rules prems] eqn:E_B. 
    destruct (exists_wp_rule_dec (rules s) assns) as [H_have_wp_rule | H_no_wp_rule].
    (* have witnessed proving rule to construct witnessed provable sequent *)
    left.
    apply one_r.
    replace (fst B s) with (rules s).
    assumption. rewrite -> E_B.  simpl.  reflexivity. 
    (* we don't have a witnessed proving  rule but enough negative information *)
    right.
    intro r; specialize (H_no_wp_rule r); replace (snd B r) with (prems r) in H_no_wp_rule.
    assumption.
    rewrite -> E_B; reflexivity.
  Defined.

   (* reformulation of above using shallow refutations *)
  Lemma wp_seq_dec3 (s: S) (assns: list proof):
    (wp_seq s) + (wsr_seq (p_roots assns) s).
  Proof.
    destruct (wp_seq_dec s assns) as [L|R].
    left; assumption.
    right; unfold wsr_seq; assumption.
  Qed.

 
  (* eos stands for equal or shorter and is used to control termination of fixpoint operation *)
  Definition eos {A B C: Type} (lp nlp: list A)(lr: list B)(nlr: list C) :=
    {lp = nlp /\ length lr = length nlr} +  {length nlr  < length lr}.

  (* termination case needs equality in first component *)
  Definition eos_nil {A B C: Type}(lp: list A) : eos lp lp ([]: list B)([]: list C) := left (conj eq_refl eq_refl).

  (* recursive case needs decrease in second component *)
  Lemma eos_cons_pf {A B C: Type}(lp nlp: list A)(r:B)(lr: list B)(nlr: list C)(p:A):
    eos lp nlp lr nlr -> eos lp (p::nlp) (r::lr) nlr.
  Proof.
    intro H_eos.
    destruct H_eos as [H_eq | H_shorter].
    right.
    simpl.
    destruct H_eq as [H_lp_nlp H_lr_nlr].
    rewrite -> H_lr_nlr.
    auto.
    simpl.
    right.
    simpl.
    auto.
  Qed.

  (* same for other recursive call *)
  Lemma eos_cons_ref {A B C: Type}(lp nlp: list A)(r:B)(lr: list B)(nlr: list C)(nr: C):
    eos lp nlp lr nlr -> eos lp nlp (r::lr) (nr::nlr).
  Proof.
    intro H_eos. destruct H_eos as [H_eq | H_shorter].
    left.
    destruct H_eq as [H_lp_nlp H_lr_nlr].
    split.
    assumption.
    simpl.
    auto.
    right.
    simpl.
    auto.
    assert (H_mon: forall (n:nat) (m:nat), n < m -> Datatypes.S n < Datatypes.S m).
    apply  PeanoNat.Nat.succ_lt_mono.
    apply H_mon.
    assumption.
  Qed.

  (* witnessed version of one step of fixpoint iteration *)
  Fixpoint iter_w (l: list S)(pl: list proof): {n: list (sref (p_roots pl)) * (list proof) & eos pl (snd n) l (fst n)}  :=
    match l (* return { n: list (sref (p_roots pl)) * (list proof) & let (nrl, npl) := n in  eos pl npl l nrl} *) with
    | [] => existT _ ([],  pl)(eos_nil pl)
    | s0::ss => match iter_w ss pl with existT _ (nrl, npl) prev => match wp_seq_dec3 s0 pl  with
      | inl np => existT _ (nrl, (existT _ s0 np)::npl)(eos_cons_pf  pl npl s0 ss nrl (existT _ s0 np) prev)
      | inr sr => existT _ ((existT _ s0 sr)::nrl, npl)(eos_cons_ref pl npl s0 ss nrl (existT _ s0 sr) prev)
      end end
    end.

  (* note the change of the order of arguments owing to the sigma type in the codomain. make consistent above? *)
  (* compute a fixpoint of iter_w, i.e. have proofs or self-referential shallow refutations *)
  (* tech: eq_rect uses equality of old and new proofs to subst type in shallow refutations *)
  (* eq_rect:  forall (A : Type) (x : A) (P : A -> Type), P x -> forall y : A, x = y -> P y *)

  (* working towards computing the entire fixpoint iteration *)
  (* auxilary lemmas to control recursion and to establish correctness assertions *)

  Lemma len_pres (pl: list proof)(nl: list (sref (p_roots pl))) : length (s_roots (p_roots pl) nl) = length nl.
  Proof.
    unfold s_roots.
    apply length_map.
  Qed. 

  (* need well founded relation that witnesses recursion pattern to show totality *)
  Definition lpt_ls_iter  (nl l: list S) := length nl < length l.

  (* in recursive calls, get shallow refutation list shorter than sequent list, hence additional gymnastics here *)
  Definition lpt_ls_iter_inv pl nl l a (H_l: length nl < length l): Acc lpt_ls_iter (s_roots (p_roots pl) nl) :=
    match a with
    | Acc_intro _ H => H (s_roots (p_roots pl) nl) (eq_ind_r (fun n : nat => n < length l) H_l (len_pres pl nl))
    end .

  (* proj1 is declared opaque in the standard library. we need a transparent version to reduce *)
  Definition proj1' {A B: Prop} (H: A /\ B) : A := match H with conj H0 _ => H0 end.
               
                                                
  (* fixpoint of iteration reached when no new shallow refutations (or proofs) are found *)
  (* know this as last comp of result of iter_w carries precisely this inforation *)
  Fixpoint iter_fp_acc (l: list S)(pl: list proof)(a: Acc lpt_ls_iter l) : { npl: list proof & list (sref (p_roots npl)) } :=
    match iter_w l pl with
    | existT _ (nrl, npl) (left  H_eq) => existT _ npl (eq_rect pl (fun x => list (sref (p_roots x))) nrl npl (proj1' H_eq))
    | existT _ (nrl, npl) (right H_lt) => iter_fp_acc (s_roots (p_roots pl) nrl) npl (lpt_ls_iter_inv pl nrl l a H_lt)
    end.

  (* well_foundedness of lpt_ls_iter, prove by well founded induction on nat *)
  Lemma lpt_ls_iter_wf_aux: forall n, forall l,  (length l = n) -> Acc lpt_ls_iter l.
  Proof.
    intro n.
    induction n as [n IHn] using (well_founded_induction PeanoNat.Nat.lt_wf_0).
    intros l H_l_len.
    apply Acc_intro.
    intros l' H_l'_shorter.
    specialize (IHn (length l')).
    refine (IHn _ l' eq_refl).
    unfold lpt_ls_iter in H_l'_shorter.
    subst n.
    assumption.
  Qed.

  Lemma lpt_ls_iter_wf : well_founded lpt_ls_iter.
  Proof.
    unfold well_founded.
    intro l.
    apply( lpt_ls_iter_wf_aux (length l) l eq_refl).
  Qed.

  (* first main theorem: ever list Delta can be ``split'' into  a list of proofs and a list of shallow refutations *)
  Definition iter_fp (Delta: list S) : { pl: list proof & list (sref (p_roots pl)) } :=
    iter_fp_acc Delta []  (lpt_ls_iter_wf Delta).

End MutInd.
