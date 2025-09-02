(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List. Import ListNotations.

Require Import bipartite mutind ptree ptree_wf.

Section Pforest.

  (** data structure into which proofs are going to be extracted *)

  (* proof forrests: the data structure into which we will ultimately extract *)
  Inductive pforest: list S -> Type :=
    | pf_emp : pforest  []
    | pf_plant: forall (s: S)(prems: list S)(prem_proofs: pforest prems)(ss: list S)(f: pforest ss), pforest (s::ss).
  
  (* translation from ptree lists to forests using well founded recursion *)
  Fixpoint lpt_to_for_aux (l: list ptree)(w: Acc lpt_cut_lft l) : pforest (map pt_root l) :=
    match l return Acc lpt_cut_lft l -> pforest (map pt_root l) with
    | []       => fun _ => pf_emp
    | (p0::ps) => fun w => let ns := pt_nodes p0 in
                           pf_plant (pt_root p0)(map pt_root ns)(lpt_to_for_aux ns (lpt_cut_lft_inv_lft p0 ps w))
                                                (map pt_root ps)(lpt_to_for_aux ps (lpt_cut_lft_inv_cut p0 ps w))
    end w.

  Definition lpt_to_for (l: list ptree): pforest (map pt_root l) := lpt_to_for_aux l (lpt_cut_lft_wf l).

  (* well formed proof forests *)
  Inductive pfor_wellformed : forall (l: list S), pforest l -> Prop := 
  | pf_emp_wf : pfor_wellformed [] pf_emp
  | pf_plant_wf : forall (s: S)(prems: list S)(prem_proofs: pforest prems)(ss: list S)(f: pforest ss),
      (exists (r:R), In r (fst B s) /\ forall (s':S), In s' (snd B r) -> In s' prems) ->
      pfor_wellformed ss f -> pfor_wellformed prems prem_proofs ->  
      pfor_wellformed (s::ss) (pf_plant s prems prem_proofs ss f).

  (* Missing: proof of preservaton of well formedness *)
  (* incomplete here ...
  Lemma lpt_to_for_aux_wf: forall (l: list ptree)(w: Acc lpt_cut_lft l) ...
  *)
  
  
  
End Pforest.
