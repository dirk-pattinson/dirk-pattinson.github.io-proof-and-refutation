(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List. Import ListNotations.

Require Import bipartite lemmas mutcoind rtree.

Section Rforest.

  (** coinductive forests and their translations *)

  Open Scope type_scope.

  (* refutation forests that we are ultimately translating into *)
  CoInductive rforest: list S -> Type :=
  | rf_emp : rforest []
  | rf_plant : forall (s: S)(prems: list S)(prem_proofs: rforest prems)(ss: list S)(f: rforest ss), rforest (s::ss).

  (* mapping of refutation trees to refutation forests *)
  CoFixpoint lrt_to_rforest: forall (l: list rtree), rforest (map rt_root l) :=
    fun l => match l return rforest  (map rt_root l) with
    | [] => rf_emp
    | (rt_grow s l f)::rts => let prems := map_in l f in let roots := map rt_root in
        rf_plant s (roots prems)(lrt_to_rforest prems)(roots rts)(lrt_to_rforest rts)
   end.
  
  (* missing: well formed ref forests and proof of preservation of well formedness of translation *)

End Rforest.
