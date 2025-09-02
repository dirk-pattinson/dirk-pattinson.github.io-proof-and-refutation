(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)



  Section Bipartite.
 (* basic common notions and data structures *)

  Open Scope type_scope.

  Parameter S: Type. (* Sequents *)
  Parameter R: Type. (* Rule Instances *)
  Parameter S_dec: forall (s s': S), {s = s'} + {s <> s'}.
  Parameter R_dec: forall (r r': R), {r = r'} + {r <> r'}.

  (* Effective Bipratite Graphs with edges given as lists *)
  (* For every sequent, the list of rules that prove the sequent, and for every rule, the list of premisses *)

  
  Definition EBG := (S -> list R) * (R -> list S).

  Parameter B: EBG.

End Bipartite.
