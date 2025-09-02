(**************************************************************************************************************)
(*                                                                                                            *)
(*                                                                                                            *)
(*                                                                                                            *)
(**************************************************************************************************************)

Require Import List.
Import ListNotations.


(* a functional list consists of a list l, and a function f: forall x, In x l -> B *)
(* head and tail operations for functional lists *)
(* tech: or_introl and or_intror can be used as reductions are automatic, could use in_eq and in_cons *)
Definition fl_hd {A B: Type} (a: A)(l: list A)(f: forall x, In x (a::l) -> B) : B :=
  f a (or_introl eq_refl).

Definition fl_tl {A B: Type} (a: A)(l: list A)(f: forall x, In x (a::l) -> B) : forall x, In x l -> B :=
  fun x w => f x (or_intror w).

(* conversion between functional lists to lists *)
Fixpoint map_in {A B: Type} (l: list A) : (forall a, In a l -> B) -> list B :=
  match l with
  | [] => (fun _ => [])
  | (x::xs) => fun f => (fl_hd x xs f)::(map_in xs (fl_tl x xs f) )
end.

(* equivalent definition with match .. return and list lemmas and differnt profile *)
Fixpoint map_in' {A B: Type} (l: list A)(f: forall a, In a l -> B): list B :=
  match l return ((forall a, In a l -> B) -> list B)  with
  | [] => fun (f: forall a, In a [] -> B) => []
  | (hd::tl)  => fun f => (f hd (in_eq hd tl))::(map_in' tl (fun a => fun f' => f a (in_cons hd a tl f')))
  end f.

(* every element in the range of map_in comes from an element on the left *)
Lemma in_map_in {A B: Type}(l: list A)(f: forall a, In a l -> B)(b: B):
  In b (map_in l f) -> exists (a:A)(w: In a l), f a w = b.
Proof.
  generalize dependent l; intro l.
  induction l as [| x xs IHxs].
  (* l = [] is impossible *)
  intros f H_in. inversion H_in.
  (* l = x::xs *)
  intros f H_in.
  simpl in H_in.
  destruct H_in as [H_in_x | H_in_xs].
  (* f x = b *)
  exists x.
  simpl.
  exists (or_introl eq_refl).
  assumption.
  (* case b in map xs *)
  simpl.
  destruct (IHxs (fl_tl x xs f) H_in_xs) as [a [w H_w]].
  exists a.
  unfold fl_tl in H_w; simpl in H_w.
  exists (or_intror w).
  assumption.
Qed.

(* We use sumbool, rather than sum, to express decidability at type level as sumbool has better support in the Coq library *)
Definition sumbool_dec (A: Type) : Type := forall (x y: A), {x = y} + {x <> y}.

(* list membership is sumbool-decidable for sumbool-decidable types *)
Lemma In_dec_dec {A: Type}: sumbool_dec A -> forall (a:A) (l: list A), {In a l} + {~ (In a l)}.
Proof.
  (* we could base this on the decidability of In in the library together with decidability of A. We give a direct proof. *)
  intros Hdec a l; induction l as [| fst rst IHrst].
  (* l = [] *)
  right; unfold In; simpl; intuition.
  (* l = fst::rst *)
  destruct (Hdec a fst) as [H_a_eq_fst | H_a_neq_fst].
  (* case a = fst *)
  left; simpl; intuition.
  (* case a <> fst *)
  destruct IHrst as [H_a_in_rst | H_a_notin_rst].
  (* case a in rst *)
  left; simpl; intuition.
  (* case a not in rst *)
  right; simpl; intuition.
Defined.


(* inversion of in is sumbool decidable for sumbool decidable types *) 
Lemma in_inv_dec {A: Type}: sumbool_dec A -> forall (a b:A) (l: list A), In b (a::l) -> {a = b} + {In b l}. 
Proof. 
  (* again, we could use the proof of in-inversion but a direct proof will be faster *) 
  intros Hdec a b l Hin. 
  destruct l as [| fst rst]. 
  (* case l = [] *) 
  left. 
  simpl in Hin; intuition. 
  (* case l = fst::rst *) 
  destruct (Hdec a b) as [H_a_eq_b | H_a_neq_b]. 
  (* if a = b we are done *) 
  left; assumption. 
  (* if a <> b we know that b in rst *) 
  right. 
  simpl in Hin; simpl; intuition. 
Defined.

(* decidable version of in_app_or *)
Lemma in_app_sumbool {A: Type}: sumbool_dec A -> forall (a:A)(l1 l2: list A), In a (l1 ++ l2) -> {In a l1} + {In a l2}.
Proof.
  intros H_dec a l1. induction l1 as [| hd tl IHtl].
  (* l1 = [] *)
  intros l2 H_in; simpl in H_in.
  intuition.
  (* l1 = hd::tl *)
  intros l2 H_in.
  assert  (H_in': In a  (hd::(tl ++ l2))).
  simpl; simpl in H_in; assumption.
  destruct (in_inv_dec H_dec hd a (tl ++ l2) H_in') as [H_hd | H_tl].
  left. simpl. intuition.
  destruct (IHtl l2 H_tl) as [H_in_tl | H_in_l2].
  left.
  simpl; intuition.
  right; assumption.
Defined.

(* decidable version of in_sumbool_or where decidability is not needed *)
Lemma in_sumbool_app {A: Type}: forall (a:A)(l1 l2: list A), {In a l1} + {In a l2} -> In a (l1 ++ l2).
Proof.
  intros a l1 l2 H_sum.
  apply in_or_app.
  intuition.
Qed.
