(** SORT -- INSERTION SORT **)

(*
Sorting can be done in expected O(N log N) time by various algorithms 
(quicksort, mergesort, heapsort, etc.). But for smallish inputs, a simple 
quadratic-time algorithm such as insertion sort can actually be faster. It's 
certainly easier to implement -- and to verify.
*)

Require Import Bool.
Require Import Nat.
Require Import List.
Require Import Permutation.
Require Import Coq.Arith.Compare_dec.
Require Import List Lia Arith Permutation.
Import ListNotations.


(* insert i l inserts i into its sorted place in list l.
   Precondition: l is sorted. *)
Fixpoint insert (a : nat) (l : list nat) : list nat :=
    match l with
    | [] => [a]
    | b::bs => if (a <=? b) then a::l
               else b::(insert a bs)
    end.

  Fixpoint sort (l : list nat) : list nat :=
    match l with
    | [] => []
    | b :: bs => insert b (sort bs)
    end.

Example sort_pi :
  sort [3;1;4;1;5;9;2;6;5;3;5]
  = [1;1;2;3;3;4;5;5;5;6;9].
Proof. simpl. reflexivity. Qed.

Compute insert 7 [1; 3; 4; 8; 12; 14; 18].


(*
For any two elements of the list (regardless of whether they are adjacent), 
they should be in the proper order. Let's try formalizing that.

We can think in terms of indices into a list lst, and say: for any valid indices i and j, 
if i < j then index lst i ≤ index lst j, where index lst n means the element of lst at 
index n.

Check nth : ∀ A : Type, nat → list A → A → A.
Check nth_error : ∀ A : Type, list A → nat → option A.

*)

Definition sorted'' (al : list nat) := 
    forall i j,
    i < j < length al ->
    nth i al 0 <= nth j al 0.

Definition sorted' (al : list nat) := 
    forall i j iv jv,
    i < j ->
    nth_error al i = Some iv ->
    nth_error al j = Some jv ->
    iv <= jv.

Lemma sort'_correct :
    forall l,
    sorted' (sort l) .
Proof.
Abort.

(*
A sorting algorithm must rearrange the elements into a list that is totally 
ordered. There are many ways we might express that idea formally in Coq. 
One is with an inductively-defined relation that says:
- The empty list is sorted.
- Any single-element list is sorted.
- For any two adjacent elements, they must be in the proper order.
*)
(*
match l with
 [] => True
 [_] =>True..
*)
Inductive sorted : list nat -> Prop :=
  | nil_sorted : sorted []
  | singleton_sorted : forall a, sorted [a]
  | pair_sorted : forall a b l, a <= b -> sorted (b::l) -> sorted (a::b::l).

Hint Constructors sorted.

(*
Using sorted, we specify what it means to be a correct sorting algorthm:
Function f is a correct sorting algorithm if f al is sorted and is a permutation 
of its input.
*)
Definition is_a_sorting_algorithm (f: list nat -> list nat) := 
    forall al,
    Permutation al (f al) /\ sorted (f al).

Hint Resolve Nat.lt_le_incl.

(* 
Prove that insertion maintains sortedness.
*)
Lemma insert_sorted:
    forall a l, 
    sorted l -> sorted (insert a l).
Proof.
    intros a l srtd_l. induction srtd_l. 
      -simpl. apply singleton_sorted.
      -simpl. destruct (Nat.leb_spec a a0).
        * simpl. constructor. auto. apply singleton_sorted.
        * simpl. constructor. auto. apply singleton_sorted.
      -simpl. destruct (Nat.leb_spec a a0). 
        * auto.
        * revert IHsrtd_l.
          unfold insert.
          destruct (Nat.leb_spec a b). 
            +simpl. auto. 
            +simpl. auto.
Qed.

Theorem sort_sorted: 
    forall l, sorted (sort l).
Proof.
  intros.
  induction l.
  -(*[]*)
  simpl. apply nil_sorted.
  -(*a::l*)
  simpl. apply insert_sorted. trivial.
Qed.

Lemma insert_perm: 
    forall x l,
    Permutation (x :: l) (insert x l).
Proof.
intros x l.
induction l.
  - simpl. trivial.
  - simpl. destruct (Nat.leb_spec x a).
    * trivial.
    * rewrite perm_swap. auto.
Qed.

Theorem sort_perm:  
  forall l, Permutation l (sort l).
Proof.
intro l.
induction l.
  - simpl. apply perm_nil.
    (* EJERCICIO EXTRA 2 PUNTOS, TERMINAR DEMOSTRACION *)
  - Admitted.


Theorem insertion_sort_correct:
    forall al,
    Permutation al (sort al) /\ sorted (sort al).
Proof.
intro.
split.
  - apply sort_perm.
  - apply sort_sorted.
Qed. 





