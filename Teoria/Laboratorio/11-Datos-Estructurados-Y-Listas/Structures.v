(* PAIRS - TUPLE *)
(*
In an Inductive type definition, each constructor can take any number of arguments -- none 
(as with true and O), one (as with S), or more than one (as with nybble, and here):
*)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(*
This declaration can be read: "The one and only way to construct a pair of numbers is by applying 
the constructor pair to two arguments of type nat."

It is nice to be able to write them with the standard mathematical notation (x,y) instead of pair x y.
We can tell Coq to allow this with a Notation declaration.
*)

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
  | (x, y) => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | (x, y) => y
  end.

Compute (fst (3,5)).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* CUIDADO CON ESTOS ERRORES *)
(* Can't match on a pair with multiple patterns: *)
(* *)
Definition bad_fst (p : natprod) : nat :=
  match p with
    | (x, y) => x
  end.

(* Can't match on multiple values with pair patterns: *)
(*
Definition bad_minus (n m : nat) : nat :=
  match n, m with
    | O   , _    => O
    | S _ , O    => n
    | S n', S m' => bad_minus n' m'
  end.*)

(*Proofs*)
Theorem surjective_pairing' : 
    forall (n m : nat),
    (n,m) = (fst (n,m), snd (n,m)).
Proof.
  simpl.
  reflexivity. 
Qed.

Theorem surjective_pairing_stuck : 
  forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.

Theorem surjective_pairing : 
  forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p. 
  simpl. reflexivity. 
Qed.

(** LIST **)
(*
 We can describe the type of lists of numbers like this: "A list is either the empty list or 
 else a pair of a number and another list."
*)
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(*
As with pairs, it is more convenient to write lists in familiar programming notation. The following 
declarations allow us to use :: as an infix cons operator and square brackets as an "outfix" 
notation for constructing lists.
*)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Check mylist3.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: _ => h
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

(*
It is again convenient to have an infix operator for it.
*)
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(* Proofs *)
(*
Simple facts about list-processing functions can sometimes be proved entirely by simplification.
*)
Theorem nil_app : 
  forall l : natlist,
  [] ++ l = l.
Proof.
simpl.
reflexivity. Qed.

(*
It is sometimes helpful to perform case analysis on the possible shapes (empty or non-empty) of 
an unknown list.
*)
Theorem tl_length_pred : 
  forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. 
  destruct l as [| n l'].
  - (* l = nil *)
    simpl.
    reflexivity.
  - (* l = cons n l' *)
    simpl.
    reflexivity. 
Qed.

(*
A list is either nil or else it is cons applied to some number and some smaller list; etc. So, 
if we have in mind some proposition P that mentions a list l and we want to argue that P holds for 
all lists, we can reason as follows:

- First, show that P is true of l when l is nil.
- Then show that P is true of l when l is cons n l' for some number n and some smaller list l', 
  assuming that P is true for l'.
*)

Theorem app_assoc : 
  forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. 
  induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl.
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite IHl1'. reflexivity. 
Qed.

(** OPTIONS **)
(*
Suppose we want to write a function that returns the nth element of some list. If we give it type 
nat → natlist → nat, then we'll have to choose some number to return when the list is too short...
*)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l,n with
  | nil, _ => 42
  | (a :: l'), 0 => a
  | (a :: l'), (S n') => nth_bad l' n'
  end.

(*
This solution is not so good: If nth_bad returns 42, we can't tell whether that value actually appears 
on the input without further processing. A better alternative is to change the return type of nth_bad 
to include an error value as a possible outcome. We call this type natoption.
*)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth (l:natlist) (n:nat) : natoption :=
  match l,n with
  | nil, _ => None
  | (a :: l'), 0 => Some a
  | (a :: l'), (S n') => nth l' n'
  end.

Compute (nth [0;1;2;3;4] 3).

(** PARTIAL MAPS **)
(*
As a final illustration of how data structures can be defined in Coq, here is a simple partial 
map data type, analogous to the map or dictionary data structures found in most programming languages
*)

Inductive id : Type :=
  | Id (n : nat).

Inductive bool : Type :=
  | true
  | false.

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S m' => false
  | S n', O  => false
  | S n', S m' => eqb n' m'
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.


Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_nat_refl:
 forall x : nat,
 eqb x x = true.
Proof.
intros.
induction x.
- simpl. reflexivity.
- simpl. rewrite IHx. reflexivity.
Qed.

Theorem eqb_id_refl : 
 forall x, 
 eqb_id x x = true.
Proof.
intros. destruct x. simpl. apply eqb_nat_refl. 
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

(*
This declaration can be read: "There are two ways to construct a partial_map: either using the 
constructor empty to represent an empty partial map, or applying the constructor record to a key, 
a value, and an existing partial_map to construct a partial_map with an additional key-to-value 
mapping."
*)

(*
The update function overrides the entry for a given key in a partial map by shadowing it with 
a new one (or simply adds a new entry if the given key is not already present).
*)
Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(*
Last, the find function searches a partial_map for a given key. It returns None if the key was not 
found and Some val if the key was associated with val. If the same key is mapped to multiple values, 
find will return the first one it encounters.
*)
Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
  find x (update d x v) = Some v.
Proof.
intros.
simpl.
rewrite eqb_id_refl.
reflexivity.
Qed.