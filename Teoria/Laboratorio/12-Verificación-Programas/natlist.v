Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

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

Fixpoint ntl (n: nat) (l:natlist) : natlist :=
  match n with
    | 0 => l
    | (S m) => ntl m (tl l)
  end.

Lemma tl_ntl : 
  forall (n:nat) (l: natlist) ,
  tl (ntl n l) = ntl (S n) l.
(*
Prueba error dummie
Proof.
intros n l.
induction n.
-simpl. reflexivity.
-simpl. (*rewrite IHn*)
Abort.
*)

Proof.
intro n.
induction n.
intros.
- simpl.
  reflexivity.
- intros my_l.
  simpl.
  rewrite IHn.
  simpl.
  reflexivity.
Qed.

Lemma ntl_tl : 
  forall (n:nat) (l:natlist) ,
  ntl (S n) l = ntl n (tl l).
Proof.
simpl. reflexivity.
Qed.

(*
Forma de crear TStream en la práctica

Variable TSh : L.
Varible TS3 : L
Variable TSt : TStream.


Compute TSnth 3 (TScons TSh (TScons TSh (TScons TSh (TS3 TSt)))).

*)


