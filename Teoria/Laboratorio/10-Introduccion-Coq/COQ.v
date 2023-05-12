(*
PROOF ASSISTANTS
The flow of ideas between logic and computer science has not been unidirectional: CS has also 
made important contributions to logic. One of these has been the development of software tools 
for helping construct proofs of logical propositions. These tools fall into two broad categories:
-Automated theorem provers
-Proof assistants are hybrid tools that automate the more routine aspects of building proofs while depending on human guidance for more difficult aspects

COQ
Coq, a proof assistant that has been under development since 1983 and that in recent years has attracted 
a large community of users in both research and industry. Coq provides a rich environment for interactive 
development of machine-checked formal reasoning. The kernel of the Coq system is a simple proof-checker, 
which guarantees that only correct deduction steps are ever performed.

Coq has been a critical enabler for a huge variety of work across computer science and mathematics:
-As a platform for modeling programming languages, it has become a standard tool for researchers who need 
 to describe and reason about complex language definitions. It has been used, for example, to check the 
 security of the JavaCard platform
-As an environment for developing formally certified software and hardware, Coq has been used, for example, 
 to build CompCert, a fully-verified optimizing compiler for C
-As a realistic environment for functional programming with dependent types
-As a proof assistant for higher-order logic, it has been used to validate a number of important results in 
 mathematics. For example, its ability to include complex computations inside proofs made it possible to 
 develop the first formally verified proof of the 4-color theorem

'Some French computer scientists have a tradition of naming their software as animal species: Caml, Elan, Foc 
 or Phox are examples of this tacit convention. In French, 'coq' means rooster, and it sounds like the initials
 of the Calculus of Constructions (CoC) on which it is based. The rooster is also the national symbol of 
 France, and C-o-q are the first three letters of the name of Thierry Coquand, one of Coq's early developers'.

Coq itself can be viewed as a combination of a small but extremely expressive functional programming language 
plus a set of tools for stating and proving logical assertions. Moreover, when we come to look more closely, 
we find that these two sides of Coq are actually aspects of the very same underlying machinery 
-- i.e., proofs are programs.

INSTALL COQ
- Windows and MacOs: Binaries
- Linux: Snap (sudo snap install coq-prover)
- Ubuntu 16.04 or later: Desktop store (optional)

https://coq.inria.fr/download 


FUNCTIONAL PROGRAMMING IN COQ
The functional style of programming is founded on simple, everyday mathematical intuition: If a procedure 
or method has no side effects, then all we need to understand about it is how it maps inputs to 
outputs -- connection between programs and simple mathematical objects supports both formal correctness proofs 
and sound informal reasoning about program behavior.

The other sense in which functional programming is 'functional' is that it emphasizes the use of functions as 
first-class values 
Algebraic data types and pattern matching, which make it easy to construct and manipulate rich data structures, 
and polymorphic type systems supporting abstraction and code reuse. Coq offers all of these features. 
***Coq's native functional programming language, called Gallina. ***

**Data and Functions**
***Enumerated Types***
One notable aspect of Coq is that its set of built-in features is extremely small. For example, instead of 
providing the usual palette of atomic data types (booleans, integers, strings, etc.), Coq offers a powerful 
mechanism for defining new data types from scratch, with all these familiar types as instances.

Naturally, the Coq distribution comes with an extensive standard library providing definitions of booleans, 
numbers, and many common data structures like lists and hash tables. But there is nothing magic or primitive 
about these library definitions.
*)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday d : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.
(*
***Coq can often figure out these types for itself when they are not given explicitly -- i.e., it can do 
type inference ***

Next check that it works on some examples
-- Use compute command 
*)
Compute (next_weekday friday).
(* ==> saturday : day *)
Compute (next_weekday (next_weekday saturday)).
(* ==> monday : day *)
(*
**Booleans**
Following the pattern of the days of the week above, we can define the standard type bool of booleans, with 
members true and false.
*)
Inductive bool : Type :=
  | true
  | false.
(*
Functions over booleans can be defined in the same way as above:
*)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb b1 b2 : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb b1 b2 :=
  match b1 with
  | true => true
  | false => b2
  end.

Check orb.

Compute(andb true false).

(*
We can also introduce some familiar infix syntax for the boolean operations we have just defined. The Notation 
command defines a new symbolic notation for an existing definition.
*)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Compute(true && false).
Check andb.

(*
These examples are also an opportunity to introduce one more small feature of Coq's programming language: 
conditional expressions... *)

Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.


Compute(orb' true false).
(*
Coq's conditionals are exactly like those found in any other language, with one small generalization. 
Since the bool type is not built in, Coq actually supports conditional expressions over any inductively 
defined type with exactly two clauses in its definition. The guard is considered true if it evaluates to 
the 'constructor' of the first clause of the Inductive definition (which just happens to be called true 
in this case) and false if it evaluates to the second.

**Types**
Every expression in Coq has a type, describing what sort of thing it computes. The Check command asks Coq 
to print the type of an expression.
Check true.
(* ===> true : bool *)
*)
Check true
  : bool.
Check (negb true)
  : bool.
Check negb
  : bool -> bool.
Check negb.
Check (andb true).

(*
**New Types from Old**
The types we have defined so far are examples of 'enumerated types': their definitions explicitly enumerate a 
finite set of elements, called constructors. Here is a more interesting type definition, where one of 
the constructors takes an argument:
*)
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(*
An Inductive definition does two things:
-It defines a set of new constructors. E.g., red, primary, true, false, monday, etc. are constructors.
-It groups them into a new named type, like bool, rgb, or color.

Constructor expressions are formed by applying a constructor to zero or more other constructors or 
constructor expressions, obeying the declared number and types of the constructor arguments. E.g.,
-red
-true
-primary red

**Modules**
Coq provides a module system to aid in organizing large developments
*)
Module Playground.
  Definition myblue : rgb := blue.
End Playground.

Definition myblue : bool := true.
Check Playground.myblue : rgb.
Compute(Playground.myblue).
Check myblue : bool.

(*
**Tuples**
A single constructor with multiple parameters can be used to create a tuple type. As an example, 
consider representing the four bits in a nybble (half a byte). We first define a datatype bit that 
resembles bool (using the constructors B0 and B1 for the two possible bit values) and then define the datatype 
nybble, which is essentially a tuple of four bits. 
*)
Module TuplePlayground.
Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0)
  : nybble.

(*
The bits constructor acts as a wrapper for its contents. Unwrapping can be done by pattern-matching, as in 
the all_zero function which tests a nybble to see if all its bits are B0. We use underscore (_) as a wildcard 
pattern to avoid inventing variable names that will not be used.
*)
Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (all_zero (bits B1 B0 B1 B0)).
(* ===> false : bool *)
Compute (all_zero (bits B0 B0 B0 B0)).
(* ===> true : bool *)

End TuplePlayground.

(*
**Numbers**
To represent unary numbers with a Coq datatype, we use two constructors. The capital-letter O constructor 
represents zero. When the S constructor is applied to the representation of the natural number n, the result is 
the representation of n+1, where S stands for 'successor'. Here is the complete datatype definition.
*)
Module NatPlayground.
Inductive nat : Type :=
  | O
  | S (n : nat).

(*
Again, let's look at this in a little more detail. The definition of nat says how expressions in the set nat 
can be built:
- the constructor expression O belongs to the set nat;
- if n is a constructor expression belonging to the set nat, then S n is also a constructor expression belonging 
  to the set nat; and
- constructor expressions formed in these two ways are the only ones belonging to the set nat.
*)
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Check (S O).
Compute(S O).

End NatPlayground.

(* Coq library *)
Check (S (S (S (S O)))).
(* ===> 4 : nat *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).
Check 4.
(* ===> 2 : nat *)

(*
The constructor S has the type nat → nat, just like functions such as pred and minustwo:
*)
Check S : nat -> nat.
Check pred.
Check minustwo : nat -> nat.

Compute(pred 2).
Compute(S 2).

(*
Now let's go on and define some more functions over numbers.
For most interesting computations involving numbers, simple pattern matching is not enough: we also need 
recursion. For example, to check that a number n is even, we may need to recursively check whether n-2 is even. 
Such functions are introduced with the keyword Fixpoint instead of Definition.
*)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Compute(even 4).

(*
Naturally, we can also define multi-argument functions by recursion.
*)

Module NatPlayground2.
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).
(* ===> 5 : nat *)

(*
You can match two expressions at once by putting a comma between them:
*)
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.
Compute (minus 6 4).

(*
6 - 4 =
5 - 3 =
4 - 2 =
3 - 1 =
2 - 0 = 2
*)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x ? y" := (mult x y)
                       (at level 50, left associativity)
                       : nat_scope.
Compute ((1 + 1) ? 0). (* (1 + 1 * 0) 
1 + (1 * 0)
*)
End NatPlayground2.

(*
Again, we can make numerical expressions easier to read and write by introducing notations for addition, 
multiplication, and subtraction.
*)
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
Compute (1 + 1 * 0).

(*
The level, associativity, and nat_scope annotations control how these notations are treated by Coq's parser. 
The details are not important for present purposes)*

When we say that Coq comes with almost nothing built-in, we really mean it: even equality testing is a 
user-defined operation! Here is a function eqb, which tests natural numbers for equality, yielding a boolean. 
Note the use of nested matches (we could also have used a simultaneous match, as we did in minus.)
*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint eqb' (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S m' => false
  | S n', O  => false
  | S n', S m' => eqb' n' m'
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x =?? y" := (eqb' x y) (at level 70) : nat_scope.

(*
We now have two symbols that look like equality: = and =?. We'll have much more to say about the differences 
and similarities between them later. For now, the main thing to notice is that x = y is a logical 
claim -- a 'proposition' -- that we can try to prove, while x =? y is an expression whose value (either 
true or false) we can compute.
*)


