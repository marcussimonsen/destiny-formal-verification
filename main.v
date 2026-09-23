From Stdlib Require Import List.
From Stdlib Require Import String.

(* Maps from the software foundations Maps chapter in LF *)

Definition total_map (A : Type) := string -> A.

Definition tm_empty {A : Type} (v : A) : total_map A := fun _ => v.

Definition tm_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (tm_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (tm_update m x v)
  (at level 100, x constr, right associativity).

Inductive Expression : Type :=
  | Nat (n : nat)
  | Plus (e1 e2 : Expression)
.

Inductive Predicate : Type :=
  | Bool (b : bool)
  | And (p1 p2 : Predicate)
  | Or (p1 p2 : Predicate)
  | Le (e1 e2 : Expression)
  | Not (p : Predicate)
.

Definition Destination := nat.

Inductive Frame : Type :=
  | Fe (d : Destination) (e : Expression)
  | Fv (n : nat) (d : Destination)
.

Inductive Judgment : Type :=
  | ev (e : Expression) (d : Destination)
  | ret (n : nat) (d : Destination)
  | frame (f : Frame) (d : Destination)
.

Notation "'[' x ']'" := (x :: nil).

Inductive Rewrite : list Judgment -> list Judgment -> Prop :=
  | evnat (v : nat) (d : Destination) :
    Rewrite [ev (Nat v) d] [ret v d]
  | evadd1 (e1 e2 : Expression) (d d1 : Destination) :
    Rewrite [ev (Plus e1 e2) d] ((ev e1 d1) :: [frame (Fe d1 e2) d])
  | evadd2 (n : nat) (e2 : Expression) (d d1 d2 : Destination) :
      Rewrite ((ret n d1) :: [frame (Fe d1 e2) d]) (ev e2 d2 :: [frame (Fv n d2) d])
  | evadd3 (n1 n2 : nat) (d d2 : Destination) :
      Rewrite (ret n2 d2 :: [frame (Fv n1 d2) d]) [ret (n1 + n2) d]
.

Inductive MultiStepRewrite : list Judgment -> list Judgment -> Prop :=
  | MSRefl (j : list Judgment) :
      MultiStepRewrite j j
  | MSStep (j1 j2 : list Judgment) :
      Rewrite j1 j2 -> MultiStepRewrite j1 j2
  | MSTrans (j1 j2 j3 : list Judgment) :
      MultiStepRewrite j1 j2 ->
      MultiStepRewrite j2 j3 ->
      MultiStepRewrite j1 j3
  | MSHead (j1 j1' : Judgment) (js : list Judgment) :
      MultiStepRewrite [j1] [j1'] ->
      MultiStepRewrite (j1 :: js) (j1' :: js)
.

Example three : nat := 3.
Example four : nat := 4.

Example e1 : Expression := Nat three.
Example e2 : Expression := Nat four.

Example d : Destination := 0.
Example d1 : Destination := 1.
Example d2 : Destination := 2.

Example ex1 : Judgment := ev e1 d.

Example ret1 : Judgment := ret three d.

Example rewrite1 : Rewrite [ex1] [ret1].
Proof.
  apply evnat.
Qed.

Example rewrite2 : MultiStepRewrite [ev (Plus e1 e2) d] [ret 7 d].
Proof.
  apply MSTrans with (j2 := ev (Nat three) d1 :: frame (Fe d1 e2) d :: nil).
  - apply MSStep. apply evadd1.
  - apply MSTrans with (j2 := ret three d1 :: frame (Fe d1 e2) d :: nil).
    + apply MSHead. apply MSStep. apply evnat.
    + apply MSTrans with (j2 := ev e2 d2 :: [frame (Fv three d2) d]).
      * apply MSStep. apply evadd2.
      * apply MSTrans with (j2 := ret four d2 :: [frame (Fv three d2) d]).
        -- apply MSHead. apply MSStep. apply evnat.
        -- apply MSStep. apply evadd3.
Qed.
