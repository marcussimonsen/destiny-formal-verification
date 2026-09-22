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

Inductive Value : Expression -> Type :=
  | VNat (n : nat) :
      Value (Nat n)
.
