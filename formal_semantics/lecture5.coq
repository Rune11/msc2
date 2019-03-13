Require Import Coq.Strings.String.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AVar (id : string)
  | APlus (a a' : aexp)
  | AMult (a a' : aexp).

Definition state := string -> nat.

Definition empty : state :=
  fun _ => 0.


(* Require Import Coq.Arith.Plus.  Plus comm *)


Fixpoint aeval (a : aexp) (s : state) : nat :=
  match a with
  | ANum n => n
  | AVar id => s id
  | APlus a a' => (aeval a s) + (aeval a' s)
  | AMult a a' => (aeval a s) * (aeval a' s)
  end.

Locate "=?".

Fixpoint update
  (s : state)
  (x: string)
  (n: nat)
: state :=
  fun y => if (eqb x y) then n else s y.








