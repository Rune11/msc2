(* apply Theorem.  ---   symmetry switches the two sides -> this can be used (and should be) used in the homework2.coq *)

Check 3.

Locate "+".

Example tpf:
  3 + 5 = 8.
Proof.
  simpl.
  reflexivity.
Qed.

Require Import Coq.Arith.Plus.

Example pc :
  forall n m: nat, n + m = m + n.
Proof.
  intros.
  apply plus_comm.
Qed.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a a' : aexp)
  | AMinus (a a' : aexp)
  | AMult (a a' : aexp).

Check (ANum 5).

Check APlus (ANum 5) (AMult (ANum 3) (ANum 2)) . (* 5 + 3 * 2 *)

Notation "x + y" := (APlus x y) (at level 50, left associativity).

Notation "x - y" := (AMinus x y) (at level 50, left associativity).

Notation "x * y" := (AMult x y) (at level 40, left associativity).

Check (ANum 5) + (ANum 3) * (ANum 2).

Fixpoint LeafCount (a : aexp) : nat :=
  match a with
  | ANum n => 1
  | APlus a1 a2 => ((LeafCount a1) + (LeafCount a2))%nat
  | AMinus a1 a2 => ((LeafCount a1) + (LeafCount a2))%nat
  | AMult a1 a2 => ((LeafCount a1) + (LeafCount a2))%nat
end.

(* %nat means that it coq has to use the + for nat, instead of the aexp one defined above *)

Eval compute in LeafCount(ANum 5).
Eval compute in LeafCount(ANum 5 + ANum 2).

Require Import Coq.Arith.Max.


Fixpoint depth (a:aexp) : nat :=
  match a with
  | ANum _ => 0
  | APlus a1 a2 => (1 + max depth(a1) (depth a2))%nat
  | AMinus a1 a2 => (1 + max depth(a1) (depth a2))%nat
  | AMult a1 a2 => (1 + max depth(a1) (depth a2))%nat
end.

Eval compute in depth(ANum 1).

