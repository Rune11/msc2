(* test *)

(* add -a *)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AMinus (a : aexp)
  | APlus (a a' : aexp).
  

Fixpoint edgeCount (a : aexp) : nat :=
  match a with
  | ANum n => 0
  | AMinus a => 1 + (edgeCount a)
  | APlus a a' => 2 + (edgeCount a) + (edgeCount a')
  end.


Definition example_aexp : aexp :=
  (* define -(1 + 2) + (-3) *)
  APlus (AMinus(APlus (ANum 1) (ANum 2))) (AMinus (ANum 3)).

Example edgeCount_example :
  edgeCount example_aexp = 6.
Proof.
  reflexivity.
Qed.

(* end of the test *)

Fixpoint nodeCount (a: aexp) : nat :=
  match a with
  | ANum n => 1
  | APlus a a' => 1 + (nodeCount a) + (nodeCount a')
  | AMinus a => 1 + (nodeCount a)
  end.

Require Import Coq.Arith.Plus. (* Plus comm *)

Theorem aexp_edgenode :
  forall a : aexp, nodeCount a = (edgeCount a) + 1.
Proof.
  intro.
  induction a as [ | a' |].
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHa'.
  reflexivity.
  simpl.
  rewrite -> IHa1.
  rewrite -> IHa2.
  Check plus_comm.
  rewrite (plus_comm (edgeCount a1) 1).
  simpl.
  Check plus_assoc.
  rewrite plus_assoc.
  reflexivity.
Qed.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AMinus a => aeval a
  | APlus a a' => (aeval a) + (aeval a')
  end.

Eval compute in (aeval (APlus (ANum 1)(ANum 2))).

Fixpoint aopt (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AMinus a => AMinus (aopt a)
  | APlus a (ANum 0) => aopt a
  (* | APlus (ANum 0) a => aopt a *)
  | APlus a a' => APlus (aopt a) (aopt a')
  end.

Eval compute in (aopt (APlus(ANum 2) (ANum 0))).

Theorem aopt_sound:
  forall a:aexp, aeval (aopt a) = aeval a.
Proof.
  intro.
  induction a.
  simpl.
  reflexivity.
  simpl.
  rewrite IHa.
  reflexivity.
  destruct a2.
  destruct n.
  simpl.
  rewrite IHa1.
  Check plus_0_r.
  rewrite plus_0_r.
  reflexivity.
  simpl.
  rewrite IHa1.
  reflexivity.
  simpl.
  rewrite IHa1.

  
simpl (aeval(APlus a1 a2)).
  rewrite <- IHa1.
  rewrite <- IHa2.
  
  

(* lecture ended *)