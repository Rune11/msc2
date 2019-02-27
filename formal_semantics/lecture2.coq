Inductive nat : Type :=
    | O
    | S (n:nat).

Check 0.
Check S.

Definition two : nat := S(S O).
Definition three : nat := S two.
Definition five : nat := S(S(three)).

Theorem S_Cong :
    forall n m : nat, n = m -> S(n) = S(m).
Proof.
    intros.
    rewrite <- H.
    reflexivity.
Qed.

Theorem eqn_sym:
    forall n m: nat, n = m -> m = n.
Proof.
    intros.
    rewrite H.
    reflexivity.
Qed.

Theorem eqn_sym2:
    forall n m: nat, n = m -> m = n.
Proof.
    intros.
    symmetry.
    apply H.
Qed.
(* the two proofs above are the same *)

Fixpoint plusn (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S n' => S(plusn n' m)
    end.

(* y_combinator mvanier -> lambda function referring to itself*)

Example plusn_test:
    plusn two three = five.
Proof.
    simpl.
    reflexivity.
Qed.

Fixpoint twice(n:nat) : nat :=
    match n with
    | O => O
    | S n' => S(S(twice n'))
end.

Example twicen_test :
    twice two = S(S(S(S(O)))).
Proof.
    reflexivity.
Qed.

Notation "n + m" := (plusn n m)
    (at level 50, left associativity).

Theorem plusn_lid:
    forall n : nat, O + n = n.
Proof.
    intro.
    simpl.
    reflexivity.
Qed.

Theorem plusn_rid:
    forall n: nat, n + O = n.
Proof.
    intro.
    induction n as [|n'].
    simpl.
    reflexivity.
    simpl.
    (* this also proves it*)
    (* apply S_Cong. *)
    rewrite IHn'.
    reflexivity.
Qed.

Theorem plusn_rS:
    forall n m : nat, n + S m = S (n + m).
    (* n + (l + m) = l + (n + m)*)
Proof.
    intros.
    induction n as [|n'].
    simpl.
    reflexivity.
    simpl.
    rewrite IHn'.
    reflexivity.
Qed.