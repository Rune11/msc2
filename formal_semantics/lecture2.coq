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