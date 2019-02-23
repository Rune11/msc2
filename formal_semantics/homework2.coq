Inductive nat : Type :=
  | O
  | S (n : nat).

Fixpoint plusn (n m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => S (plusn n' m)
  end.

Fixpoint muln (n m : nat) {struct n} : nat :=
    match n with
    | O => O
    | S n' => plusn (muln n' m) m
    end.

Definition two := S (S O).
Definition three := S two.
Definition six := S (S (S three)).
Example muln_test :
  muln two three = six.
Proof.
  reflexivity.
Qed.

Theorem muln_riz :
    forall n : nat, muln n O = O.
  (* n * 0 = 0 *)
Proof.
  intros n.
  induction n as [| n' IHn'].
  simpl.
  reflexivity.
  simpl.
  rewrite -> IHn'.
  simpl.
  reflexivity.
Qed.

(* Would be nicer if I would use muln_riz insted of proving it again, but no idea how to do it*)

Theorem muln_zcomm :
  forall n : nat, muln O n = muln n O.
Proof.
  simpl.
  intros.
  induction n as [| n' IHn'].
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn'.
  simpl.
  reflexivity.
Qed.