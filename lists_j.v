Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2. Qed.