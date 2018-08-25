Require Import Arith.
Definition g x := x - 100.
Definition f x := x + 100.
Compute f 10.
Theorem g_f : forall x, g (f x) = x.
Proof.
  intros x.
  unfold f, g.
  rewrite Nat.add_sub.
  reflexivity.
Qed.

Require Import List.
Import ListNotations.
Fixpoint reverse {A : Type} (xs : list A) :=
  match xs with
  | nil => nil
  | x :: xs' =>
    reverse xs' ++ [x]
  end.
Compute reverse [1;2;3].

Theorem reverse_reverse : forall (A : Type) (xs : list A),
    reverse (reverse xs) = xs.
Proof.
  intros A xs.
  induction xs.
  -simpl.
   reflexivity.
  -simpl.
   Lemma reverse_append : forall (A : Type) (xs ys : list A),
       reverse (xs ++ ys) = reverse ys ++ reverse xs.
   Proof.
     intros A xs ys.
     induction xs.
     -simpl.
      rewrite app_nil_r.
      reflexivity.
     -simpl.
      rewrite IHxs.
      rewrite app_assoc.
      reflexivity.
   Qed.
   rewrite reverse_append.
   rewrite IHxs.
   simpl.
   reflexivity.
Qed.
