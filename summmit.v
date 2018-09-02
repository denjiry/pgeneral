Inductive bool : Set :=
|true : bool
|false : bool.

Inductive False : Prop:=.

Inductive nat : Set :=
|O : nat
|S : nat -> nat.

Inductive True : Prop :=
I : True.

(* Inductive eq (A: Type) (x : A) : A-> Prop:= *)
(* eq_refl : x = x :>A. *)
  
Definition not (A : Prop) := A-> False.

Notation "~ x" := (not x).

Theorem sample : 1 <> 2.
Proof.
  unfold not.
  intros.
  (* Error: No such hypothesis: H *)
  inversion H. Qed.

