From mathcomp
     Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.
  Lemma contrap : forall A B : Prop, ((A -> B) -> (~B -> ~A)).
  Proof.
    rewrite /not.
    move => A0 B0 AtoB notB.
      by move /AtoB.
  Qed.
  