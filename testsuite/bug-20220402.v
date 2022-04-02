From Coq Require Import Reals.
From Interval Require Import Tactic.
Open Scope R_scope.

Notation "x = y ± z" := (Rle (Rabs (x - y)) z) (at level 70, y at next level).

Lemma quintic1 x : x^5 = x + 1 -> x = 11673039782614185/10000000000000000 ± 1/100000000000000.
Proof.
intros H.
root H.
Qed.

Definition quintic2 x := ltac:(root (x^5 - x - 1)).

Goal forall x, x^5 - x - 1 = 0 -> x = 11673039782614185 / 10000000000000000 ± 1/1000000.
Proof.
intros x H.
apply quintic2 in H.
interval.
Qed.
