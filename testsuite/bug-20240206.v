From Coq Require Import Reals.
From Interval Require Import Tactic.

Goal forall x, (0 <= x <= 1 -> -1 < x <= 2)%R.
Proof. intros x Hx. interval. Qed.

Goal forall x, (0 <= x <= 1 -> -1 <= x < 2)%R.
Proof. intros x Hx. interval. Qed.

Goal forall x, (0 <= x <= 1 -> -1 < x < 2)%R.
Proof. intros x Hx. interval. Qed.
