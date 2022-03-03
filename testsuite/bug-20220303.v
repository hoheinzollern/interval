From Coq Require Import Reals.
From Interval Require Import Tactic.

Goal (1000 <= exp 800)%R.
Proof. interval. Qed.
