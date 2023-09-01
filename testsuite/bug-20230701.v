From Coq Require Import Reals.
From Interval Require Import Tactic.

Goal forall x : Datatypes.id R, (0 <= x <= 1)%R -> (0 <= x + x <= 2)%R.
Proof.
intros.
interval with (i_taylor x, i_prec 10).
Qed.
