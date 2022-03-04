From Coq Require Import Reals.
From Interval Require Import Tactic.

Open Scope R_scope.

Goal forall x, x^3 + x - 1 = 0 -> Rabs (x - 67/100) <= 1/10.
Proof.
intros x H.
root H.
Qed.

Goal forall x z, 0 <= x <= 1 -> 2 <= z <= 2 -> (x+1)*(x+1) - z = 0 -> Rabs (x+1 - 1414/1000) <= 1/1000.
Proof.
intros x z Hx Hz H.
root H (x+1) with (i_depth 2).
Qed.
