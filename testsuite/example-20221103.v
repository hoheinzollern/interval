From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.
Open Scope R_scope.

Goal Rabs (RInt_gen (fun x => 1/(1+x)^2 * (ln x)^2) (at_right 0) (at_point 1) - PI^2 / 6) <= 1/1000000.
Proof.
integral.
Qed.
