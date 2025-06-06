From Coq Require Import Reals.
From Interval Require Import Tactic.

Open Scope R_scope.

Notation pow2 := (Raux.bpow Zaux.radix2).

(*
Example taken from:
William J. Cody Jr. and William Waite
Software Manual for the Elementary Functions
*)

Goal forall x : R, Rabs x <= 35/100 ->
  let p := fun t => 1 * pow2 (-2) + t * (1116769 * pow2 (-28)) in
  let q := fun t => 1 * pow2 (-1) + t * (13418331 * pow2 (-28)) in
  let r := 2 * (x * p (x^2) / (q (x^2) - x * p (x^2)) + 1 * pow2 (-1)) in
  Rabs ((r - exp x) / exp x) <= 17 * pow2 (-34).
Proof.
intros x Hx p q r.
interval with (i_prec 40, i_bisect x, i_taylor x, i_degree 3).
Qed.
