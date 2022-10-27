From Coq Require Import Reals Lra.
From Interval Require Import Tactic.
Open Scope R_scope.

Definition foo x `(3 <= x <= 4) := ltac:(root (tan (x/4) = exp (sin x)) with i_decimal).

Goal forall x, 3 <= x <= 4 -> tan (x/4) = exp (sin x) -> Rabs (x - PI) <= 1/1000000000.
Proof.
  intros x Hx H.
  assert (H' := foo x Hx H).
  interval.
Qed.

Notation "x = y ± z" := (Rle (Rabs (x - y)) z) (at level 70, y at next level).

From Flocq Require Import Core.
Notation round := (round radix2 (FLT_exp (-1074) 53) ZnearestE).
Definition fadd x y := round (x + y).
Definition fmul x y := round (x * y).

Goal
  forall x, -1/256 <= x <= 1/256 ->
  let c2 := 9007164895206513 * bpow radix2 (-54) in
  fadd 1 (fmul x (fadd 1 (fmul x c2))) = exp x ± 1/100000000.
Proof.
  intros x Hx c2.
  unfold fadd, fmul, c2.
  interval with (i_taylor x).
Qed.
