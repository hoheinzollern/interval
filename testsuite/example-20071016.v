From Coq Require Import Reals Lra.
From Interval Require Import Tactic.

Open Scope R_scope.
Notation "x = y ± z" := (Rle (Rabs (x - y)) z) (at level 70, y at next level).

(* Tactic interval *)

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 3/2.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
  interval.
Qed.

Goal
  forall x, -1 <= x <= 1 ->
  sqrt (1 - x) <= 141422/100000.
Proof.
  intros.
  interval_intro (sqrt (1 - x)) upper as H'.
  apply Rle_trans with (1 := H').
  lra.
Qed.

Goal
  forall x, 3/2 <= x <= 2 ->
  forall y, 1 <= y <= 33/32 ->
  sqrt(1 + x/sqrt(x+y)) = 144/1000*x + 118/100 ± 71/32768.
Proof.
  intros.
  interval with (i_prec 19, i_bisect x).
Qed.

Goal
  forall x, 1/2 <= x <= 2 ->
  sqrt x = ((((122 / 7397 * x + (-1733) / 13547) * x
             + 529 / 1274) * x + (-767) / 999) * x
             + 407 / 334) * x + 227 / 925 ± 5/65536.
Proof.
  intros.
  interval with (i_bisect x, i_taylor x, i_degree 3).
Qed.

Goal
  forall x, -1 <= x ->
  x < 1 + powerRZ x 3.
Proof.
  intros.
  apply Rminus_lt.
  interval with (i_bisect x, i_autodiff x).
Qed.

From Flocq Require Import Core.

Notation rnd := (round radix2 (FLT_exp (-1074) 53) ZnearestE).

Goal
  forall x, -1 <= x <= 1 ->
  rnd (1 + rnd (x * rnd (1 + rnd (x * (922446257493983/2251799813685248)))))
    = exp x ± 31/100.
Proof.
  intros.
  interval with (i_taylor x).
Qed.

(* Tactic integral *)

From Coquelicot Require Import Coquelicot.

Goal
  RInt (fun x => atan (sqrt (x*x + 2)) / (sqrt (x*x + 2) * (x*x + 1))) 0 1
    = 5/96*PI*PI ± 1/1000.
Proof.
  integral with (i_fuel 2, i_degree 5).
Qed.

Goal
  RInt_gen (fun x => 1 * (powerRZ x 3 * ln x^2))
           (at_right 0) (at_point 1) = 1/32.
Proof.
  refine ((fun H => Rle_antisym _ _ (proj2 H) (proj1 H)) _).
  integral with (i_prec 10).
Qed.

(*
Goal
  Rabs (RInt_gen (fun t => 1/sqrt t * exp (-(1*t)))
                 (at_point 1) (Rbar_locally p_infty)
        - 2788/10000) <= 1/1000.
Proof.
  interval.
Qed.
*)

(* Tactic root *)

Goal
  forall x:R, 999 <= x <= 1000 ->
  sin x = 0 -> x = 318 * PI ± 1/1000.
Proof.
  intros x Hx Hs.
  root Hs.
Qed.

(* Degenerate forms *)

Definition equal_1 x `(0 <= x <= PI/2) :=
  ltac:(interval ((cos x)² + (sin x)²) with (i_taylor x)).

Definition equal_PI_over_4 :=
  ltac:(integral (RInt (fun x => 1 / (1+x*x)) 0 1)).

Definition equal_0_442854401002 x :=
  ltac:(root (exp x = 2 - x) with i_decimal).

(* Tactic plot and command Plot *)

From Interval Require Import Plot.

Definition p1 := ltac:(plot (fun x => x^2 * sin (x^2)) (-4) 4).

Definition p2 := ltac:(
  plot (fun x => sin (x + exp x))
    0 6 (-5/4) (5/4) with (i_size 120 90, i_degree 6)).
Plot p2 as "picture.gnuplot".

Plot ltac:(plot (fun x => sqrt (1 - x^2) * sin (x * 200)) (-1) 1
  with (i_degree 1, i_size 100 300)) as "picture.gnuplot".
