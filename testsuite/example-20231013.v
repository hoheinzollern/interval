From Coq Require Import Reals.
From Flocq Require Import Core.
From Interval Require Import Tactic.

Open Scope R_scope.

Goal forall x, 0 <= x <= 10 ->
  Rabs (round radix2 (FLT_exp (-1074) 53) ZnearestE (IZR (Zfloor x)) + - IZR (Zfloor x)) <= 1/1000.
Proof.
intros x H.
interval.
Qed.

Goal forall x, -1/1000 <= round radix2 (FIX_exp (-4)) Zceil x - x <= 1/10.
Proof.
intros x.
interval.
Qed.
