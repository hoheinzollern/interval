From Coq Require Import Reals.
From Coquelicot Require Import Coquelicot.
From Interval Require Import Tactic.

Open Scope R_scope.

Definition stirling x eps := sqrt (2 * PI * x) * exp (x * (ln x - 1)) * exp (1 / (12 * x + eps)).
Definition digits x := IZR (Raux.Ztrunc (ln x / ln 10)) + 1.
Definition fact_50 eps (_: 0 <= eps <= 1) :=
  ltac:(interval (digits (stirling 50 eps)) with (i_prec 30)).

(*

Notation pow2 := (Raux.bpow Zaux.radix2).

Definition p0 := 1 * pow2 (-2).
Definition p1 := 4002712888408905 * pow2 (-59).
Definition p2 := 1218985200072455 * pow2 (-66).
Definition q0 := 1 * pow2 (-1).
Definition q1 := 8006155947364787 * pow2 (-57).
Definition q2 := 4573527866750985 * pow2 (-63).

Definition f t :=
  let t2 := t * t in
  let p := p0 + t2 * (p1 + t2 * p2) in
  let q := q0 + t2 * (q1 + t2 * q2) in
  2 * ((t * p) / (q - t * p) + 1/2).

Lemma method_error :
  forall t : R, Rabs t <= 0.35 ->
  Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof.
intros t Ht.
Time interval with (i_bisect t, i_taylor t, i_prec 80).
Qed.

Goal Rabs (RInt (fun tau => (0.5 * ln (tau^2 + 2.25) + 4.1396 + ln PI)^2 / (0.25 + tau^2))
  (-100000) 100000 - 226.8435) <= 2e-4.
Proof.
Time integral.
Qed.

Goal Rabs (RInt_gen (fun tau => (1 + (0.5 * ln (1 + 2.25/tau^2) + 4.1396 + ln PI) / ln tau)^2 / (1 + 0.25 / tau^2) *
  (powerRZ tau (-2) * (ln tau)^2)) (at_point 100000) (Rbar_locally p_infty) - 0.00317742) <= 1e-5.
Proof.
Time integral.
Qed.

Definition p := ltac:(plot (fun t => (f t - exp t) / exp t) (-0.35) 0.35 with (i_prec 80)).

*)
