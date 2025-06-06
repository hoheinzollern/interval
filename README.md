CoqInterval
===========

This library provides vernacular files containing tactics for
simplifying the proofs of inequalities on expressions of real numbers
for the [Coq proof assistant](https://coq.inria.fr/).

This package is free software; you can redistribute it and/or modify it
under the terms of CeCILL-C Free Software License (see the [COPYING](COPYING) file).
Main author is Guillaume Melquiond <guillaume.melquiond@inria.fr>.

See the file [INSTALL.md](INSTALL.md) for installation instructions.


Project Home
------------

Homepage: https://coqinterval.gitlabpages.inria.fr/

Repository: https://gitlab.inria.fr/coqinterval/interval

Bug tracker: https://gitlab.inria.fr/coqinterval/interval/issues


Invocation
----------

In order to use the tactics of the library, one has to import the
`Interval.Tactic` file into a Coq proof script. The main tactic is named
`interval`.

The tactic can be applied on a goal of the form `c1 <= e <= c2` with
`e` an expression involving real-valued operators. Sub-expressions that
are not recognized by the tactic should be either terms `t` appearing in
hypothesis inequalities `c3 <= t <= c4` or simple integers. The
bounds `c1`, `c2`, etc, are expressions that contain only constant leaves,
e.g., `5 / sqrt (1 + PI)`.

The complete list of recognized goals is as follows:

  - `c1 <= e <= c2`;
  - `e <= c1`, `c1 <= e`, `e >= c1`, and `c1 >= e`;
  - `e < c1`, `c1 < e`, `e > c1`, and `c1 > e`;
  - `e <> c1` and `c1 <> e`;
  - `Rabs e <= c1`, handled as `-c1 <= e <= c1`.

The complete list of recognized hypotheses is as follows:

  - `c1 <= t <= c2`, `c1 <= e < c2`, `c1 < e <= c2`, and `c1 < e < c2`;
  - `t <= c1`, `c1 <= t`, `t >= c1`, and `c1 >= t`;
  - `t < c1`, `c1 < t`, `t > c1`, and `c1 > t`;
  - `Rabs t <= c1` and `Rabs t < c1`, handled as `-c1 <= e <= c1`.

The tactic recognizes the following operators: `PI`, `Ropp`, `Rabs`, `Rinv`,
`Rsqr`, `sqrt`, `cos`, `sin`, `tan`, `atan`, `exp`, `ln`, `pow`, `Rpower`,
`powerRZ`, `Rplus`, `Rminus`, `Rmult`, `Rdiv`. Flocq's operators `Zfloor`,
`Zceil`, `Ztrunc`, `ZnearestE` (composed with `IZR`) are also recognized.
Flocq's operator `Generic_fmt.round` with format `FLT_exp` is also supported.
There are some restrictions on the domain of a few functions: `pow` and
`powerRZ` should be written with a numeric exponent; the input of `cos`
and `sin` should be between `-2*PI` and `2*PI`; the input of `tan` should
be between `-PI/2` and `PI/2`. Outside of these domains, the
trigonometric functions return tight results only for singleton
input intervals.

A helper tactic `interval_intro e` is also available. Instead of proving
the current goal, it computes an enclosure of the expression `e` passed
as argument and it introduces the resulting inequalities into the proof
context. If only one bound is needed, the keywords `lower` and `upper`
can be passed to the tactic, so that it does not perform useless
computations. For example, `interval_intro e lower` introduces only the
inequality corresponding to the lower bound of `e` in the context. The
`interval_intro` tactic uses a fresh name for the generated inequalities,
unless one uses `as` followed by an intro pattern.

The `integral` tactic is a specialized version of `interval` that can be
used when the target enclosure involves an expression containing an integral.
Such an integral should be expressed using `RInt`; its bounds should be
constant; and its integrand should be an expression containing only
constant leaves except for the integration variable. Improper integrals
are also supported, when expressed using `RInt_gen`. The supported bounds
are then `(at_right 0) (at_point _)` and `(at_point _) (Rbar_locally
p_infty)`. In the improper case, the integrand should be of the form
`(fun t => f t * g t)` with `f` a function bounded on the integration
domain and `g t` one of the following expressions:

  - `(ln t) ^ _`,
  - `powerRZ t _ * (ln t) ^ _`,
  - `/ (t * (ln t) ^ _)`.

The `root H` tactic is a specialized version of `interval` that can be
used when the target enclosure involves an expression that is
constrained by an equation whose proof is `H`. Rather than an equality
proof, the tactic can also be passed an equality statement or even
just a real expression (then assumed to be zero), in which case the
tactic generates a new goal that asks for a proof of this equality.

The helper tactic `integral_intro` is the counterpart of `interval_intro`,
but for introducing enclosures of integrals into the proof context. As
with `interval_intro`, keywords `lower`, `upper`, and `as`, are
supported. Similarly, `root_intro` introduces enclosures of roots into
the proof context. Only `as` is supported in that case. When an
equality (rather than a proof) is passed to `root_intro`, no new goal
is generated, but the introduced hypothesis uses the equality as its
antecedent.

Tactics `interval_intro`, `integral_intro`, and `root_intro` are
available as degenerate forms that unify the obtained enclosure with
the current goal. They are meant to be used when the goal is an
existential variable, e.g., in a tactic-in-term context. Those
degenerate forms are named `interval`, `integral`, and `root`, for
conciseness, but they should not be confused with the original
tactics. For all intents and purposes, they behave like the `*_intro`
tactics.

The `plot` tactic produces correct function graphs, that is, two curves
that are guaranteed to enclose the given function on the given input
interval. It is invoked as `plot f x1 x2`. An output range can optionally
be passed: `plot f x1 x2 y1 y2`. If not, it is computed on the fly.

The `Interval.Plot` file provides a `Plot` command that can be used to
display a function graph. This is done by invoking the `gnuplot` command,
which thus needs to be installed. If a string is passed as an optional
argument, instead of invoking `gnuplot`, a file is created with the
corresponding Gnuplot script.

This file also provides a `Def` command, which has a syntax similar to
the `Definition`, except that the right-hand side is not a Gallina
term but an Ltac term. This command is meant to be used in conjunction
with the degenerate forms of the tactics `interval`, `integral`, and
`root`. If the name given to the term does not matter, the simpler
`Do` command can be used instead. Both commands display the type of
the generated term with some syntactic sugar. If the type is a
function graph (as produced by `plot`), then the command `Plot` is
invoked on it.

Fine-tuning
-----------

The behavior of the tactics can be tuned by passing an optional set of
parameters `with (param1, param2, ...)`. These parameters are parsed from
left to right. If some parameters are conflicting, the earlier ones are
discarded. Available parameters are as follows (with the type of their
arguments, if any):

  - `i_prec (p:positive)`

    Set the precision used to emulate floating-point computations. If
    this parameter is not specified, the tactics perform computations
    using machine floating-point numbers, when available. Otherwise, the
    tactic defaults to using `i_prec 53`. Note that, in some corner
    cases, the tactics might fail when using native numbers, despite the
    goals being provable using a 53-bit emulation.

  - `i_native_compute`

    Perform computations using `native_compute` instead of `vm_compute`.
    This greatly increases the startup time of the tactics, but makes the
    computations faster. This is useful only for
    computationally-intensive proofs.

  - `i_bisect (x:R)`

    Instruct the tactics to split the interval enclosing `x` until the
    goal is proved on all the sub-intervals. Several `i_bisect`
    parameters can be given. In that case, the tactic cycles through all
    of them, splitting the input domain along the corresponding variable.
    Computation time is more or less proportional to the final number of
    sub-domains. This parameter is only meaningful for the `interval` and
    `interval_intro` tactics.

  - `i_depth (n:nat)`

    Set the maximal bisection depth. Setting it to a nonzero value has no
    effect unless `i_bisect` parameters are also passed. If the maximal
    depth is `n`, the tactic will consider up to `2^n` sub-domains in the
    worst case. As with `i_bisect`, this parameter is only meaningful for
    the `interval` and `interval_intro` tactics. The maximal depth
    defaults to `15` for `interval`, and to `5` for `interval_intro`.
    Note that `interval_intro` computes the best enclosure that could be
    verified by `interval` using the same maximal depth.

  - `i_autodiff (x:R)`

    Instruct the tactics to perform an automatic differentiation of the
    target expression with respect to `x`. This makes the tactic about
    twice slower on each sub-domain. But it makes it possible to detect
    some monotony properties of the target expression, thus reducing the
    amount of sub-domains that need to be considered. Note that this is
    only useful if there are several occurrences of `x` in the goal. This
    parameter is only meaningful for the `interval` and `interval_intro`
    tactics. It is mutually exclusive with `i_taylor`. This parameter can
    also be used with the `root` and `root_intro` tactics, if they did
    not guess the correct target variable.

  - `i_taylor (x:R)`

    Instruct the tactics to compute a reliable polynomial enclosure of
    the target expression using Taylor models in `x`. As with
    `i_autodiff`, this is useful only if `x` occurs several times in the
    goal. Computing polynomial enclosures is much slower than automatic
    differentiation, but it can reduce the final number of sub-domains
    even further, thus speeding up proofs. Note that it might fail to
    prove goals that are feasible using automatic differentiation. As
    with `i_autodiff`, the `i_taylor` parameter is only meaningful for
    the `interval` and `interval_intro` tactics. It is implicit for the
    `integral`, `integral_intro`, and `plot` tactics, as Taylor models of
    the integrand (respectively, plotted function) are computed with
    respect to its variable.

  - `i_degree (d:nat)`

    Set the degree of polynomials used as enclosures. The default degree
    is 10. For `interval` and `interval_intro`, this parameter is only
    meaningful in conjunction with `i_taylor`.

  - `i_fuel (n:positive)`

    Set the maximum number of sub-domains considered when bounding
    integrals. The tactics maintain a set of integration sub-domains; it
    splits the sub-domains that contribute the most to the inaccuracy of
    the integral until its enclosure is tight enough to satisfy the goal.
    By default, the tactics will split the integration domain into at
    most 100 sub-domains. This parameter is only meaningful for the
    `integral` and `integral_intro` tactics.

  - `i_width (p:Z)`

    Instruct the `integral_intro` tactic to compute an enclosure of the
    integral that is no larger than `2^p`. The tactic will split the
    integration domain until the resulting enclosure reaches this width
    or `i_fuel` is exhausted. This parameter is meaningless for the other
    tactics. It is mutually exclusive with `i_relwidth`.

  - `i_relwidth (p:positive)`

    Instruct the `integral_intro` tactic to compute an enclosure of the
    integral whose relative width is no larger than `2^-p`. This
    parameter is meaningless for the other tactics. It defaults to 10.
    This means that, if neither `i_width` nor `i_relwidth` is used,
    `integral_intro` will compute an enclosure of the integral accurate
    to three decimal digits, assuming `i_fuel` is large enough.

  - `i_size (w h:positive)`

    Instruct the `plot` tactic to target a resolution of `w` by `h`
    pixels. This parameter is meaningless for the other tactics. It
    defaults to a resolution of `512x384`. The tactic will subdivide the
    input interval into `w` subintervals, and it will try to ensure that
    the function graph is no larger than a few pixels vertically.

  - `i_delay`

    Prevent Coq from verifying the generated proof at invocation time.
    Instead, Coq will check the proof term at `Qed` time. This makes
    the tactics `interval`, `integral`, and `root` instant. But it
    also means that failures, if any, will only be detected at `Qed`
    time, possibly with an inscrutable error message. This parameter
    is thus meant to be used when editing a proof script for which the
    tactics are already known to succeed. For the tactics
    `interval_intro`, `integral_intro`, and `root_intro`, computations
    are performed anyway (the risk of failure is thus negligible), but
    the `i_delay` parameter postpones their verification until `Qed`
    time. This makes these tactics twice as fast and is especially useful
    when optimizing the arguments of `i_prec`, `i_degree`, etc. For
    the degenerate forms of `interval_intro`, `integral_intro`, and
    `root_intro`, the `i_delay` parameter is always passed implicitly.

  - `i_decimal`

    Instruct the tactics to output interval bounds using a decimal
    representation. This parameter is only meaningful for the tactics
    `interval_intro`, `integral_intro`, and `root_intro`, as well as
    the corresponding degenerate tactics.


Examples
--------

```coq
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
Plot p1.

Definition p2 := ltac:(
  plot (fun x => sin (x + exp x))
    0 6 (-5/4) (5/4) with (i_size 120 90, i_degree 6)).
Plot p2 as "picture.gnuplot".

Plot ltac:(plot (fun x => sqrt (1 - x^2) * sin (x * 200)) (-1) 1
  with (i_degree 1, i_size 100 300)).

(* Commands Do and Def *)

Do interval (PI²/6).

Do integral (RInt_gen (fun x => 1/(1 + x)^2 * (ln x)^2) (at_right 0) (at_point 1))
  with (i_relwidth 30).

Def quintic x := root (x^5 - x = 1).
```
