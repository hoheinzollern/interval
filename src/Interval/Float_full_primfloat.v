(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: https://coqinterval.gitlabpages.inria.fr/

Copyright (C) 2023-2023, Inria

This library is governed by the CeCILL-C license under French law and
abiding by the rules of distribution of free software. You can use,
modify and/or redistribute the library under the terms of the CeCILL-C
license as circulated by CEA, CNRS and Inria at the following URL:
http://www.cecill.info/

As a counterpart to the access to the source code and rights to copy,
modify and redistribute granted by the license, users are provided
only with a limited warranty and the library's author, the holder of
the economic rights, and the successive licensors have only limited
liability. See the COPYING file for more details.
*)

From Coq Require Import Reals Psatz Floats.

Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Float.
Require Import Float_full.
Require Import Specific_bigint Specific_ops.
Require Import Primitive_ops.
Require Import Interval_helper.

Module PrimFloatIntervalFull <: IntervalOps.

Module I := FloatIntervalFull PrimitiveFloat.
Module Faux := SpecificFloat BigIntRadix2.
Module Iaux := FloatIntervalFull Faux.
Module IT := IntervalTacticAux Iaux.

Import I.

Definition pi (prec : F.precision) : type :=
  (Ibnd 0x1.921fb54442d18p+1 0x1.921fb54442d20p+1)%float.

Theorem pi_correct : forall prec, contains (convert (pi prec)) (Xreal PI).
Proof.
intros prec.
cbv -[IZR PI Rle Rdiv].
IT.do_interval (@None R) (@nil R) (Faux.PtoP 60) 0%nat 0%nat false true itm_naive.
Qed.

Include FloatInterval PrimitiveFloat.

Definition cos := cos.
Definition sin := sin.
Definition tan := tan.
Definition atan := atan.
Definition exp := exp.
Definition ln := ln.

Definition cos_correct := cos_correct.
Definition sin_correct := sin_correct.
Definition tan_correct := tan_correct.
Definition atan_correct := atan_correct.
Definition exp_correct := exp_correct.
Definition ln_correct := ln_correct.

End PrimFloatIntervalFull.
