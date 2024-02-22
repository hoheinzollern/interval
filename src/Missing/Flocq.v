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

From Coq Require Import ZArith SpecFloat.
From Flocq Require Import BinarySingleNaN.

Definition SF2B' {prec emax} (x : spec_float) : binary_float prec emax :=
  match x with
  | S754_zero s => B754_zero s
  | S754_infinity s => B754_infinity s
  | S754_nan => B754_nan
  | S754_finite s m e =>
    match bounded prec emax m e as b return bounded prec emax m e = b -> _ with
    | true => B754_finite s m e
    | false => fun H => B754_nan
    end eq_refl
  end.

Lemma SF2B'_B2SF :
  forall {prec emax} (x : binary_float prec emax), SF2B' (B2SF x) = x.
Proof.
intros prec emax [s|s| |s m e H] ; try easy.
apply B2SF_inj.
simpl.
generalize (eq_refl (bounded prec emax m e)).
pattern (bounded prec emax m e) at 2 3.
apply eq_sym in H.
now elim H.
Qed.
