(**
This file is part of the CoqApprox formalization of rigorous
polynomial approximation in Coq:
http://tamadi.gforge.inria.fr/CoqApprox/

Copyright (C) 2010-2012, ENS de Lyon.
Copyright (C) 2010-2016, Inria.
Copyright (C) 2014-2016, IRIT.

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

From Coq Require Import Rdefinitions Raxioms RIneq Rbasic_fun.
From mathcomp.ssreflect Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition eqr (r1 r2 : R) : bool :=
  if Req_EM_T r1 r2 is left _ then true else false.

Lemma eqrP : Equality.axiom eqr.
Proof.
by move=> r1 r2; rewrite /eqr; case: Req_EM_T=> H; apply: (iffP idP).
Qed.

Canonical Structure real_eqMixin := EqMixin eqrP.
Canonical Structure real_eqType := Eval hnf in EqType R real_eqMixin.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Import Monoid.

Canonical Radd_monoid := Law RplusA Rplus_0_l Rplus_0_r.
Canonical Radd_comoid := ComLaw Rplus_comm.

Canonical Rmul_monoid := Law RmultA Rmult_1_l Rmult_1_r.
Canonical Rmul_comoid := ComLaw Rmult_comm.

Canonical Rmul_mul_law := MulLaw Rmult_0_l Rmult_0_r.
Canonical Radd_add_law := AddLaw Rmult_plus_distr_r Rmult_plus_distr_l.

Canonical Zmul_monoid := Monoid.Law Z.mul_assoc Z.mul_1_l Z.mul_1_r.
