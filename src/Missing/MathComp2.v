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

From HB Require Import structures.
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

HB.instance Definition _ := hasDecEq.Build R eqrP.

Fact RplusA : associative (Rplus).
Proof. by move=> *; rewrite Rplus_assoc. Qed.

Fact RmultA : associative (Rmult).
Proof. by move=> *; rewrite Rmult_assoc. Qed.

Import Monoid.

HB.instance Definition _ := isComLaw.Build R 0%R Rplus
  RplusA Rplus_comm Rplus_0_l.

HB.instance Definition _ := isComLaw.Build R 1%R Rmult
  RmultA Rmult_comm Rmult_1_l.

HB.instance Definition _ := isMulLaw.Build R 0%R Rmult Rmult_0_l Rmult_0_r.
HB.instance Definition _ := isAddLaw.Build R Rmult Rplus
  Rmult_plus_distr_r Rmult_plus_distr_l.

HB.instance Definition _ := Monoid.isLaw.Build Z 1%Z Z.mul
  Z.mul_assoc Z.mul_1_l Z.mul_1_r.

Module BigOp.
Notation bigopE := bigop.unlock.
End BigOp.
