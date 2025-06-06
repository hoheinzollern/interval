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

From Coq Require Import Reals Psatz PrimInt63 Uint63 Sint63 PArray Floats.

From Flocq Require Import Core PrimFloat BinarySingleNaN.

Require Import Missing.Flocq.
Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Float.
Require Import Float_full.
Require Import Specific_bigint Specific_ops.
Require Import Primitive_ops.
Require Import Lang_expr Lang_tac.
Require Import Interval_helper.

Local Open Scope R_scope.

Lemma sub_sub_assoc : forall x y z, (x - (y - z) = x - y + z)%uint63.
Proof.
intros x y z. rewrite 3Sint63.sub_of_Z, Sint63.add_of_Z.
apply Sint63.to_Z_inj. rewrite 4Sint63.of_Z_spec. rewrite <-4cmod_cmod by easy.
unfold Zcmod at 1 3. unfold Z.sub. rewrite (Z.add_comm (Sint63.to_Z x)).
rewrite Z.opp_eq_mul_m1. rewrite <-2Z.add_assoc, cmod_mul_add_mod; [| easy | now exists 1%Z].
rewrite cmod_add_mod; [| easy | now exists 1%Z].
apply f_equal with (f := fun n => (n mod wB + (- Z.quot wB 2))%Z). lia.
Qed.

Lemma asr_land : forall x y, (Uint63.to_Z y <= 62)%Z ->
  to_Z x = (to_Z (asr x y) * (2 ^ Uint63.to_Z y) + Uint63.to_Z (x land (lsl 1 y - 1)))%Z.
Proof. intros x y Hy.
  rewrite asr_spec, land_spec', Uint63.sub_spec, lsl_spec.
  change (Uint63.to_Z 1) with 1%Z. rewrite Z.mul_1_l. rewrite (Z.mod_small (2 ^ _)).
  2: { change wB with (2 ^ 63)%Z. split. apply (Zpower_ge_0 radix2).
    apply (Zpower_lt radix2); lia. }
  rewrite Z.mod_small.
  2: { change wB with (2 ^ 63)%Z. split. apply Z.lt_le_pred.
    apply (Zpower_gt_0 radix2). apply Uint63.to_Z_bounded.
    apply Z.lt_pred_le. apply (Zpower_le radix2). lia. }
  change (2 ^ _ - 1)%Z with (Z.pred (2 ^ Uint63.to_Z y)).
  rewrite <-Z.ones_equiv. rewrite Z.land_ones by apply Uint63.to_Z_bounded.
  unfold to_Z at 3. rewrite (proj2 (Uint63.ltb_spec _ _)) by
    now apply Z.le_lt_trans with (1 := Hy).
  rewrite <-(to_Z_mod_Uint63to_Z x).
  rewrite <-Znumtheory.Zmod_div_mod.
  - rewrite Z.mul_comm. apply Zdiv.Z_div_mod_eq_full.
  - apply (Zpower_gt_0 radix2). apply Uint63.to_Z_bounded.
  - easy.
  - change wB with (2 ^ 63)%Z.
    replace 63%Z with (63 - Uint63.to_Z y + Uint63.to_Z y)%Z by ring.
    rewrite Z.pow_add_r. apply Z.divide_factor_r.
    lia. apply Uint63.to_Z_bounded.
Qed.

Lemma ulp_FLX_le_FLT : forall (beta : radix) (emin prec : Z), Prec_gt_0 prec ->
  forall x : R, ulp beta (FLX_exp prec) x <= ulp beta (FLT_exp emin prec) x.
Proof. intros beta emin prec Iprec_gt_0 x. unfold ulp.
destruct (Req_bool_spec x 0) as [-> | Hx]; [rewrite negligible_exp_FLX by easy |].
- destruct (negligible_exp_FLT emin prec) as [n [-> _]]. apply bpow_ge_0.
- apply bpow_le. unfold cexp, FLX_exp, FLT_exp. lia.
Qed.

Lemma ulp_FLX_eq_FLT_large : forall (beta : radix) (emin prec : Z), Prec_gt_0 prec ->
  forall x : R, bpow beta (emin + prec - 1) <= Rabs x ->
  ulp beta (FLX_exp prec) x = ulp beta (FLT_exp emin prec) x.
Proof. intros beta emin prec Iprec_gt_0 x Hx.
rewrite <-(ulp_abs _ (FLX_exp _)), <-(ulp_abs _ (FLT_exp _ _)).
unfold ulp. destruct (Req_bool_spec (Rabs x) 0) as [H | _];
 [generalize (bpow_gt_0 beta (emin + prec - 1)); lra |]. f_equal.
unfold cexp. rewrite <-Rabs_Rabsolu in Hx. apply mag_gt_bpow in Hx.
unfold FLX_exp, FLT_exp. lia.
Qed.

Lemma succ_FLX_le_FLT : forall beta emin prec, Prec_gt_0 prec -> forall x,
  succ beta (FLX_exp prec) x <= succ beta (FLT_exp emin prec) x.
Proof. intros beta emin prec Iprec_gt_0 x. unfold succ.
case (Rle_bool 0 x); [now apply Rplus_le_compat_l, ulp_FLX_le_FLT |].
unfold pred_pos. case (Req_bool (- x) (bpow beta (mag beta (- x) - 1)));
  rewrite 2Ropp_minus_distr; apply Rplus_le_compat_r;
 [apply bpow_le; unfold FLT_exp, FLX_exp; lia | now apply ulp_FLX_le_FLT].
Qed.

Lemma pred_FLT_le_FLX : forall beta emin prec, Prec_gt_0 prec -> forall x,
  pred beta (FLT_exp emin prec) x <= pred beta (FLX_exp prec) x.
Proof. intros beta emin prec Iprec_gt_0 x. unfold pred.
apply Ropp_le_contravar. now apply succ_FLX_le_FLT.
Qed.

Lemma succ_FLX_eq_FLT_large : forall beta emin prec, Prec_gt_0 prec -> forall x,
  bpow beta (emin + prec - 1) <= x ->
  succ beta (FLX_exp prec) x = succ beta (FLT_exp emin prec) x.
Proof. intros beta emin prec Iprec_gt_0 x Hx. unfold succ, pred_pos.
destruct (Rle_bool_spec 0 x) as [_ | H].
2: generalize (bpow_gt_0 beta (emin + prec - 1)); lra.
rewrite <-ulp_FLX_eq_FLT_large; [easy.. |].
apply Rle_trans with (1 := Hx), Rle_abs.
Qed.

Lemma FLX_FLT_aux : forall (emin prec e : Z),
 (emin + prec - 1 < e)%Z -> FLX_exp prec e = FLT_exp emin prec e.
Proof. unfold FLX_exp, FLT_exp. lia. Qed.

Lemma pred_FLT_eq_FLX_large : forall beta emin prec, Prec_gt_0 prec -> forall x,
  bpow beta (emin + prec - 1) < x ->
  pred beta (FLT_exp emin prec) x = pred beta (FLX_exp prec) x.
Proof. intros beta emin prec Iprec_gt_0 x Hx. unfold pred, succ, pred_pos.
destruct (Rle_bool_spec 0 (- x)) as [H | _].
{ generalize (bpow_gt_0 beta (emin + prec - 1)). lra. }
rewrite 3Ropp_involutive. revert Hx.
destruct (Req_bool_spec x (bpow beta (mag beta x - 1))) as [-> | _]; intros Hx.
{ apply lt_bpow in Hx. rewrite mag_bpow. now rewrite <- FLX_FLT_aux by lia. }
rewrite <-ulp_FLX_eq_FLT_large; [easy.. |]. left. apply Rlt_le_trans with (1 := Hx), Rle_abs.
Qed.

Lemma succ_round_gt_id : forall (beta : radix) (fexp : Z -> Z), Valid_exp fexp ->
  forall rnd : R -> Z, Valid_rnd rnd -> forall x : R, ulp beta fexp x <> 0 ->
  x < succ beta fexp (Generic_fmt.round beta fexp rnd x).
Proof. intros beta fexp Ivalid_exp rnd Ivalid_rnd x Hulp.
destruct (generic_format_EM beta fexp x) as [Hx | Hx].
- rewrite round_generic by easy. unfold succ. destruct (Rle_bool_spec 0 x) as [H | H].
  + generalize (ulp_ge_0 beta fexp x). lra.
  + generalize (pred_pos_lt_id beta fexp (- x)). lra.
- revert Hx. destruct (succ_round_ge_id beta fexp rnd x) as [H | ->]; [easy |].
  intros Hx. now generalize (generic_format_succ beta fexp (Generic_fmt.round beta fexp rnd x)
   (generic_format_round _ _ _ _)).
Qed.

Lemma succ_round_FLX_le_FLT : forall beta emin prec, Prec_gt_0 prec ->
  forall rnd, Valid_rnd rnd -> forall x, generic_format beta (FLX_exp prec) x ->
  succ beta (FLX_exp prec) x <=
  succ beta (FLT_exp emin prec) (Generic_fmt.round beta (FLT_exp emin prec) rnd x).
Proof. intros beta emin prec Iprec_gt_0 rnd Ivalid_rnd x Hx.
generalize (FLX_exp_valid prec). intros Ivalid_exp_FLX.
apply succ_le_lt; [easy.. | |].
- apply generic_format_FLX_FLT with emin. generalize (FLT_exp_valid emin prec).
  intros Ivalid_exp_FLT. apply generic_format_succ; [easy |].
  now apply generic_format_round.
- apply succ_round_gt_id; [now apply FLT_exp_valid | easy |]. unfold ulp.
  destruct (Req_bool_spec x 0) as [-> | Hxneq0].
  + destruct (negligible_exp_FLT emin prec) as [n [-> _]].
    generalize (bpow_gt_0 beta (FLT_exp emin prec n)). lra.
  + generalize (bpow_gt_0 beta (cexp beta (FLT_exp emin prec) x)). lra.
Qed.

Lemma pred_round_FLT_le_FLX : forall beta emin prec, Prec_gt_0 prec ->
  forall rnd, Valid_rnd rnd -> forall x, generic_format beta (FLX_exp prec) x ->
  pred beta (FLT_exp emin prec) (Generic_fmt.round beta (FLT_exp emin prec) rnd x)
  <= pred beta (FLX_exp prec) x.
Proof. intros beta emin prec Iprec_gt_0 rnd Ivalid_rnd x Hx. unfold pred.
apply Ropp_le_contravar. set (rnd' := fun x => Z.opp (rnd (- x))).
replace (- Generic_fmt.round _ _ _ _) with (Generic_fmt.round beta (FLT_exp emin prec) rnd' (- x)).
2: { unfold Generic_fmt.round, scaled_mantissa, F2R. simpl. unfold rnd'. now rewrite cexp_opp,
    <-Ropp_mult_distr_l, Ropp_involutive, Ropp_mult_distr_l, <-opp_IZR. }
apply succ_round_FLX_le_FLT; [easy | | now apply generic_format_opp].
apply Build_Valid_rnd; unfold rnd'.
- intros x' y' Hx'y'. rewrite <-Z.opp_le_mono. apply Ivalid_rnd. lra.
- intros n. rewrite <-opp_IZR. apply Z.opp_inj. rewrite Z.opp_involutive.
  apply Ivalid_rnd.
Qed.

Lemma pred_FLX_exact_shift : forall beta prec, Prec_gt_0 prec -> forall x e,
  pred beta (FLX_exp prec) (x * bpow beta e) = pred beta (FLX_exp prec) x * bpow beta e.
Proof. intros beta prec Iprec_gt_0 x e. unfold pred.
rewrite <-Ropp_mult_distr_l. f_equal. rewrite Ropp_mult_distr_l.
now apply succ_FLX_exact_shift.
Qed.

Lemma succ_FLT_shift_ge : forall beta emin prec, Prec_gt_0 prec ->
  forall rnd, Valid_rnd rnd -> forall x, generic_format beta (FLT_exp emin prec) x ->
  bpow beta (emin + prec - 1) <= x -> forall e,
  succ beta (FLT_exp emin prec) x * bpow beta e <=
  succ beta (FLT_exp emin prec) (Generic_fmt.round beta (FLT_exp emin prec) rnd (x * bpow beta e)).
Proof. intros beta emin prec Iprec_gt_0 rnd Ivalid_rnd x Hformat_x Hmin_x e.
rewrite <-(succ_FLX_eq_FLT_large _ _ _ _ x) by easy. rewrite <-succ_FLX_exact_shift by easy.
apply succ_round_FLX_le_FLT; [easy.. |].
now apply Mult_error.mult_bpow_exact_FLX, generic_format_FLX_FLT with emin.
Qed.

Lemma pred_FLT_shift_le : forall beta emin prec, Prec_gt_0 prec ->
  forall rnd, Valid_rnd rnd -> forall x, generic_format beta (FLT_exp emin prec) x ->
  bpow beta (emin + prec - 1) < x -> forall e,
  pred beta (FLT_exp emin prec) (Generic_fmt.round beta (FLT_exp emin prec) rnd (x * bpow beta e))
  <= pred beta (FLT_exp emin prec) x * bpow beta e.
Proof. intros beta emin prec Iprec_gt_0 rnd Ivalid_rnd x Hformat_x Hinf_x e.
rewrite (pred_FLT_eq_FLX_large _ _ _ _ x) by easy. rewrite <-pred_FLX_exact_shift by easy.
apply pred_round_FLT_le_FLX; [easy.. |].
now apply Mult_error.mult_bpow_exact_FLX, generic_format_FLX_FLT with emin.
Qed.

Lemma pred_round_N_le :
  forall beta fexp choice, Valid_exp fexp ->
  forall x y e,
  bpow beta (e - 1) < Rabs (Generic_fmt.round beta fexp (Znearest choice) x) < bpow beta e ->
  (x - y <= /2 * bpow beta (fexp e))%R ->
  (pred beta fexp (Generic_fmt.round beta fexp (Znearest choice) x) <= y)%R.
Proof.
intros beta fexp choice Vexp x y e [He1 He2] Hxy.
apply Rle_trans with (x - /2 * bpow beta (fexp e))%R.
2: lra.
clear Hxy.
unfold pred, succ, pred_pos, ulp, cexp.
rewrite Ropp_involutive.
assert (Ha: (Rabs (Generic_fmt.round beta fexp (Znearest choice) x) <> 0)%R).
{ intros H.
  apply Rlt_not_le with (1 := He1).
  rewrite H.
  apply bpow_ge_0. }
rewrite 2!(Req_bool_false _ 0).
2: { contradict Ha. rewrite Ha. apply Rabs_R0. }
2: { contradict Ha. rewrite <- Rabs_Ropp, Ha. apply Rabs_R0. }
assert (Hm: mag beta (Generic_fmt.round beta fexp (Znearest choice) x) = e :> Z).
{ apply mag_unique.
  refine (conj _ He2).
  now apply Rlt_le. }
rewrite mag_opp, Hm.
generalize (error_le_half_ulp beta fexp choice x).
unfold ulp, cexp.
rewrite Req_bool_false.
2: {
  intros H.
  apply Rlt_not_le with (1 := He1).
  rewrite H, round_0 by apply valid_rnd_N.
  rewrite Rabs_R0.
  apply bpow_ge_0. }
replace (mag beta x : Z) with e.
2: {
  destruct (mag_round beta fexp (Znearest choice) x).
  { contradict Ha.
    rewrite Ha. apply Rabs_R0. }
  now rewrite <- H.
  rewrite H in He1, He2.
  apply lt_bpow in He1, He2.
  lia. }
intros H.
apply Rabs_le_inv in H.
case Rle_bool_spec ; intros H'.
- lra.
- rewrite Req_bool_false. lra.
  intros H''.
  apply Rlt_not_le with (1 := He1).
  rewrite H'', Rabs_pos_eq.
  apply Rle_refl.
  apply bpow_ge_0.
Qed.

Lemma succ_round_N_ge :
  forall beta fexp choice, Valid_exp fexp ->
  forall x y e,
  bpow beta (e - 1) < Rabs (Generic_fmt.round beta fexp (Znearest choice) x) < bpow beta e ->
  (y - x <= /2 * bpow beta (fexp e))%R ->
  (y <= succ beta fexp (Generic_fmt.round beta fexp (Znearest choice) x))%R.
Proof.
intros beta fexp choice Vexp x y e [He1 He2] Hxy.
apply Rle_trans with (x + /2 * bpow beta (fexp e))%R.
lra.
clear Hxy.
unfold succ, pred_pos, ulp, cexp.
assert (Ha: (Rabs (Generic_fmt.round beta fexp (Znearest choice) x) <> 0)%R).
{ intros H.
  apply Rlt_not_le with (1 := He1).
  rewrite H.
  apply bpow_ge_0. }
rewrite 2!(Req_bool_false _ 0).
2: { contradict Ha. rewrite <- Rabs_Ropp, Ha. apply Rabs_R0. }
2: { contradict Ha. rewrite Ha. apply Rabs_R0. }
assert (Hm: mag beta (Generic_fmt.round beta fexp (Znearest choice) x) = e :> Z).
{ apply mag_unique.
  refine (conj _ He2).
  now apply Rlt_le. }
rewrite mag_opp, Hm.
generalize (error_le_half_ulp beta fexp choice x).
unfold ulp, cexp.
rewrite Req_bool_false.
2: {
  intros H.
  apply Rlt_not_le with (1 := He1).
  rewrite H, round_0 by apply valid_rnd_N.
  rewrite Rabs_R0.
  apply bpow_ge_0. }
replace (mag beta x : Z) with e.
2: {
  destruct (mag_round beta fexp (Znearest choice) x).
  { contradict Ha.
    rewrite Ha. apply Rabs_R0. }
  now rewrite <- H.
  rewrite H in He1, He2.
  apply lt_bpow in He1, He2.
  lia. }
intros H.
apply Rabs_le_inv in H.
case Rle_bool_spec ; intros H'.
- lra.
- rewrite Req_bool_false. lra.
  intros H''.
  apply Rlt_not_le with (1 := He1).
  rewrite <- Rabs_Ropp, H'', Rabs_pos_eq.
  apply Rle_refl.
  apply bpow_ge_0.
Qed.

Lemma pred_succ_round_N_le :
  forall beta fexp choice, Valid_exp fexp ->
  forall x y e,
  bpow beta (e - 1) < Rabs (Generic_fmt.round beta fexp (Znearest choice) x) < bpow beta e ->
  (Rabs (x - y) <= /2 * bpow beta (fexp e))%R ->
  (pred beta fexp (Generic_fmt.round beta fexp (Znearest choice) x) <= y <= succ beta fexp (Generic_fmt.round beta fexp (Znearest choice) x))%R.
Proof.
intros beta fexp choice Vexp x y e He Hxy.
apply Rabs_le_inv in Hxy.
split.
now apply pred_round_N_le with (1 := Vexp) (2 := He).
apply succ_round_N_ge with (1 := Vexp) (2 := He).
lra.
Qed.

Module PrimFloatIntervalFull <: IntervalOps.

Module Faux := SpecificFloat BigIntRadix2.
Module Iaux := FloatIntervalFull Faux.
Module IT := IntervalTacticAux Iaux.
Import IT.SimpleTactic.

Module I := FloatIntervalFull PrimitiveFloat.
Import I.

Definition pi (prec : F.precision) : type :=
  (Ibnd 0x1.921fb54442d18p+1 0x1.921fb54442d19p+1)%float.

Theorem pi_correct : forall prec, contains (convert (pi prec)) (Xreal PI).
Proof.
intros prec.
cbv -[IZR PI Rle Rdiv].
interval with (i_prec 60).
Qed.

Include FloatInterval PrimitiveFloat.

Definition cos := cos.
Definition sin := sin.
Definition tan := tan.
Definition atan := atan.
Definition ln := ln.

Definition cos_correct := cos_correct.
Definition sin_correct := sin_correct.
Definition tan_correct := tan_correct.
Definition atan_correct := atan_correct.
Definition ln_correct := ln_correct.

Module ExpImpl.

Definition consts := [|
  0x1.0000000000000p0%float;
  0x1.02c9a3e778061p0%float;
  0x1.059b0d3158574p0%float;
  0x1.0874518759bc8p0%float;
  0x1.0b5586cf9890fp0%float;
  0x1.0e3ec32d3d1a2p0%float;
  0x1.11301d0125b51p0%float;
  0x1.1429aaea92de0p0%float;
  0x1.172b83c7d517bp0%float;
  0x1.1a35beb6fcb75p0%float;
  0x1.1d4873168b9aap0%float;
  0x1.2063b88628cd6p0%float;
  0x1.2387a6e756238p0%float;
  0x1.26b4565e27cddp0%float;
  0x1.29e9df51fdee1p0%float;
  0x1.2d285a6e4030bp0%float;
  0x1.306fe0a31b715p0%float;
  0x1.33c08b26416ffp0%float;
  0x1.371a7373aa9cbp0%float;
  0x1.3a7db34e59ff7p0%float;
  0x1.3dea64c123422p0%float;
  0x1.4160a21f72e2ap0%float;
  0x1.44e086061892dp0%float;
  0x1.486a2b5c13cd0p0%float;
  0x1.4bfdad5362a27p0%float;
  0x1.4f9b2769d2ca7p0%float;
  0x1.5342b569d4f82p0%float;
  0x1.56f4736b527dap0%float;
  0x1.5ab07dd485429p0%float;
  0x1.5e76f15ad2148p0%float;
  0x1.6247eb03a5585p0%float;
  0x1.6623882552225p0%float;
  0x1.6a09e667f3bcdp0%float;
  0x1.6dfb23c651a2fp0%float;
  0x1.71f75e8ec5f74p0%float;
  0x1.75feb564267c9p0%float;
  0x1.7a11473eb0187p0%float;
  0x1.7e2f336cf4e62p0%float;
  0x1.82589994cce13p0%float;
  0x1.868d99b4492edp0%float;
  0x1.8ace5422aa0dbp0%float;
  0x1.8f1ae99157736p0%float;
  0x1.93737b0cdc5e5p0%float;
  0x1.97d829fde4e50p0%float;
  0x1.9c49182a3f090p0%float;
  0x1.a0c667b5de565p0%float;
  0x1.a5503b23e255dp0%float;
  0x1.a9e6b5579fdbfp0%float;
  0x1.ae89f995ad3adp0%float;
  0x1.b33a2b84f15fbp0%float;
  0x1.b7f76f2fb5e47p0%float;
  0x1.bcc1e904bc1d2p0%float;
  0x1.c199bdd85529cp0%float;
  0x1.c67f12e57d14bp0%float;
  0x1.cb720dcef9069p0%float;
  0x1.d072d4a07897cp0%float;
  0x1.d5818dcfba487p0%float;
  0x1.da9e603db3285p0%float;
  0x1.dfc97337b9b5fp0%float;
  0x1.e502ee78b3ff6p0%float;
  0x1.ea4afa2a490dap0%float;
  0x1.efa1bee615a27p0%float;
  0x1.f50765b6e4540p0%float;
  0x1.fa7c1819e90d8p0%float|
  0%float|].

Definition InvLog2_64 := 0x1.71547652b82fep6%float.
Definition Log2div64h := 0x1.62e42fefap-7%float.
Definition Log2div64l := 0x1.cf79abc9e3b3ap-46%float.

Definition q1 := 0x1p0%float.
Definition q2 := 0x1.fffffffffdb3bp-2%float.
Definition q3 := 0x1.555555555653ep-3%float.
Definition q4 := 0x1.555573f218b93p-5%float.
Definition q5 := 0x1.111112d9f54c8p-7%float.

Definition g0 : ArithExpr (BinFloat :: nil) BinFloat :=
  Op MUL (Var 0) (Op ADD (BinFl q1) (Op MUL (Var 0) (Op ADD (BinFl q2) (Op MUL (Var 0) (Op ADD (BinFl q3) (Op MUL (Var 0) (Op ADD (BinFl q4) (Op MUL (Var 0) (BinFl q5))))))))).

Definition Papprox (t : PrimFloat.float) := Eval cbv in evalPrim g0 (t, tt).

Definition exp_aux (x : F.type) :=
  if PrimFloat.ltb x (-0x1.74385446d71c4p9)%float then (0%float, 0x1p-1074%float) else
  if PrimFloat.ltb 0x1.62e42fefa39efp9%float x then (0x1.fffffffffffffp1023%float, infinity) else
  let k0 := (x * InvLog2_64 + 0x1.8p52)%float in let kf := (k0 - 0x1.8p52)%float in
  let tf := (x - kf * Log2div64h - kf * Log2div64l)%float in
  let ki := (normfr_mantissa (fst (frshiftexp k0)) - 6755399440921280)%uint63 in
  let C := consts.[PrimInt63.land ki 63] in
  let kq := PrimInt63.asr ki 6 in let y := (C * Papprox tf)%float in
  let lb := (C + (y + -0x1.25p-57))%float in let ub := (C + (y + 0x1.25p-57))%float in
  (next_down (ldshiftexp lb kq), next_up (ldshiftexp ub kq)).

Lemma exp_aux_correct :
  forall x, is_finite (Prim2B x) = true ->
 (let lb := fst (exp_aux x) in
  F.valid_lb lb = true /\
  match F.toX lb with
  | Xreal.Xnan => True
  | Xreal.Xreal r => r <= Rtrigo_def.exp (B2R (Prim2B x))
  end) /\
 (let ub := snd (exp_aux x) in
  F.valid_ub ub = true /\
  match F.toX ub with
  | Xreal.Xnan => True
  | Xreal.Xreal r => Rtrigo_def.exp (B2R (Prim2B x)) <= r
  end).
Proof.
intros x Fx. unfold exp_aux. rewrite 2ltb_equiv, 2Bltb_correct by easy.
set (xr := B2R (Prim2B x)). fold xr in Fx. case Rlt_bool_spec.
{ intros. change ((true = true /\ 0 <= Rtrigo_def.exp xr) /\
    true = true /\ Rtrigo_def.exp xr <= 1 * Rpow2 (-1074)). clearbody xr. cbv -[Rinv Rmult Rlt IZR]in H.
  refine ((fun J => conj (conj eq_refl (proj1 J)) (conj eq_refl (proj2 J))) _).
  interval with (i_prec 80). }
case Rlt_bool_spec.
{ intros H _.
  change ((true = true /\ IZR (9007199254740991 * 2 ^ 971) <= Rtrigo_def.exp xr) /\ true = true /\ True).
  refine ((fun J => conj (conj eq_refl J) (conj eq_refl I)) _).
  apply (@succ_le_lt radix2 (FLT_exp (-1074) 53)) in H.
  2: now apply FLT_exp_valid.
  2, 3: apply generic_format_B2R.
  clearbody xr. revert H. unfold succ.
  rewrite Rle_bool_true by now apply F2R_ge_0.
  set (f := Prim2B _).
  generalize (@Bulp_correct prec emax Hprec Hmax f eq_refl).
  change (fexp prec emax) with (FLT_exp (-1074) 53). intros [<- _] H.
  cbv -[Rinv Rmult Rle IZR] in H.
  interval with (i_prec 80). }
intros H0 H1.
assert (Hx : -6548164122079684 * Rpow2 (-43) <= xr <= 6243314768165359 * Rpow2 (-43)).
{ clearbody xr. cbv -[Rinv Rmult Rle IZR] in H0, H1 |- *. lra. } clear H0 H1.

change 6755399440921280%uint63 with (PrimInt63.sub 6755399441055744 134464).

rewrite sub_sub_assoc. set (ki := (normfr_mantissa _ - _)%uint63).
replace (PrimInt63.land _ _) with (PrimInt63.land ki 63).
2: { rewrite <-(Uint63.of_to_Z (PrimInt63.land ki 63)),
             <-(Uint63.of_to_Z (PrimInt63.land (ki + 134464) 63)).
  rewrite 2land_spec', Uint63.add_spec. change (_ 63%uint63) with (Z.ones 6).
  rewrite 2Z.land_ones by easy. rewrite <-Znumtheory.Zmod_div_mod; [| easy | easy |].
  2: { now exists (2 ^ 57)%Z. } change (_ 134464%uint63) with (2101 * 64)%Z.
  now rewrite Z.mod_add by easy. }
set (kr := PrimInt63.land ki 63).
set (dlb := (-0x1.25p-57)%float). set (dub := 0x1.25p-57%float).
set (d := 0x1.25p-57).
assert (d = Rabs (SF2R radix2 (Prim2SF dlb)) /\ d = Rabs (SF2R radix2 (Prim2SF dub))) as [Hdlb Hdub].
{ cbn. unfold F2R, d. cbn. change (Z.neg 5154510511013888) with (Z.opp 5154510511013888)%Z.
  rewrite opp_IZR, <-Ropp_mult_distr_l, Rabs_Ropp, Rabs_pos_eq; lra. }

unfold xr in Hx |- *. clear xr.
rewrite <-is_finite_SF_B2SF, B2SF_Prim2B in Fx.
rewrite <-Prim2SF2R_Prim2B2R in Hx |- *.
assert (Hxr_ : -746 <= SF2R radix2 (Prim2SF x) <= 710) by interval.

set (xR := SF2R radix2 (Prim2SF x)).
assert (HxR : generic_format radix2 (FLT_exp (-1074) 53) xR).
{ unfold xR. rewrite Prim2SF2R_Prim2B2R. apply generic_format_B2R. }

unfold Interval.contains, I.convert. simpl. rewrite 2PrimitiveFloat.toX_Prim2B.
unfold I.F.valid_lb, I.F.valid_ub.
rewrite 2eqb_equiv, next_down_equiv, next_up_equiv, 2ldshiftexp_equiv.

revert kr. rename ki into ki_.
set (ki' := @FastNearbyintToInt (BinFloat :: nil) (Op MUL (Var 0) (BinFl InvLog2_64))).
change ki_ with (evalPrim ki' (x, tt)).
assert_float (fun ki => -68736 <= IZR ki <= 65536).
{ cbn -[bpow]. unfold Rrnd.rnd, round_mode. interval. }

intros ki Hki0 Hki kr.

assert (Hki1 : (-68736 <= to_Z ki <= 65536)%Z).
{ destruct Hki0 as [Hki00 Hki01]. now apply le_IZR in Hki00, Hki01. }

assert (Hki2 : (-1074 <= to_Z (asr ki 6) <= 1024)%Z).
{ rewrite asr_spec. destruct Hki1 as [Hki10 Hki11].
  apply (Z.div_le_mono _ _ 64 ltac:(easy)) in Hki10, Hki11.
  cbn in Hki10, Hki11 |- *. lia. }

replace (Uint63.to_Z _) with ((to_Z (asr ki 6)) + 2101)%Z.
2: { rewrite <- to_Z_mod_Uint63to_Z.
  rewrite 2!asr_spec, Sint63.add_spec, cmod_small by (cbn; lia).
  change (to_Z 134464) with (2101 * 64)%Z.
  rewrite Zdiv.Z_div_plus by easy.
  apply eq_sym, Z.mod_small.
  revert Hki2. rewrite asr_spec. cbn; lia. }
rewrite Z.add_simpl_r.
set (kq := asr ki 6).

assert (Hkr0 : (0 <= to_Z kr <= 63)%Z).
{ unfold kr. unfold to_Z. rewrite (proj2 (Uint63.ltb_spec _ _)).
  - rewrite land_spec'. change (Uint63.to_Z 63) with (Z.ones 6). rewrite Z.land_ones by easy.
    generalize (Z.mod_pos_bound (Uint63.to_Z ki) (2 ^ 6)%Z ltac:(easy)). lia.
  - rewrite land_spec'. change (Uint63.to_Z 63) with (Z.ones 6). rewrite Z.land_ones by easy.
    generalize (Z.mod_pos_bound (Uint63.to_Z ki) (2 ^ 6)%Z ltac:(easy)).
    change (Uint63.to_Z min_int) with 4611686018427387904%Z. lia. }

assert (Hkr1 : to_Z kr = Uint63.to_Z kr).
{ rewrite <- to_Z_mod_Uint63to_Z. apply eq_sym, Z.mod_small. cbn -[kr]. lia. }

assert (Hkr3 : (0 <= IZR (to_Z kr) <= 63)) by (now split; apply IZR_le).

set (k0 := (x * InvLog2_64 + 6755399441055744)%float). fold k0 in ki.

change (consts.[kr]) with (@evalPrim (Integer :: nil) _ (ArrayAcc consts (Var 0)) (kr, tt)).
assert_float (fun C => 0.984375 <= C <= 1.984375 /\
  (Uint63.to_Z kr = 0%Z -> C = 1) /\
  Rabs (C - Rtrigo_def.exp (IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64))) <= Rpow2 (-53)).
{ split. simpl. unfold Int32.in_bounds. simpl ; lia. easy. }
{ split. easy. cbn. fold kr. lia. }
{ simpl evalRounded. rewrite <- Hkr1.
  assert (H: forall i, (0 <= i <= 63)%Z ->
    Rabs (SF2R radix2 (Prim2SF consts.[of_Z i]) - Rtrigo_def.exp (IZR i * (Rpower.ln 2 / 64))) <= Rpow2 (-53)).
  { intros i [Hi1 Hi2].
    assert (Hi: forall j, (i <= j)%Z -> i = j \/ (i <= Z.pred j)%Z) by lia.
    do 64 (apply Hi in Hi2 ; destruct Hi2 as [->|Hi2] ;
      [cbn -[bpow]; interval with (i_prec 61) | simpl Z.pred in Hi2]).
    now elim (Z.le_trans _ _ _ Hi1 Hi2). }
  split; [| split].
  3: { now apply H. }
  2: { intros ->. now apply Rinv_r, IZR_neq. }
  replace (SF2R _ _) with
   (SF2R radix2 (Prim2SF consts.[of_Z (to_Z kr)]) - Rtrigo_def.exp (IZR (to_Z kr) * (Rpower.ln 2 / 64))
     + Rtrigo_def.exp (IZR (to_Z kr) * (Rpower.ln 2 / 64))) by ring.
  generalize (H (to_Z kr) Hkr0).
  generalize (SF2R radix2 (Prim2SF consts.[of_Z (to_Z kr)]) - Rtrigo_def.exp (IZR (to_Z kr) * (Rpower.ln 2 / 64))).
  intros; interval. }
intros C' [bnd_C [HC1 HC2]] FC _.
set (C := SF2R radix2 (Prim2SF C')).

set (k'' := FastNearbyint (@Op (BinFloat :: nil) _ MUL (Var 0) (BinFl InvLog2_64))).
change (k0 - 6755399441055744)%float with (@evalPrim (BinFloat :: nil) _ k'' (x, tt)).
assert_float (fun k => -68736 <= k <= 65536).
{ cbn -[bpow]. unfold Rrnd.nearbyint, Rrnd.rnd, round_mode.
  rewrite round_FIX_IZR. interval. }
intros k Hk Fk Ek.

set (te := xR - IZR (to_Z ki) * (Rpower.ln 2 / 64)).
set (t'' := @Op (BinFloat :: BinFloat :: nil) _ SUB (OpExact SUB (Var 1) (OpExact MUL (Var 0) (BinFl Log2div64h))) (Op MUL (Var 0) (BinFl Log2div64l))).
change (x - _ - _)%float with (@evalPrim (BinFloat :: BinFloat :: nil) _ t'' (k, (x, tt))).
assert_float (fun t => Rabs t <= 355 / 65536 /\ Rabs (t - te) <= 65537 * Rpow2 (-77)).
{ rewrite Ek. cbn -[bpow]; unfold F2R; cbn -[bpow].
  unfold Rrnd.nearbyint, Rrnd.rnd, round_mode, Rrnd.Rnd.
  fold xR.
  rewrite round_FIX_IZR.
  set (k' := ZnearestE (Generic_fmt.round radix2 (FLT_exp Rrnd.emin Rrnd.prec) ZnearestE (xR * _))).
  replace (6243314768150528 * Rpow2 (-59)) with (47632711549 * Rpow2 (-42)) by (simpl; lra).
  rewrite <-Rmult_assoc, <-mult_IZR. split.
  2: { apply round_generic; [apply valid_rnd_N |]. apply generic_format_FLT.
    exists (Defs.Float radix2 (k' * 47632711549) (-42));
    unfold F2R; cbn; [easy | | easy]. apply lt_IZR.
    rewrite abs_IZR, mult_IZR. unfold k'. interval. }
    apply round_generic; [apply valid_rnd_N |].
    assert (Rabs xR <= 746) by interval.
    assert (Rabs xR <= /256 \/ /256 <= Rabs xR) as [H8 | H8] by lra.
    - replace k' with 0%Z by (apply eq_IZR, Rle_le_eq; unfold k'; interval).
      rewrite Rmult_0_l, Rminus_0_r. easy.
    - apply generic_format_FLT.
      exists (Defs.Float radix2 (Ztrunc (xR * Rpow2 60) - k' * 47632711549 * 262144) (-60)).
      3: easy.
      2: { cbn. apply lt_IZR. rewrite abs_IZR, minus_IZR, 2mult_IZR.
        cbn -[Rabs IZR Ztrunc Rmult Rminus Rlt].
        unfold k'. interval with (i_taylor xR). }
      unfold F2R; cbn.
      rewrite minus_IZR, Rmult_minus_distr_r. apply f_equal2.
      2: rewrite !mult_IZR; lra.
      change (generic_format radix2 (FIX_exp (-60)) xR). revert HxR.
      apply generic_inclusion_ge with (e1 := (-8)%Z); [| easy].
      unfold FIX_exp, FLT_exp. lia. }
{ unfold te. rewrite Hki. simpl P2M_list.
  rewrite Ek. simpl evalRounded.
  rewrite <-round_FIX_IZR with (f := ZnearestE).
  unfold Rrnd.nearbyint, round_mode.
  cbn -[bpow]; unfold F2R; cbn -[bpow].
  fold xR in Hxr_ |- *.
  rename k into k_.
  set (k := Generic_fmt.round radix2 (FIX_exp 0) ZnearestE (Rrnd.rnd (xR * _))).
  split. { unfold k, Rrnd.rnd, round_mode. interval with (i_taylor xR). }
  set (RLog2div64l := 8153543309409082 * Rpow2 (-98)).
  set (RLog2div64h := 6243314768150528 * Rpow2 (-59)).
  set (u := xR - k * _ - _).
  set (delt1 := Rrnd.rnd u - u).
  set (delt2 := Rrnd.rnd (k * RLog2div64l) - k * RLog2div64l).
  replace (Rrnd.rnd u - (xR - k * (Rpower.ln 2 / 64)))
    with (delt1 - delt2 - k * (RLog2div64h + RLog2div64l - Rpower.ln 2 / 64))
    by (unfold delt1, delt2, u; ring).
  unfold Rrnd.rnd, round_mode in delt1, delt2, k, u.
  interval with (i_taylor xR, i_prec 120). }
intros t' [b_t err_t] Ft _.
set (t := SF2R radix2 (Prim2SF t')).

change (Papprox t') with (@evalPrim (BinFloat :: nil) _ g0 (t', tt)).
assert_float (fun y => Rabs y <= 0.0055 /\ Rabs (1 + y - Rtrigo_def.exp t) <= 11 * Rpow2 (-62)).
{ cbn -[bpow].
  unfold Rrnd.rnd, Rrnd.emin, round_mode, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax.
  split.
  - interval.
  - fold t in b_t |- *.
    interval with (i_taylor t, i_bisect t, i_prec 80). }
intros y' [b_y Hy] Fy _.
set (y := SF2R radix2 (Prim2SF y')).

set (penult := @Op (BinFloat :: BinFloat :: BinFloat :: nil) BinFloat ADD (Op MUL (Var 0) (Var 1)) (Var 2)).
change (_ * _ + dlb)%float with (evalPrim penult (C', (y', (dlb, tt)))).
change (_ * _ + dub)%float with (evalPrim penult (C', (y', (dub, tt)))).

set (xred := xR - IZR (to_Z kq) * Rpower.ln 2).
assert (Exred: xred = (t - (t - te) + IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64))).
{ unfold xred, te, kr. rewrite (asr_land ki 6) by easy. rewrite plus_IZR, mult_IZR.
  change (lsl 1 6 - 1)%uint63 with 63%uint63. change (2 ^ Uint63.to_Z 6)%Z with 64%Z.
  fold xR kq. field. }

assert (Hxred : Rabs (xred - IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64)) <= 356 / 65536).
{ rewrite Exred.
  unfold Rminus at 1. rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r. revert err_t.
  fold t. generalize (t - te). intros r Hr. interval. }

assert (Main :
  forall d : PrimFloat.float,
  is_finite_SF (Prim2SF d) = true -> Rabs (SF2R radix2 (Prim2SF d)) <= Rpow2 (-52) ->
  let z := evalPrim penult (C', (y', (d, tt))) in
  is_finite_SF (Prim2SF z) = true /\
  Rabs (SF2R radix2 (Prim2SF z)) <= 0.011 /\
  let Y := Rtrigo_def.exp (IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64)) + SF2R radix2 (Prim2SF z) in
  0.989 <= Y <= 1.99 /\
  Rabs (Y - (Rtrigo_def.exp xred + SF2R radix2 (Prim2SF d))) <= 0x1.24b34edb6f103p-57).
{
  clear d dlb dub Hdlb Hdub.
  intros d fin_d b_d.
  unfold penult.
  assert_float.
  intros z -> ->.
  apply (conj eq_refl).

  simpl in Hki.
  fold xR in xred, Hx, Hxr_, Hki |- *.
  clearbody xR.
  clear ki_ k0 x Fx Ek.
  simpl evalRounded.
  set (dR := SF2R radix2 (Prim2SF d)).
  fold dR C y in b_d |- *.
  clearbody dR.
  clear d fin_d.

  cbn -[bpow consts Uint63.to_Z kr]. unfold Rrnd.rnd, Rrnd.maxval, round_mode,
    Rrnd.emin, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax, Rrnd.maxval.
  split. { interval. }
  split. { rewrite <- Hkr1. interval. }

  rewrite Exred.
  fold y.
  set (eps := 1 + y - Rtrigo_def.exp t).
  replace y with (Rtrigo_def.exp t - 1 + eps) by (unfold eps; ring).
  fold y eps in Hy. clearbody eps.
  fold C.
  set (Y1 := C * _). set (Y2 := Generic_fmt.round _ _ _ Y1). set (Y3 := Y2 + _).
  set (Y4 := Generic_fmt.round _ _ _ _).

  rewrite exp_plus. unfold Rminus at 2. rewrite exp_plus.
  replace (_ - _) with ((Y4 - Y3) + (Y2 - Y1)
    + (Rtrigo_def.exp t - 1) * (C - Rtrigo_def.exp (IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64)))
    - (Rtrigo_def.exp (- (t - te)) - 1) * Rtrigo_def.exp (IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64)) * Rtrigo_def.exp t
    + C * eps) by
   (unfold Y4, Y3, Y2, Y1; ring).

  revert HC2. fold C. generalize (C - Rtrigo_def.exp (IZR (Uint63.to_Z kr) * (Rpower.ln 2 / 64))). intros r Hr.
  unfold Y4, Y3, Y2, Y1.
  rewrite <- Hkr1.
  rewrite exp_Ropp.
  revert err_t. fold t. generalize (t - te). intros r0 Hr0.
  interval with (i_prec 100).
}

assert (Hb : forall d,
  is_finite_SF (Prim2SF d) = true ->
  Rabs (SF2R radix2 (Prim2SF d)) = 0x1.25p-57 ->
  Rabs (Rrnd.rnd (Rrnd.rnd (SF2R radix2 (Prim2SF C') + SF2R radix2 (Prim2SF (evalPrim penult (C', (y', (d, tt)))))) *
      Rpow2 (to_Z kq))) < 9007199254740991 * Rpow2 971).
{ intros d' Hd1 Hd2.
  refine (_ (Main d' Hd1 _)).
  2: rewrite Hd2 ; interval.
  clear Main.
  set (y'' := evalPrim penult _).
  intros [_ [_ [Hb2 Hb3]]].
  simpl evalRounded.
  revert Hx Hd2 Hb2 Hb3 Hki2 HC2.
  unfold xred. fold C.
  clear.
  set (Y := Rtrigo_def.exp _ + _). set (delt := C - _).
  intros [_ Hx] Hd2 HY'' HY' [_ Hkq] Hdelt. unfold Rrnd.rnd, round_mode.
  replace (C + _) with (Y + delt) by (unfold Y, delt; ring).
  unfold Rminus at 2 in HY'. rewrite exp_plus, exp_Ropp in HY'.
  replace (Rtrigo_def.exp (_ * _)) with (Rpow2 (to_Z kq)) in HY' by now rewrite bpow_exp.
  assert (Haux := bpow_gt_0 radix2 (to_Z kq)).
  replace (Y - _) with ((Y * Rpow2 (to_Z kq) - Rtrigo_def.exp xR) / Rpow2 (to_Z kq) - SF2R radix2 (Prim2SF d'))
    in HY' by (field; lra).
  refine (_ (Rle_trans _ _ _ ltac:(apply Rabs_triang_inv) HY')).
  intros HY. clear HY'. apply Rcomplements.Rle_minus_l in HY.
  rewrite Hd2, Rcomplements.Rabs_div in HY by apply Rgt_not_eq, bpow_gt_0.
  assert (Hkq' : 0 <= Rpow2 (to_Z kq) <= Rpow2 1024).
  { split. apply bpow_ge_0. now apply bpow_le. }
  apply -> Rcomplements.Rle_div_l in HY ; [| now apply Rabs_gt; right].
  apply (Rle_trans _ _ (0x1.8p-56 * Rpow2 1024)) in HY.
  2: { apply Rmult_le_compat; [ interval | apply Rabs_pos | interval |].
    now rewrite Rabs_pos_eq by lra. }
  unfold emax.
  assert (Hx' : 0 <= Rtrigo_def.exp xR <= Rpow2 1024 - Rpow2 978) by interval with (i_prec 60).
  change (Generic_fmt.round _ _ _) with Rrnd.rnd.
  set (delt1 := Rrnd.rnd (Y + delt) - (Y + delt)).
  set (delt2 :=
      Rrnd.rnd (Rrnd.rnd (Y + delt) * Rpow2 (to_Z kq))
    - Rrnd.rnd (Y + delt) * Rpow2 (to_Z kq)).
  replace (Rrnd.rnd (_ * _)) with
   (delt2 + delt1 * Rpow2 (to_Z kq)
    + (Y * Rpow2 (to_Z kq) - Rtrigo_def.exp xR)
    + Rtrigo_def.exp xR + delt * Rpow2 (to_Z kq))
    by (unfold delt1, delt2; ring).
  revert HY. generalize (Y * Rpow2 (to_Z kq) - Rtrigo_def.exp xR). intros r Hr.
  unfold Rrnd.rnd, round_mode in delt1, delt2.
  interval with (i_prec 60). }

assert (Haux_ : forall d,
    is_finite_SF (Prim2SF d) = true ->
    Rabs (SF2R radix2 (Prim2SF d)) <= 0x1p-52 ->
    Uint63.to_Z kr <> 0%Z ->
    1.001 <= C + SF2R radix2 (Prim2SF (evalPrim penult (C', (y', (d, tt))))) <= 1.999).
{ intros d' Hd1 Hd2 Hkz.
  refine (_ (Main d' Hd1 _)).
  2: interval.
  set (y'' := evalPrim penult _).
  intros [_ [_ [_ Hb3]]].
  replace (_ + _) with (C - Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64))
      + (Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)) +
          SF2R radix2 (Prim2SF y'') -
          (Rtrigo_def.exp (xR - IZR (to_Z kq) * Rpower.ln 2) + SF2R radix2 (Prim2SF d')))
      + Rtrigo_def.exp (xR - IZR (to_Z kq) * Rpower.ln 2) + SF2R radix2 (Prim2SF d')) by ring.
  revert Hb3 HC2. fold C xred.
  generalize (C - Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64))).
  generalize (Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)) +
      SF2R radix2 (Prim2SF y'') -
     (Rtrigo_def.exp xred + SF2R radix2 (Prim2SF d'))).
  intros r0 r1 Hr0 Hr1.
  unfold xred.
  replace (xR - IZR (to_Z kq) * Rpower.ln 2) with
    (xR - IZR (to_Z kq) * Rpower.ln 2 - IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)
     + IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)) by ring.
  revert Hxred.
  unfold xred.
  generalize (xR - IZR (to_Z kq) * Rpower.ln 2 - IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)).
  intros r2 Hr2.
  assert (Hkr_ : 1 <= IZR (Uint63.to_Z kr) <= 63).
  { rewrite Hkr1 in Hkr0. split; apply IZR_le; [lia | easy]. }
  interval. }

split.

{ generalize (Main dlb eq_refl ltac:(cbn; interval)).
  set (y'' := evalPrim penult _).
  intros [Hlb1 [Hlb4 [Hlb2 Hlb3]]].
  fold k0 kr in Hlb1, Hlb2, Hlb3, Hlb4.

generalize (Bldexp_correct _ _ Hprec Hmax mode_NE (Prim2B (C' + y'')) (to_Z (ki >> 6))).
specialize (Hb dlb eq_refl (eq_sym Hdlb)).
rewrite <- Prim2SF2R_Prim2B2R.
change (C' + y'')%float with
  (@evalPrim (BinFloat :: BinFloat :: nil) BinFloat (Op ADD (Var 0) (Var 1)) (C', (y'', tt))).
assert_float.
intros p Fp Ep.
rewrite Rlt_bool_true.
2: { rewrite Ep. apply Rlt_le_trans with (1 := Hb). interval with (i_prec 60). }
set (f := Bldexp _ _ _). intros [Heq [Hfin _]].
refine (_ (Bpred_correct prec emax Hprec Hmax f _)).
2: { now rewrite Hfin, <- is_finite_SF_B2SF, B2SF_Prim2B. }
rewrite Heq.
case Rlt_bool_spec.
2: { intros _ H. now rewrite <- (SF2B'_B2SF (Bpred f)), H. }
intros _ [Heqpred [Hfinpred _]].

replace (Beqb _ _) with false.
2: { simpl. unfold Beqb, SFeqb, SFcompare. now destruct Bpred. }

rewrite PrimitiveFloat.B2R_BtoX, Heqpred by easy.
split. easy.
rewrite Ep. clear Hb Fp Ep. clear dependent f. simpl evalRounded.
fold C in bnd_C, HC1, HC2 |- *. clearbody C.
eapply Rle_trans. apply pred_FLT_shift_le. easy. apply valid_rnd_round_mode.
apply generic_format_round. now apply FLT_exp_valid. apply valid_rnd_round_mode.
unfold Rrnd.rnd, round_mode. interval.
apply Rmult_le_reg_r with (Rpow2 (- to_Z kq)). { apply bpow_gt_0. }
rewrite Rmult_assoc. rewrite <-bpow_plus. rewrite Z.add_opp_diag_r, Rmult_1_r.
rewrite bpow_exp, <-exp_plus, opp_IZR. change (IZR radix2) with 2.
replace (Rtrigo_def.exp _) with (C + SF2R radix2 (Prim2SF y'')
  - (C - Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)))
  - (Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64))
      + SF2R radix2 (Prim2SF y'')
      - (Rtrigo_def.exp (xR + - IZR (to_Z kq) * Rpower.ln 2) + SF2R radix2 (Prim2SF dlb)))
  - SF2R radix2 (Prim2SF dlb)) by ring.
generalize Hlb3. unfold xred, Rminus at 2. rewrite Ropp_mult_distr_l.
fold xR.
generalize (Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)) +
   SF2R radix2 (Prim2SF y'') -
   (Rtrigo_def.exp (xR + - IZR (to_Z kq) * Rpower.ln 2) + SF2R radix2 (Prim2SF dlb))).
intros r Hr. unfold Rrnd.rnd, round_mode.
destruct (Z.eq_dec (Uint63.to_Z kr) 0) as [Hkr | Hkr].
- rewrite Hkr at 1. rewrite HC1 at 1 2 3 by easy.
  rewrite Rmult_0_l, exp_0, Rminus_eq_0, Rminus_0_r.
  apply Rle_trans with (1 + SF2R radix2 (Prim2SF y'')).
  { apply pred_round_le_id. now apply FLT_exp_valid. apply valid_rnd_N. }
  apply Rminus_le. ring_simplify. cbn -[bpow]. interval.
- apply pred_round_N_le with (e := 1%Z).
  now apply FLT_exp_valid.
  generalize (Haux_ dlb eq_refl ltac:(rewrite <- Hdlb; interval) Hkr).
  fold y''. generalize (C + SF2R radix2 (Prim2SF y'')). intros r0 Hr0. interval.
  revert HC2. generalize (C - Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64))). intros r0 Hr0.
  ring_simplify. cbn -[bpow]. interval. }

clear dlb Hdlb.

generalize (Main dub eq_refl ltac:(cbn; interval)).
set (y'' := evalPrim penult _).
intros [Hub1 [Hub4 [Hub2 Hub3]]].
fold k0 kr in Hub1, Hub2, Hub3, Hub4.

generalize (Bldexp_correct _ _ Hprec Hmax mode_NE (Prim2B (C' + y'')) (to_Z (ki >> 6))).
specialize (Hb dub eq_refl (eq_sym Hdub)).
rewrite <- Prim2SF2R_Prim2B2R.
change (C' + y'')%float with
 (@evalPrim (BinFloat :: BinFloat :: nil) BinFloat (Op ADD (Var 0) (Var 1)) (C', (y'', tt))).
assert_float.
intros p Fp Ep.
rewrite Rlt_bool_true.
2: { rewrite Ep. apply Rlt_le_trans with (1 := Hb). interval with (i_prec 60). }
set (f := Bldexp _ _ _). intros [Heq [Hfin _]].
refine (_ (Bsucc_correct prec emax Hprec Hmax f _)).
2: { now rewrite Hfin, <- is_finite_SF_B2SF, B2SF_Prim2B. }
rewrite Heq.
case Rlt_bool_spec.
2: { intros _ H. now rewrite <- (SF2B'_B2SF (Bsucc f)), H. }
intros _ [Heqsucc [Hfinsucc _]].

replace (Beqb _ _) with false.
2: { simpl. unfold Beqb, SFeqb, SFcompare. now destruct Bsucc. }

rewrite PrimitiveFloat.B2R_BtoX, Heqsucc by easy.
split. easy.
rewrite Ep. clear Hb Ep Fp. clear dependent f. simpl evalRounded.
fold C in bnd_C, HC1, HC2 |- *. clearbody C.
eapply Rle_trans ; cycle 1. apply succ_FLT_shift_ge. easy. apply valid_rnd_round_mode.
apply generic_format_round. now apply FLT_exp_valid. apply valid_rnd_round_mode.
unfold Rrnd.rnd, round_mode. interval.
apply Rmult_le_reg_r with (Rpow2 (- to_Z kq)). { apply bpow_gt_0. }
rewrite Rmult_assoc. rewrite <-bpow_plus. rewrite Z.add_opp_diag_r, Rmult_1_r.
rewrite bpow_exp, <-exp_plus, opp_IZR. change (IZR radix2) with 2.
replace (Rtrigo_def.exp _) with (C + SF2R radix2 (Prim2SF y'')
  - (C - Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)))
  - (Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64))
      + SF2R radix2 (Prim2SF y'')
      - (Rtrigo_def.exp (xR + - IZR (to_Z kq) * Rpower.ln 2) + SF2R radix2 (Prim2SF dub)))
  - SF2R radix2 (Prim2SF dub)) by ring.
generalize Hub3. unfold xred, Rminus at 2. rewrite Ropp_mult_distr_l.
fold xR.
generalize (Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64)) +
   SF2R radix2 (Prim2SF y'') -
   (Rtrigo_def.exp (xR + - IZR (to_Z kq) * Rpower.ln 2) + SF2R radix2 (Prim2SF dub))).
intros r Hr. unfold Rrnd.rnd, round_mode.
destruct (Z.eq_dec (Uint63.to_Z kr) 0) as [Hkr | Hkr].
- rewrite Hkr at 1. rewrite HC1 at 1 2 3 by easy.
  rewrite Rmult_0_l, exp_0, Rminus_eq_0, Rminus_0_r.
  apply Rle_trans with (1 + SF2R radix2 (Prim2SF y'')).
  2: { apply succ_round_ge_id. now apply FLT_exp_valid. apply valid_rnd_N. }
  apply Rminus_le. ring_simplify. cbn -[bpow]. interval.
- apply succ_round_N_ge with (e := 1%Z).
  now apply FLT_exp_valid.
  generalize (Haux_ dub eq_refl ltac:(rewrite <- Hdub; interval) Hkr).
  fold y''. generalize (C + SF2R radix2 (Prim2SF y'')). intros r0 Hr0. interval.
  revert HC2. generalize (C - Rtrigo_def.exp (IZR φ (kr)%uint63 * (Rpower.ln 2 / 64))). intros r0 Hr0.
  ring_simplify. cbn -[bpow]. interval.
Qed.

End ExpImpl.

Import ExpImpl.

Definition exp (prec : F.precision) xi :=
  let aux x :=
    let k0 := (x * InvLog2_64 + 0x1.8p52)%float in let kf := (k0 - 0x1.8p52)%float in
    let tf := (x - kf * Log2div64h - kf * Log2div64l)%float in
    let ki := (normfr_mantissa (fst (frshiftexp k0)) - 6755399440921280)%uint63 in
    let C := consts.[PrimInt63.land ki 63] in
    let kq := PrimInt63.asr ki 6 in let y := (C * Papprox tf)%float in
    (C, y, kq) in
  match xi with
  | Ibnd xl xu =>
    Ibnd
     (if F.real xl then
        if PrimFloat.ltb xl (-0x1.74385446d71c4p9)%float then 0%float else
        if PrimFloat.ltb 0x1.62e42fefa39efp9%float xl then 0x1.fffffffffffffp1023%float else
        let '(C, y, kq) := aux xl in
        next_down (ldshiftexp (C + (y + -0x1.25p-57))%float kq)
      else 0%float)
     (if F.real xu then
        if PrimFloat.ltb xu (-0x1.74385446d71c4p9)%float then 0x1p-1074%float else
        if PrimFloat.ltb 0x1.62e42fefa39efp9%float xu then infinity else
        let '(C, y, kq) := aux xu in
        next_up (ldshiftexp (C + (y + 0x1.25p-57))%float kq)
      else nan)
  | Inan => Inan
  end.

Theorem exp_correct :
  forall prec, extension Xexp (exp prec).
Proof.
intros prec [|xl xu].
easy.
intros [|x].
now simpl; case (_ && _)%bool.
unfold convert at 1.
case_eq (F.valid_lb xl); [|intros _ [H0 H1]; lra].
case_eq (F.valid_ub xu); [|intros _ _ [H0 H1]; lra].
intros Vxu Vxl [Hxl Hxu].
simpl.
assert (Hl := fun H => proj1 (exp_aux_correct xl H)).
assert (Hu := fun H => proj2 (exp_aux_correct xu H)).
rewrite <- PrimitiveFloat.real_is_finite, F.real_correct, B2Prim_Prim2B in Hl.
rewrite <- PrimitiveFloat.real_is_finite, F.real_correct, B2Prim_Prim2B in Hu.
set (l := if F.real xl then _ else _).
set (u := if F.real xu then _ else _).
assert (Vl : F.valid_lb l = true).
{ unfold l. clear l u.
  rewrite F.real_correct.
  destruct (F.toX xl) as [|rxl].
  easy.
  specialize (Hl eq_refl).
  revert Hl.
  unfold exp_aux.
  destruct PrimFloat.ltb.
  easy.
  now destruct PrimFloat.ltb. }
assert (Vu : F.valid_ub u = true).
{ unfold u. clear l u Vl.
  rewrite F.real_correct.
  destruct (F.toX xu) as [|rxu].
  easy.
  specialize (Hu eq_refl).
  revert Hu.
  unfold exp_aux.
  destruct PrimFloat.ltb.
  easy.
  now destruct PrimFloat.ltb. }
rewrite Vl, Vu; unfold l, u.
split.
- clear u Hxu Hu Vu.
  rewrite F.real_correct.
  assert (Hxl' := PrimitiveFloat.toX_Prim2B xl).
  destruct (F.toX xl) as [|rxl].
  apply Rlt_le, exp_pos.
  apply eq_sym, PrimitiveFloat.BtoX_B2R in Hxl'.
  specialize (Hl eq_refl).
  revert Hl.
  unfold exp_aux.
  intros [_ H].
  destruct PrimFloat.ltb.
  apply Rle_trans with (1 := H).
  apply Raux.exp_le.
  now rewrite <- Hxl'.
  destruct PrimFloat.ltb.
  apply Rle_trans with (1 := H).
  apply Raux.exp_le.
  now rewrite <- Hxl'.
  revert H.
  set (yl := next_down _).
  simpl.
  destruct F.toX as [|ryl].
  easy.
  intros H.
  apply Rle_trans with (1 := H).
  apply Raux.exp_le.
  now rewrite <- Hxl'.
- clear l Hxl Hl Vl.
  rewrite F.real_correct.
  assert (Hxu' := PrimitiveFloat.toX_Prim2B xu).
  destruct (F.toX xu) as [|rxu].
  easy.
  apply eq_sym, PrimitiveFloat.BtoX_B2R in Hxu'.
  specialize (Hu eq_refl).
  revert Hu.
  unfold exp_aux.
  intros [_ H].
  destruct PrimFloat.ltb.
  apply Rle_trans with (2 := H).
  apply Raux.exp_le.
  now rewrite <- Hxu'.
  destruct PrimFloat.ltb.
  easy.
  revert H.
  set (yl := next_up _).
  simpl.
  destruct F.toX as [|ryu].
  easy.
  intros H.
  apply Rle_trans with (2 := H).
  apply Raux.exp_le.
  now rewrite <- Hxu'.
Qed.

End PrimFloatIntervalFull.
