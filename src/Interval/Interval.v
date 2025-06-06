(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: https://coqinterval.gitlabpages.inria.fr/

Copyright (C) 2007-2016, Inria

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

From Coq Require Import Bool Reals Psatz.
From Coquelicot Require Import Coquelicot.

Require Import Stdlib.
Require Import Xreal.
Require Import Basic.

Inductive interval : Set :=
  | Inan : interval
  | Ibnd (l u : ExtendedR) : interval.

Definition Xlower (xi : interval) : ExtendedR :=
  match xi with
  | Ibnd xl _ => xl
  | _ => Xnan
  end.

Definition Xupper (xi : interval) : ExtendedR :=
  match xi with
  | Ibnd _ xu => xu
  | _ => Xnan
  end.

Definition contains i v :=
  match i, v with
  | Ibnd l u, Xreal x =>
    match l with
    | Xreal r => Rle r x
    | Xnan => True
    end /\
    match u with
    | Xreal r => Rle x r
    | Xnan => True
    end
  | Inan, _ => True
  | _, Xnan => False
  end.

Inductive output_bound : Set :=
  | BInteger : Z -> output_bound
  | BDecimal : QArith_base.Q -> output_bound
  | BFraction : Z -> Z -> output_bound.

Definition convert_bound b :=
  match b with
  | BInteger n => IZR n
  | BDecimal q => Q2R q
  | BFraction n d => (IZR n / IZR d)%R
  end.

Definition contains_output xi x :=
  match xi with
  | (None, None) => True
  | (None, Some xu) => (x <= convert_bound xu)%R
  | (Some xl, None) => (convert_bound xl <= x)%R
  | (Some xl, Some xu) => (convert_bound xl <= x <= convert_bound xu)%R
  end.

Lemma contains_connected :
  forall xi, connected (fun x => contains xi (Xreal x)).
Proof.
intros [|l u] a b Ha Hb x Hx.
exact I.
split.
destruct l as [|l].
exact I.
exact (Rle_trans _ _ _ (proj1 Ha) (proj1 Hx)).
destruct u as [|u].
exact I.
exact (Rle_trans _ _ _ (proj2 Hx) (proj2 Hb)).
Qed.

Lemma contains_Xnan :
  forall xi, contains xi Xnan <-> xi = Inan.
Proof.
intros xi.
now case xi ; split.
Qed.

Lemma contains_Inan :
  forall xi x, xi = Inan -> contains xi x.
Proof.
now intros xi x ->.
Qed.

Lemma contains_le :
  forall xl xu v,
  contains (Ibnd xl xu) v ->
  le_lower xl v /\ le_upper v xu.
Proof.
intros xl xu v.
case v.
intro.
elim H.
intros r.
case xl.
intro.
exact H.
intros l (Hl, Hu).
split.
exact (Ropp_le_contravar _ _ Hl).
exact Hu.
Qed.

Lemma le_contains :
  forall xl xu v,
  le_lower xl (Xreal v) -> le_upper (Xreal v) xu ->
  contains (Ibnd xl xu) (Xreal v).
Proof.
intros xl xu v.
case xl.
intros _ Hu.
exact (conj I Hu).
intros l Hl Hu.
split.
exact (Ropp_le_cancel _ _ Hl).
exact Hu.
Qed.

Definition subset xi yi :=
  match xi, yi with
  | Ibnd xl xu, Ibnd yl yu =>
    match xl, xu with
    | Xreal xl, Xreal xu => (xu < xl)%R
    | _, _ => False
    end
    \/ (le_lower yl xl /\ le_upper xu yu)
  | _, Inan => True
  | _, _ => False
  end.

Definition subset' xi yi :=
  forall x, contains xi x -> contains yi x.

Theorem subset_contains :
  forall xi yi,
  subset xi yi ->
  subset' xi yi.
Proof.
intros xi yi.
destruct yi as [|yl yu].
easy.
destruct xi as [|xl xu].
easy.
intros H [|v] Hv.
easy.
destruct H as [H|[H1 H2]].
{ destruct xl as [|xl]. easy.
  destruct xu as [|xu]. easy.
  simpl in Hv. lra. }
apply contains_le in Hv.
apply le_contains.
now apply le_lower_trans with (1 := H1).
now apply le_upper_trans with (2 := H2).
Qed.

Definition domain' P b :=
  forall x, contains b (Xreal x) -> P x.

Theorem bisect' :
  forall P xl xm xu,
  domain' P (Ibnd xl xm) ->
  domain' P (Ibnd xm xu) ->
  domain' P (Ibnd xl xu).
Proof.
intros P xl xm xu Hl Hu x H.
elim H.
case_eq xm ; intros.
apply Hu.
rewrite H0.
exact (conj I (proj2 H)).
case (Rle_dec x r) ; intros Hr.
apply Hl.
apply le_contains.
exact (proj1 (contains_le _ _ _ H)).
rewrite H0.
exact Hr.
apply Hu.
apply le_contains.
rewrite H0.
unfold le_lower.
simpl.
apply Ropp_le_contravar.
auto with real.
exact (proj2 (contains_le _ _ _ H)).
Qed.

Definition not_empty xi :=
  exists v, contains xi (Xreal v).

Lemma contains_Xreal :
  forall xi x,
  contains xi x ->
  contains xi (Xreal (proj_val x)).
Proof.
intros xi [|x].
now destruct xi.
easy.
Qed.

Lemma not_empty_contains :
  forall xi x,
  contains xi x ->
  not_empty xi.
Proof.
intros xi x Hx.
exists (proj_val x).
now apply contains_Xreal.
Qed.

Lemma contains_lower :
  forall l u x,
  contains (Ibnd (Xreal l) u) x ->
  contains (Ibnd (Xreal l) u) (Xreal l).
Proof.
intros.
split.
apply Rle_refl.
destruct x as [|x].
elim H.
destruct u as [|u].
exact I.
apply Rle_trans with (1 := proj1 H) (2 := proj2 H).
Qed.

Lemma contains_upper :
  forall l u x,
  contains (Ibnd l (Xreal u)) x ->
  contains (Ibnd l (Xreal u)) (Xreal u).
Proof.
intros.
split.
destruct x as [|x].
elim H.
destruct l as [|l].
exact I.
apply Rle_trans with (1 := proj1 H) (2 := proj2 H).
apply Rle_refl.
Qed.

Module Type IntervalBounds.

Parameter type : Type.
Parameter nan : type.
Parameter convert : type -> ExtendedR.
Parameter precision : Type.
Parameter PtoP : positive -> precision.

End IntervalBounds.

Module Type IntervalBasicOps.

Declare Module F : IntervalBounds.

Parameter type : Type.
Parameter valid_lb : F.type -> Prop.
Parameter valid_ub : F.type -> Prop.
Parameter convert : type -> interval.
Parameter zero : type.
Parameter nai : type.
Parameter empty : type.
Parameter bnd : F.type -> F.type -> type.
Parameter singleton : F.type -> type.
Parameter real : type -> bool.
Parameter is_empty : type -> bool.

Parameter valid_lb_real :
  forall b, F.convert b = Xreal (proj_val (F.convert b)) -> valid_lb b.

Parameter valid_ub_real :
  forall b, F.convert b = Xreal (proj_val (F.convert b)) -> valid_ub b.

Parameter valid_lb_nan : valid_lb F.nan.

Parameter valid_ub_nan : valid_ub F.nan.

Parameter bnd_correct :
  forall l u, valid_lb l -> valid_ub u ->
  convert (bnd l u) = Ibnd (F.convert l) (F.convert u).

Parameter singleton_correct :
  forall b,
  contains (convert (singleton b)) (Xreal (proj_val (F.convert b))).

Parameter zero_correct :
  convert zero = Ibnd (Xreal 0) (Xreal 0).

Parameter nai_correct :
  convert nai = Inan.

Parameter empty_correct :
  forall x, contains (convert empty) x -> False.

Parameter real_correct :
  forall xi, real xi = match convert xi with Inan => false | _ => true end.

Parameter is_empty_correct :
  forall xi x, contains (convert xi) x ->
  is_empty xi = true -> False.

Parameter output : bool -> type -> option output_bound * option output_bound.

Parameter output_correct :
  forall fmt xi x, contains (convert xi) (Xreal x) -> contains_output (output fmt xi) x.

Parameter subset : type -> type -> bool.

Parameter subset_correct :
  forall xi yi v,
  contains (convert xi) v ->
  subset xi yi = true ->
  contains (convert yi) v.

Parameter join : type -> type -> type.
Parameter meet : type -> type -> type.
Parameter sign_large : type -> Xcomparison.
Parameter sign_strict : type -> Xcomparison.

Parameter sign_large_correct :
  forall xi,
  match sign_large xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rle 0 (proj_val x)
  | Xund => True
  end.

Parameter sign_strict_correct :
  forall xi,
  match sign_strict xi with
  | Xeq => forall x, contains (convert xi) x -> x = Xreal 0
  | Xlt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rlt (proj_val x) 0
  | Xgt => forall x, contains (convert xi) x -> x = Xreal (proj_val x) /\ Rlt 0 (proj_val x)
  | Xund => True
  end.

Parameter join_correct :
  forall xi yi v,
  contains (convert xi) v \/ contains (convert yi) v ->
  contains (convert (join xi yi)) v.

Parameter meet_correct :
  forall xi yi v,
  contains (convert xi) v -> contains (convert yi) v ->
  contains (convert (meet xi yi)) v.

Parameter meet_correct' :
  forall xi yi v,
  contains (convert (meet xi yi)) v ->
  contains (convert xi) v /\ contains (convert yi) v.

Parameter midpoint : type -> F.type.

Parameter midpoint_correct :
  forall xi,
  not_empty (convert xi) ->
  F.convert (midpoint xi) = Xreal (proj_val (F.convert (midpoint xi))) /\
  contains (convert xi) (F.convert (midpoint xi)).

Parameter bisect : type -> type * type.

Parameter bisect_correct :
  forall xi x,
  contains (convert xi) x ->
  contains (convert (fst (bisect xi))) x \/ contains (convert (snd (bisect xi))) x.

Definition extension f fi := forall b x,
  contains (convert b) x -> contains (convert (fi b)) (f x).

Definition extension_2 f fi := forall ix iy x y,
  contains (convert ix) x ->
  contains (convert iy) y ->
  contains (convert (fi ix iy)) (f x y).

Parameter mask : type -> type -> type.

Parameter mask_correct : extension_2 Xmask mask.
Parameter mask_correct' :
  forall xi yi x,
  contains (convert xi) x ->
  contains (convert (mask xi yi)) x.

Definition precision := F.precision.

Parameter wider : precision -> type -> type -> bool.

Parameter neg : type -> type.
Parameter abs : type -> type.
Parameter inv : precision -> type -> type.
Parameter invnz : precision -> type -> type.
Parameter sqr : precision -> type -> type.
Parameter sqrt : precision -> type -> type.
Parameter add : precision -> type -> type -> type.
Parameter sub : precision -> type -> type -> type.
Parameter mul : precision -> type -> type -> type.
Parameter div : precision -> type -> type -> type.
Parameter power_int : precision -> type -> Z -> type.
Parameter nearbyint : rounding_mode -> type -> type.
Parameter error_fix : precision -> rounding_mode -> Z -> type -> type.
Parameter error_flt : precision -> rounding_mode -> Z -> positive -> type -> type.

Parameter neg_correct : extension Xneg neg.
Parameter abs_correct : extension Xabs abs.
Parameter inv_correct : forall prec, extension Xinv (inv prec).
Parameter sqr_correct : forall prec, extension Xsqr (sqr prec).
Parameter sqrt_correct : forall prec, extension Xsqrt (sqrt prec).
Parameter add_correct : forall prec, extension_2 Xadd (add prec).
Parameter sub_correct : forall prec, extension_2 Xsub (sub prec).
Parameter mul_correct : forall prec, extension_2 Xmul (mul prec).
Parameter div_correct : forall prec, extension_2 Xdiv (div prec).
Parameter power_int_correct : forall prec n, extension (fun x => Xpower_int x n) (fun x => power_int prec x n).
Parameter nearbyint_correct : forall mode, extension (Xnearbyint mode) (nearbyint mode).
Parameter error_fix_correct : forall prec mode emin, extension (Xerror_fix mode emin) (error_fix prec mode emin).
Parameter error_flt_correct : forall prec mode emin p, extension (Xerror_flt mode emin p) (error_flt prec mode emin p).

Parameter neg_correct' :
  forall xi x,
  contains (convert (neg xi)) (Xneg x) ->
  contains (convert xi) x.

Parameter invnz_correct :
  forall prec xi x,
  x <> Xreal 0 -> contains (convert xi) x -> contains (convert (invnz prec xi)) (Xinv x).

Parameter cancel_add : precision -> type -> type -> type.
Parameter cancel_sub : precision -> type -> type -> type.

Parameter bounded : type -> bool.
Parameter lower_bounded : type -> bool.
Parameter upper_bounded : type -> bool.

Parameter lower_extent : type -> type.
Parameter upper_extent : type -> type.
Parameter whole : type.

Parameter lower_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (x <= y)%R ->
  contains (convert (lower_extent xi)) (Xreal x).

Parameter upper_extent_correct :
  forall xi x y,
  contains (convert xi) (Xreal y) ->
  (y <= x)%R ->
  contains (convert (upper_extent xi)) (Xreal x).

Parameter whole_correct :
  forall x,
  contains (convert whole) (Xreal x).

Parameter lower_complement : type -> type.
Parameter upper_complement : type -> type.

Parameter lower_complement_correct :
  forall xi x y,
  contains (convert xi) (Xreal x) ->
  contains (convert (lower_complement xi)) (Xreal y) ->
  (y <= x)%R.

Parameter upper_complement_correct :
  forall xi x y,
  contains (convert xi) (Xreal x) ->
  contains (convert (upper_complement xi)) (Xreal y) ->
  (x <= y)%R.

Parameter lower : type -> F.type.
Parameter upper : type -> F.type.

Parameter lower_correct :
  forall xi : type,
  not_empty (convert xi) ->
  F.convert (lower xi) = Xlower (convert xi).

Parameter valid_lb_lower :
  forall xi : type,
  not_empty (convert xi) ->
  valid_lb (lower xi).

Parameter upper_correct :
  forall xi : type,
  not_empty (convert xi) ->
  F.convert (upper xi) = Xupper (convert xi).

Parameter valid_ub_upper :
  forall xi : type,
  not_empty (convert xi) ->
  valid_ub (upper xi).

Definition bounded_prop xi :=
  not_empty (convert xi) ->
  convert xi = Ibnd (F.convert (lower xi)) (F.convert (upper xi)).

Parameter lower_bounded_correct :
  forall xi,
  lower_bounded xi = true ->
  F.convert (lower xi) = Xreal (proj_val (F.convert (lower xi))) /\
  bounded_prop xi.

Parameter upper_bounded_correct :
  forall xi,
  upper_bounded xi = true ->
  F.convert (upper xi) = Xreal (proj_val (F.convert (upper xi))) /\
  bounded_prop xi.

Parameter bounded_correct :
  forall xi,
  bounded xi = true ->
  lower_bounded xi = true /\ upper_bounded xi = true.

Parameter fromZ_small : Z -> type.

Parameter fromZ_small_correct :
  forall v,
  (Z.abs v <= 256)%Z ->
  contains (convert (fromZ_small v)) (Xreal (IZR v)).

Parameter fromZ : precision -> Z -> type.

Parameter fromZ_correct :
  forall prec v, contains (convert (fromZ prec v)) (Xreal (IZR v)).

Definition propagate_l fi :=
  forall xi yi : type, convert xi = Inan -> convert (fi xi yi) = Inan.
Definition propagate_r fi :=
  forall xi yi : type, convert yi = Inan -> convert (fi xi yi) = Inan.

Parameter mask_propagate_l : propagate_l mask.
Parameter mask_propagate_r : propagate_r mask.
Parameter add_propagate_l : forall prec, propagate_l (add prec).
Parameter sub_propagate_l : forall prec, propagate_l (sub prec).
Parameter mul_propagate_l : forall prec, propagate_l (mul prec).
Parameter div_propagate_l : forall prec, propagate_l (div prec).
Parameter add_propagate_r : forall prec, propagate_r (add prec).
Parameter sub_propagate_r : forall prec, propagate_r (sub prec).
Parameter mul_propagate_r : forall prec, propagate_r (mul prec).
Parameter div_propagate_r : forall prec, propagate_r (div prec).

End IntervalBasicOps.

Module Type IntervalOps.

Include IntervalBasicOps.

Parameter pi : precision -> type.
Parameter cos : precision -> type -> type.
Parameter sin : precision -> type -> type.
Parameter tan : precision -> type -> type.
Parameter atan : precision -> type -> type.
Parameter exp : precision -> type -> type.
Parameter ln : precision -> type -> type.

Parameter pi_correct : forall prec, contains (convert (pi prec)) (Xreal PI).
Parameter cos_correct : forall prec, extension Xcos (cos prec).
Parameter sin_correct : forall prec, extension Xsin (sin prec).
Parameter tan_correct : forall prec, extension Xtan (tan prec).
Parameter atan_correct : forall prec, extension Xatan (atan prec).
Parameter exp_correct : forall prec, extension Xexp (exp prec).
Parameter ln_correct : forall prec, extension Xln (ln prec).

End IntervalOps.

Module IntervalBasicExt (I : IntervalBasicOps).

Lemma nai_correct :
  forall x, contains (I.convert I.nai) x.
Proof.
intros x.
now rewrite I.nai_correct.
Qed.

Lemma contains_le :
  forall xi x,
  contains (I.convert xi) x ->
  le_lower (I.F.convert (I.lower xi)) x /\ le_upper x (I.F.convert (I.upper xi)).
Proof.
intros xi x H.
assert (H' := not_empty_contains _ _ H).
rewrite I.lower_correct, I.upper_correct by easy.
destruct I.convert as [|xl xu].
easy.
now apply contains_le.
Qed.

Definition propagate fi :=
  forall xi, I.convert xi = Inan -> I.convert (fi xi) = Inan.

Lemma propagate_extension :
  forall fi f, I.extension (Xbind f) fi -> propagate fi.
Proof.
intros fi f Hf xi H.
specialize (Hf xi Xnan).
rewrite H in Hf.
specialize (Hf I).
clear -Hf.
now destruct I.convert.
Qed.

Lemma neg_propagate : propagate I.neg.
Proof.
apply propagate_extension with (1 := I.neg_correct).
Qed.

Lemma inv_propagate : forall prec, propagate (I.inv prec).
Proof.
intros prec.
apply propagate_extension with (1 := I.inv_correct prec).
Qed.

Lemma sqrt_propagate : forall prec, propagate (I.sqrt prec).
Proof.
intros prec.
apply propagate_extension with (1 := I.sqrt_correct prec).
Qed.

Lemma power_int_propagate : forall prec n, propagate (fun x => I.power_int prec x n).
Proof.
intros prec n.
apply propagate_extension with (1 := I.power_int_correct prec n).
Qed.

Lemma error_fix_propagate : forall prec mode emin, propagate (I.error_fix prec mode emin).
Proof.
intros prec mode emin.
apply propagate_extension with (1 := I.error_fix_correct prec mode emin).
Qed.

Lemma error_flt_propagate : forall prec mode emin p, propagate (I.error_flt prec mode emin p).
Proof.
intros prec mode emin p.
apply propagate_extension with (1 := I.error_flt_correct prec mode emin p).
Qed.

Definition extension f fi :=
  forall (xi : I.type) (x : R),
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (fi xi)) (Xreal (f x)).

Definition extension_2 f fi :=
  forall (xi yi : I.type) (x y : R),
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert yi) (Xreal y) ->
  contains (I.convert (fi xi yi)) (Xreal (f x y)).

Lemma neg_correct : extension Ropp I.neg.
Proof.
intros xi x.
now apply I.neg_correct.
Qed.

Lemma abs_correct : extension Rabs I.abs.
Proof.
intros xi x.
now apply I.abs_correct.
Qed.

Lemma inv_correct : forall prec, extension Rinv (I.inv prec).
Proof.
intros prec xi x Hx.
generalize (I.inv_correct prec xi _ Hx).
unfold Xinv', Xbind.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma invnz_correct :
  forall prec xi x,
  x <> 0%R ->
  contains (I.convert xi) (Xreal x) ->
  contains (I.convert (I.invnz prec xi)) (Xreal (/ x)).
Proof.
intros prec xi x Zx Hx.
refine (_ (I.invnz_correct prec xi _ _ Hx)).
unfold Xinv', Xbind.
now rewrite is_zero_false.
contradict Zx.
now injection Zx.
Qed.

Lemma sqr_correct : forall prec, extension Rsqr (I.sqr prec).
Proof.
intros prec xi x.
now apply I.sqr_correct.
Qed.

Lemma sqrt_correct : forall prec, extension sqrt (I.sqrt prec).
Proof.
intros prec xi x Hx.
generalize (I.sqrt_correct prec xi _ Hx).
unfold Xsqrt', Xbind.
case is_negative ; try easy.
Qed.

Lemma add_correct : forall prec, extension_2 Rplus (I.add prec).
Proof.
intros prec xi yi x y.
now apply I.add_correct.
Qed.

Lemma sub_correct : forall prec, extension_2 Rminus (I.sub prec).
Proof.
intros prec xi yi x y.
now apply I.sub_correct.
Qed.

Lemma mul_correct : forall prec, extension_2 Rmult (I.mul prec).
Proof.
intros prec xi yi x y.
now apply I.mul_correct.
Qed.

Lemma div_correct : forall prec, extension_2 Rdiv (I.div prec).
Proof.
intros prec xi yi x y Hx Hy.
generalize (I.div_correct prec _ _ _ _ Hx Hy).
simpl. unfold Xdiv'.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma nearbyint_correct :
  forall mode, extension (Rnearbyint mode) (I.nearbyint mode).
Proof.
intros mode xi x.
now apply I.nearbyint_correct.
Qed.

Definition round_fix prec mode emin xi :=
  I.add prec xi (I.error_fix prec mode emin xi).

Lemma round_fix_correct :
  forall mode prec emin, extension (Basic.round_fix mode emin) (round_fix prec mode emin).
Proof.
intros mode prec emin xi x Hx.
unfold round_fix.
replace (Basic.round_fix mode emin x)
  with (x + (Basic.round_fix mode emin x - x)) by ring.
apply add_correct; [easy| ].
now apply I.error_fix_correct with (x := Xreal x).
Qed.

Lemma round_fix_correct' :
  forall mode prec emin, I.extension (Xround_fix mode emin) (round_fix prec mode emin).
Proof.
unfold round_fix.
intros mode prec emin xi [ |x] Hx ; simpl.
- now apply contains_Xnan, I.add_propagate_l, contains_Xnan.
- replace (Basic.round_fix mode emin x)
    with (x + (Basic.round_fix mode emin x - x)) by ring.
  apply add_correct; [easy| ].
  now apply I.error_fix_correct with (x := Xreal x).
Qed.

Definition round_flt prec mode emin p xi :=
  I.add prec xi (I.error_flt prec mode emin p xi).

Lemma round_flt_correct :
  forall mode prec emin p, extension (Basic.round_flt mode emin p) (round_flt prec mode emin p).
Proof.
intros mode prec emin p xi x Hx.
unfold round_flt.
replace (Basic.round_flt mode emin p x)
  with (x + (Basic.round_flt mode emin p x - x)) by ring.
apply add_correct; [easy| ].
now apply I.error_flt_correct with (x := Xreal x).
Qed.

Lemma round_flt_correct' :
  forall mode prec emin p, I.extension (Xround_flt mode emin p) (round_flt prec mode emin p).
Proof.
unfold round_flt.
intros mode prec emin p xi [| x] Hx ; simpl.
- now apply contains_Xnan, I.add_propagate_l, contains_Xnan.
- replace (Basic.round_flt mode emin p x)
    with (x + (Basic.round_flt mode emin p x - x)) by ring.
  apply add_correct; [easy| ].
  now apply I.error_flt_correct with (x := Xreal x).
Qed.

Lemma power_int_correct :
  forall prec n, extension (fun x => powerRZ x n) (fun xi => I.power_int prec xi n).
Proof.
intros prec n xi x Hx.
generalize (I.power_int_correct prec n xi _ Hx).
unfold Xpower_int, Xpower_int', Xbind.
destruct n as [|n|n] ; try easy.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma zero_correct : contains (I.convert I.zero) (Xreal 0).
Proof.
rewrite I.zero_correct.
split ; apply Rle_refl.
Qed.

Lemma contains_only_0 r :
  contains (I.convert I.zero) (Xreal r) -> r = 0%R.
Proof.
rewrite I.zero_correct.
intros [H1 H2].
now apply Rle_antisym.
Qed.

Lemma join_correct :
  forall ui vi u v x,
  contains (I.convert ui) (Xreal u) ->
  contains (I.convert vi) (Xreal v) ->
  (u <= x <= v)%R ->
  contains (I.convert (I.join ui vi)) (Xreal x).
Proof.
intros ui vi u v x Iu Iv [H1 H2].
assert (Hu := I.join_correct ui vi (Xreal u)).
assert (Hv := I.join_correct ui vi (Xreal v)).
destruct (I.convert (I.join ui vi)) as [|p q].
easy.
split.
destruct p as [|p].
easy.
apply Rle_trans with (2 := H1).
apply Hu.
now left.
destruct q as [|q].
easy.
apply Rle_trans with (1 := H2).
apply Hv.
now right.
Qed.

Lemma contains_RInt prec (f3 : R -> R) x1 x2 Y X1 X2 :
  ex_RInt f3 x1 x2->
  contains (I.convert X1) (Xreal x1) ->
  contains (I.convert X2) (Xreal x2) ->
  (forall x, (Rmin x1 x2 <= x <= Rmax x1 x2)%R -> contains (I.convert Y) (Xreal (f3 x))) ->
  contains (I.convert (I.mul prec (I.sub prec X2 X1) Y)) (Xreal (RInt f3 x1 x2)).
Proof.
intros Hf3_int HZx1 HZx2 Hext.
destruct (Req_dec x2 x1) as [H|H].
{ rewrite H, RInt_point.
  unfold zero ; simpl.
  rewrite <- (Rmult_0_l (f3 x1)).
  apply mul_correct.
  rewrite <- (Rminus_diag_eq x2 x1) by easy.
  now apply sub_correct.
  apply Hext.
  apply Rmin_Rmax_l. }
replace (RInt f3 x1 x2) with ((x2 - x1) * ((RInt f3 x1 x2) / (x2 - x1)))%R.
2: {
  field.
  now apply Rminus_eq_contra.
}
apply mul_correct.
now apply sub_correct.
assert (H': forall x1 x2 : R, x1 < x2 ->
  (forall x, Rmin x1 x2 <= x <= Rmax x1 x2 -> contains (I.convert Y) (Xreal (f3 x))) ->
  ex_RInt f3 x1 x2 -> contains (I.convert Y) (Xreal (RInt f3 x1 x2 / (x2 - x1)))).
2: {
  destruct (Rdichotomy _ _ H) as [H21|H12].
  apply ex_RInt_swap in Hf3_int.
  rewrite <- opp_RInt_swap by easy.
  replace (-_/_)%R with (RInt f3 x2 x1 / (x1 - x2))%R by (field; lra).
  apply H' ; try easy.
  now rewrite Rmin_comm, Rmax_comm.
  now apply H'.
}
clear.
intros x1 x2 H' Hext Hf3_int.
destruct (I.convert Y) as [|l u].
easy.
apply le_contains.
- destruct l as [|rl]. easy.
  unfold le_lower, le_upper. simpl.
  apply Ropp_le_contravar.
  apply RInt_le_l ; try easy.
  intros x Hx.
  apply Hext.
  now rewrite -> Rmin_left, Rmax_right ; try apply Rlt_le.
- destruct u as [|ru]. easy.
  unfold le_upper.
  apply RInt_le_r ; try easy.
  intros x Hx.
  apply Hext.
  now rewrite -> Rmin_left, Rmax_right ; try apply Rlt_le.
Qed.

Definition midpoint xi :=
  let m := I.midpoint xi in I.bnd m m.

Lemma midpoint_correct :
  forall xi, not_empty (I.convert xi) ->
  I.convert (midpoint xi) = let m := Xreal (proj_val (I.F.convert (I.midpoint xi))) in Ibnd m m.
Proof.
intros xi Ex.
destruct (I.midpoint_correct xi Ex) as [H1 H2].
unfold midpoint.
rewrite I.bnd_correct.
now rewrite H1.
now apply I.valid_lb_real.
now apply I.valid_ub_real.
Qed.

Lemma contains_midpoint :
  forall xi, not_empty (I.convert xi) ->
  contains (I.convert (midpoint xi)) (Xreal (proj_val (I.F.convert (I.midpoint xi)))).
Proof.
intros xi Hx.
rewrite (midpoint_correct xi Hx).
split ; apply Rle_refl.
Qed.

Lemma subset_midpoint :
  forall xi, not_empty (I.convert xi) ->
  subset' (I.convert (midpoint xi)) (I.convert xi).
Proof.
intros xi Ex.
rewrite (midpoint_correct xi Ex).
intros [|x].
easy.
intros [H1 H2].
rewrite (Rle_antisym _ _ H2 H1).
destruct (I.midpoint_correct xi Ex) as [H3 H4].
now rewrite <- H3.
Qed.

End IntervalBasicExt.

Module IntervalExt (I : IntervalOps).

Include (IntervalBasicExt I).

Lemma cos_correct : forall prec, extension cos (I.cos prec).
Proof.
intros prec xi x.
now apply I.cos_correct.
Qed.

Lemma sin_correct : forall prec, extension sin (I.sin prec).
Proof.
intros prec xi x.
now apply I.sin_correct.
Qed.

Lemma tan_correct : forall prec, extension tan (I.tan prec).
Proof.
intros prec xi x Hx.
generalize (I.tan_correct prec xi _ Hx).
unfold Xtan', Xbind.
case is_zero ; try easy.
now case I.convert.
Qed.

Lemma atan_correct : forall prec, extension atan (I.atan prec).
Proof.
intros prec xi x.
now apply I.atan_correct.
Qed.

Lemma exp_correct : forall prec, extension exp (I.exp prec).
Proof.
intros prec xi x.
now apply I.exp_correct.
Qed.

Lemma ln_correct : forall prec, extension ln (I.ln prec).
Proof.
intros prec xi x Hx.
generalize (I.ln_correct prec xi _ Hx).
unfold Xln', Xbind.
case is_positive ; try easy.
now case I.convert.
Qed.

End IntervalExt.
