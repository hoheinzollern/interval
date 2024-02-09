From Coq Require Import PrimInt63 Sint63 Floats PArray.
From Coq Require Import Bool List Reals Lia Lra.

From Flocq Require Import Core PrimFloat BinarySingleNaN Operations.

Require Generic_proof.

Local Open Scope R_scope.

(** Signed computer integers: operations and constants **)

Definition Zcmod a b := let c := Z.quot b 2 in
  ((a + c) mod b - c)%Z.

Infix "cmod" := Zcmod (at level 40, no associativity) : Z_scope.

Lemma mod_mul_add_mod : forall a b m n c, (b <> 0)%Z -> (exists k, b = (k * c)%Z) ->
  ((a mod b * m + n) mod c = (a * m + n) mod c)%Z.
Proof. intros a b m n c Ib_neq_0 [k Heq_b].
generalize (Zdiv.Z_div_mod_eq_full a b). intros Haux.
rewrite Z.add_comm in Haux. apply Z.sub_move_r in Haux.
rewrite <-Haux. clear Haux. rewrite Heq_b at 1.
rewrite Z.mul_sub_distr_r, <-Z.add_sub_swap. unfold Z.sub.
rewrite (Z.mul_comm k c), <-!Z.mul_assoc, (Z.mul_comm c), <-Z.mul_opp_l.
apply Z.mod_add. lia.
Qed.

Corollary cmod_mul_add_mod : forall a b m n c, (b <> 0)%Z -> (exists k, b = (k * c)%Z) ->
  ((a cmod b * m + n) mod c = (a * m + n) mod c)%Z.
Proof. intros a b m n c. unfold Zcmod. rewrite Z.mul_sub_distr_r.
replace (a * m)%Z with ((a + Z.quot b 2) * m - (Z.quot b 2) * m)%Z by ring.
unfold Z.sub. rewrite <-2Z.add_assoc. apply mod_mul_add_mod.
Qed.

Corollary mod_add_mod : forall a b n c, (b <> 0)%Z -> (exists k, b = (k * c)%Z) ->
  ((a mod b + n) mod c = (a + n) mod c)%Z.
Proof. intros a b n c. rewrite <-(Z.mul_1_r (a mod b)).
rewrite <-(Z.mul_1_r a) at 2. apply mod_mul_add_mod.
Qed.

Corollary mod_mul_mod : forall a b n c, (b <> 0)%Z -> (exists k, b = (k * c)%Z) ->
  ((a mod b * n) mod c = (a * n) mod c)%Z.
Proof. intros a b n c. rewrite <-(Z.add_0_r (a mod b * n)).
rewrite <-(Z.add_0_r (a * n)). apply mod_mul_add_mod.
Qed.

Corollary cmod_add_mod : forall a b n c, (b <> 0)%Z -> (exists k, b = (k * c)%Z) ->
  ((a cmod b + n) mod c = (a + n) mod c)%Z.
Proof. intros a b n c. rewrite <-(Z.mul_1_r (a cmod b)).
rewrite <-(Z.mul_1_r a) at 2. apply cmod_mul_add_mod.
Qed.

Corollary cmod_mul_mod : forall a b n c, (b <> 0)%Z -> (exists k, b = (k * c)%Z) ->
  ((a cmod b * n) mod c = (a * n) mod c)%Z.
Proof. intros a b n c. rewrite <-(Z.add_0_r (a cmod b * n)).
rewrite <-(Z.add_0_r (a * n)). apply cmod_mul_add_mod.
Qed.

Lemma cmod_cmod : forall a b, (0 < b)%Z -> (a cmod b)%Z = Sint63.cmod a b.
Proof. intros a b H. unfold Zcmod, Sint63.cmod.
now rewrite Zquot.Zquot_Zdiv_pos; [| lia |].
Qed.

Lemma cmod_bounded : forall a b, (0 < b)%Z ->
 (- (b / 2) <= a cmod b <= b - b / 2 - 1)%Z.
Proof. intros a b H0. rewrite cmod_cmod by assumption.
generalize (Z.mod_pos_bound (a + b / 2) b H0).
unfold Sint63.cmod. lia.
Qed.

Module Type Size.
Parameter bits : positive.
End Size.

Module Size32 <: Size.
Definition bits := 32%positive.
End Size32.

Module Size63 <: Size.
Definition bits := 63%positive.
End Size63.

Module Size64 <: Size.
Definition bits := 64%positive.
End Size64.


Module SI (S : Size).

Definition bits := S.bits.

Definition N := Z.pow_pos 2 bits.
Definition norm n := Zcmod n N.

Definition in_bounds n := (- (N/2) <= n <= N/2 - 1)%Z.

Lemma in_bounds_norm : forall n, in_bounds (norm n).
Proof. intros n. unfold in_bounds, norm.
  replace (N / 2)%Z with (N - N / 2)%Z at 2.
  { apply cmod_bounded. now apply Zpower_pos_gt_0. }
  unfold N. rewrite Z.pow_pos_fold.
  replace (Z.pos bits) with (Z.pos bits - 1 + 1)%Z at 1 by ring.
  rewrite Z.pow_add_r ; [|lia|easy].
  rewrite Z.pow_sub_r ; [|easy|lia].
  change (2 ^ 1)%Z with 2%Z.
  ring.
Qed.

Lemma norm_in_bounds : forall n, in_bounds n -> norm n = n.
Proof. intros n. unfold in_bounds, norm.
  rewrite cmod_cmod by now apply Zpower_pos_gt_0.
  intros H. apply Sint63.cmod_small. lia.
Qed.

Definition add  n1 n2 := norm (n1 + n2)%Z.
Definition sub  n1 n2 := norm (n1 - n2)%Z.
Definition mul  n1 n2 := norm (n1 * n2)%Z.
Definition div  n1 n2 := norm (n1 / n2)%Z. (* Not expected to be useful for now *)
Definition quot n1 n2 := norm (Z.quot n1 n2).

End SI.

Module Int32 := SI Size32.
Module Int63 := SI Size63.
Module Int64 := SI Size64.

(** Real numbers: operations and constants **)

Notation Rpow2 := (bpow radix2).

Module Type Format.
Parameter prec : positive.
Parameter emax : Z.
End Format.

Module Format64 <: Format.
Definition prec := 53%positive.
Definition emax := 1024%Z.
End Format64.


Module RoundedR (F : Format).

Definition prec := Z.pos F.prec.
Definition emax := F.emax.

Definition emin := (3 - prec - emax)%Z.

Definition Rnd m := (round radix2 (FLT_exp emin prec) (round_mode m)).

Delimit Scope rnd_scope with rnd.

Notation rnd := (Rnd mode_NE).

Notation "x + y" := (rnd (x + y)) : rnd_scope.
Notation "x - y" := (rnd (x - y)) : rnd_scope.
Notation "x * y" := (rnd (x * y)) : rnd_scope.
Notation "x / y" := (rnd (x / y)) : rnd_scope.

Definition fma {md} x y z := Rnd md (x * y + z).
Definition sqrt {md} x := Rnd md (sqrt x).
Definition ldexp {md} x e := Rnd md (x * Rpow2 e).

Definition nearbyint {md} x := round radix2 (FIX_exp 0) (round_mode md) x.
Notation trunc := (@nearbyint mode_ZR).

Lemma nearbyint_IZR : forall md x, @nearbyint md x = IZR ((round_mode md) x).
Proof.
unfold nearbyint, round, F2R, scaled_mantissa. simpl.
intros md x. now rewrite 2Rmult_1_r.
Qed.

Definition maxval := IZR (radix2 ^ prec - 1)%Z * Rpow2 (emax - prec)%Z.
Definition minval := Rpow2 emin.

Lemma maxval_lt : maxval < Rpow2 emax.
Proof.
unfold maxval. replace emax with (prec + (emax - prec))%Z at 2 by (* lia *)
  now rewrite Z.add_comm, Z.sub_add. rewrite bpow_plus.
apply Rmult_lt_compat_r; [apply bpow_gt_0 |]. rewrite minus_IZR.
rewrite IZR_Zpower by easy. apply (Rplus_lt_reg_r 1). unfold Rminus.
rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
apply Rlt_plus_1.
Qed.

Lemma minval_gt : minval > 0.
Proof. apply bpow_gt_0. Qed.

End RoundedR.


Module Rrnd := RoundedR Format64.





(** On primitive arrays **)


Definition float_max x y := if ltb x y then y else x.

Definition float_min x y := if ltb x y then x else y.

Definition finite_array a :=
  snd (N.iter (Z.to_N (Uint63.to_Z (PArray.length a)))
   (fun '(i, b) => (Z.succ i, b && is_finite_SF (Prim2SF (get a (of_Z i))))) (0%Z, true)).

Definition float_array_max_partial a i := snd (N.iter (Z.to_N i)
 (fun '(n, x) => (Z.succ n, float_max x (PArray.get a (Uint63.of_Z n)))) (0%Z, neg_infinity)).

Definition float_array_min_partial a i := snd (N.iter (Z.to_N i)
 (fun '(n, x) => (Z.succ n, float_min x (PArray.get a (Uint63.of_Z n)))) (0%Z, infinity)).

Definition float_array_max a := float_array_max_partial a (Uint63.to_Z (PArray.length a)).

Definition float_array_min a := float_array_min_partial a (Uint63.to_Z (PArray.length a)).

Lemma finite_array_correct : forall a, finite_array a = true -> forall i,
 (Uint63.to_Z i < Uint63.to_Z (PArray.length a))%Z -> is_finite (Prim2B a.[i]) = true.
Proof. intros a fina_a i bnd_i. unfold finite_array in fina_a.
set (P := fun n '(i, b) => (Z.of_N n <= Uint63.to_Z (PArray.length a))%Z -> b = true ->
  i = Z.of_N n /\ forall j, (0 <= j < Z.of_N n)%Z -> is_finite (Prim2B a.[of_Z j]) = true).
set (f := fun '(i, b) => (Z.succ i, b && is_finite_SF (Prim2SF a.[of_Z i]))).
cut (forall n, P n (N.iter n f (0%Z, true))).
2: { apply N.iter_ind; [intros _ _; split; [easy | lia] |].
  intros n [i' b]. simpl. intros IHn H1 H2.
  destruct IHn as [IHn_1 IHn_2]; [lia | now apply andb_prop in H2 |].
  split; [lia |]. intros j Hj'. rewrite IHn_1 in H2.
  rewrite <-B2SF_Prim2B, is_finite_SF_B2SF in H2.
  assert (Hj : (0 <= j < Z.of_N n)%Z \/ j = Z.of_N n) by lia. clear Hj'.
  now destruct Hj as [Hj | ->]; [now apply IHn_2 | now apply andb_prop in H2]. }
intros Haux. specialize (Haux (Z.to_N (Uint63.to_Z (PArray.length a)))).
unfold P in Haux. revert fina_a Haux. destruct N.iter as [i' b].
simpl. intros -> He. rewrite <-(Uint63.of_to_Z i).
generalize (Uint63.to_Z_bounded (PArray.length a)). intros Hy.
apply He; [lia | easy |]. generalize (Uint63.to_Z_bounded i). lia.
Qed.

Lemma float_array_max_partial_correct : forall a, finite_array a = true -> forall i,
 (Uint63.to_Z i <= Uint63.to_Z (PArray.length a))%Z ->
  let f := float_array_max_partial a (Uint63.to_Z i) in
   ((0 < Uint63.to_Z i)%Z -> is_finite (Prim2B f) = true) /\ forall j,
     (0 <= Uint63.to_Z j < Uint63.to_Z i)%Z -> PrimFloat.leb a.[j] f = true.
Proof. intros a fina_a i bnd_i.
generalize (Uint63.to_Z_bounded i). intros Hi.
destruct (Uint63.to_Z i); [split; lia | | lia].
unfold float_array_max_partial. simpl.
set (P := fun p '(n, x) =>
 (Z.pos p <= Uint63.to_Z (PArray.length a))%Z ->
  n = Z.pos p /\ is_finite (Prim2B x) = true /\
  forall j, (0 <= Uint63.to_Z j < n)%Z -> PrimFloat.leb a.[j] x = true).
set (f := fun '(n, x) => (Z.succ n, float_max x a.[of_Z n])).

assert (non_empty_a : (0 < Uint63.to_Z (PArray.length a))%Z) by lia.
revert bnd_i.

cut (forall p', P p' (Pos.iter f (0%Z, neg_infinity) p')).
2: { apply Pos.iter_ind.
  { unfold P, f, float_max. simpl. intros _. split; [easy |].
    rewrite ltb_spec. cbn -[Uint63.to_Z]. unfold SFltb, SFcompare.
    generalize (finite_array_correct a fina_a 0 non_empty_a).
    intros fin_a_0. generalize fin_a_0.
    rewrite <-is_finite_SF_B2SF, B2SF_Prim2B.
    split; [now destruct Prim2SF; [| destruct s | |] |]. intros j bnd_j.
    rewrite <-(Uint63.of_to_Z j). replace (Uint63.to_Z j) with 0%Z by lia.
    assert (a_0_leb_self : PrimFloat.leb a.[0] a.[0] = true).
    { now rewrite leb_equiv, Bleb_correct, Rle_bool_true; [| apply Rle_refl | ..]. }
    revert fin_a_1. now destruct Prim2SF; [| destruct s | |]; clear -a_0_leb_self.
 (* That "clear" instruction is necessary, otherwise it loops indefinitely for some reason *) }
  intros p' [n x]. unfold P, f, float_max. simpl. intros IHp' bnd_p'.
  rewrite Pos2Z.inj_succ in bnd_p' |- *. split; [lia |].
  destruct IHp' as [eq_n [fin_x a_j_le_x']]; [lia |]. rewrite ltb_equiv.
  assert (fin_a_n : is_finite (Prim2B a.[of_Z n]) = true).
  { apply finite_array_correct; [easy |].
    generalize (Uint63.to_Z_bounded (PArray.length a)). intros Haux.
    rewrite Uint63.of_Z_spec, Z.mod_small; lia. } split.
  { now rewrite (Bltb_correct prec emax (Prim2B x) (Prim2B a.[of_Z n]));
   [destruct Rlt_bool | |]. } intros j [bnd_j_0 bnd_j_1].
  apply Z.lt_succ_r, Zle_lt_or_eq in bnd_j_1.
  destruct bnd_j_1 as [bnd_j_1 | bnd_j_1].
  - rewrite Bltb_correct by easy.
    assert (fin_a_j : is_finite (Prim2B a.[j]) = true)
      by (now apply finite_array_correct; [| lia]).
    assert (a_j_le_x : (a.[j] <=? x)%float = true) by (now apply a_j_le_x'; split).
    clear a_j_le_x'. case Rlt_bool_spec; intros comp_x; [| apply a_j_le_x].
    rewrite leb_equiv, Bleb_correct in a_j_le_x |- * by easy. apply Rle_bool_true.
    destruct (Rle_or_lt (B2R (Prim2B a.[j])) (B2R (Prim2B x))) as [Haux | Haux]; [lra |].
    apply Rle_bool_false in Haux. rewrite a_j_le_x in Haux. lia.
    (* again, "easy" does not terminate *)
  - rewrite <-(Uint63.of_to_Z j), bnd_j_1. rewrite Bltb_correct by easy.
    case Rlt_bool_spec; intros comp_x; rewrite leb_equiv, Bleb_correct by easy;
      apply Rle_bool_true; [apply Rle_refl | easy]. }

intros Haux. destruct Uint63.to_Z as [| p' |] eqn:Hlen; [lia | | lia].
clear non_empty_a. intros comp_p_p'. generalize Haux. intros Haux'.
specialize (Haux p). specialize (Haux' p'). unfold P in Haux. revert Haux.
destruct (Pos.iter _ _ p) as [p'' x] eqn:H. simpl. intros H'.
apply H' in comp_p_p'. destruct comp_p_p' as [-> [fin_x prop_x]]. now split.
Qed.

Lemma float_array_min_partial_correct : forall a, finite_array a = true -> forall i,
 (Uint63.to_Z i <= Uint63.to_Z (PArray.length a))%Z ->
  let f := float_array_min_partial a (Uint63.to_Z i) in
   ((0 < Uint63.to_Z i)%Z -> is_finite (Prim2B f) = true) /\ forall j,
     (0 <= Uint63.to_Z j < Uint63.to_Z i)%Z -> PrimFloat.leb f a.[j] = true.
Proof. intros a fina_a i bnd_i.
generalize (Uint63.to_Z_bounded i). intros Hi.
destruct (Uint63.to_Z i); [split; lia | | lia].
unfold float_array_min_partial. simpl.
set (P := fun p '(n, x) =>
 (Z.pos p <= Uint63.to_Z (PArray.length a))%Z ->
  n = Z.pos p /\ is_finite (Prim2B x) = true /\
  forall j, (0 <= Uint63.to_Z j < n)%Z -> PrimFloat.leb x a.[j] = true).
set (f := fun '(n, x) => (Z.succ n, float_min x a.[of_Z n])).

assert (non_empty_a : (0 < Uint63.to_Z (PArray.length a))%Z) by lia.
revert bnd_i.

cut (forall p', P p' (Pos.iter f (0%Z, infinity) p')).
2: { apply Pos.iter_ind.
  { unfold P, f, float_min. simpl. intros _. split; [easy |].
    rewrite ltb_spec. cbn -[Uint63.to_Z]. unfold SFltb, SFcompare.
    generalize (finite_array_correct a fina_a 0 non_empty_a).
    intros fin_a_0. generalize fin_a_0.
    rewrite <-is_finite_SF_B2SF, B2SF_Prim2B.
    split; [now destruct Prim2SF; [| destruct s | |] |]. intros j bnd_j.
    rewrite <-(Uint63.of_to_Z j). replace (Uint63.to_Z j) with 0%Z by lia.
    assert (a_0_leb_self : PrimFloat.leb a.[0] a.[0] = true).
    { now rewrite leb_equiv, Bleb_correct, Rle_bool_true; [| apply Rle_refl | ..]. }
    revert fin_a_1. now destruct Prim2SF; [| destruct s | |]; clear -a_0_leb_self. }
  intros p' [n x]. unfold P, f, float_min. simpl. intros IHp' bnd_p'.
  rewrite Pos2Z.inj_succ in bnd_p' |- *. split; [lia |].
  destruct IHp' as [eq_n [fin_x x_le_a_j']]; [lia |]. rewrite ltb_equiv.
  assert (fin_a_n : is_finite (Prim2B a.[of_Z n]) = true).
  { apply finite_array_correct; [easy |].
    generalize (Uint63.to_Z_bounded (PArray.length a)). intros Haux.
    rewrite Uint63.of_Z_spec, Z.mod_small; lia. } split.
  { now rewrite (Bltb_correct prec emax (Prim2B x) (Prim2B a.[of_Z n]));
   [destruct Rlt_bool | |]. } intros j [bnd_j_0 bnd_j_1].
  apply Z.lt_succ_r, Zle_lt_or_eq in bnd_j_1.
  destruct bnd_j_1 as [bnd_j_1 | bnd_j_1].
  - rewrite Bltb_correct by easy.
    assert (fin_a_j : is_finite (Prim2B a.[j]) = true)
      by (now apply finite_array_correct; [| lia]).
    assert (x_le_a_j : (x <=? a.[j])%float = true) by (now apply x_le_a_j'; split).
    clear x_le_a_j'. case Rlt_bool_spec; intros comp_x; [apply x_le_a_j |].
    rewrite leb_equiv, Bleb_correct in x_le_a_j |- * by easy. apply Rle_bool_true.
    destruct (Rle_or_lt (B2R (Prim2B x)) (B2R (Prim2B a.[j]))) as [Haux | Haux]; [lra |].
    apply Rle_bool_false in Haux. rewrite x_le_a_j in Haux. lia.
    (* again, "easy" does not terminate *)
  - rewrite <-(Uint63.of_to_Z j), bnd_j_1. rewrite Bltb_correct by easy.
    case Rlt_bool_spec; intros comp_x; rewrite leb_equiv, Bleb_correct by easy;
      apply Rle_bool_true; [lra | apply Rle_refl]. }

intros Haux. destruct Uint63.to_Z as [| p' |] eqn:Hlen; [lia | | lia].
clear non_empty_a. intros comp_p_p'. generalize Haux. intros Haux'.
specialize (Haux p). specialize (Haux' p'). unfold P in Haux. revert Haux.
destruct (Pos.iter _ _ p) as [p'' x] eqn:H. simpl. intros H'.
apply H' in comp_p_p'. destruct comp_p_p' as [-> [fin_x prop_x]]. now split.
Qed.

(** Floating point numbers: operations and constants **)

Definition HPrec_gt_0 : Prec_gt_0 Rrnd.prec := Hprec.
Definition HPrec_lt_emax : Prec_lt_emax Rrnd.prec Rrnd.emax := Hmax.

Definition binnorm     md m e   := @binary_normalize _ _ HPrec_gt_0 HPrec_lt_emax md m e false.
Definition FPadd       md x y   := @Bplus _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPsub       md x y   := @Bminus _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPmul       md x y   := @Bmult _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPdiv       md x y   := @Bdiv _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPfma       md x y z := @Bfma _ _ HPrec_gt_0 HPrec_lt_emax md x y z.
Definition FPnearbyint md x     := @Bnearbyint _ _ HPrec_lt_emax md x.
Definition FPtrunc        x     := @Btrunc Rrnd.prec Rrnd.emax x.
Definition FPldexp     md x e   := @Bldexp _ _ HPrec_gt_0 HPrec_lt_emax md x e.
Definition FPsqrt      md x     := @Bsqrt _ _ HPrec_gt_0 HPrec_lt_emax md x.


(** Typed arithmetic expression trees **)




(* 1. Types and operations on them *)


Inductive ExprType := Integer | BinFloat (*| Pair: ExprType -> ExprType -> ExprType *).



(* 1.0. Evaluation as primitive types *)


Definition evalExprTypePrim T := match T with
  | Integer  => PrimInt63.int
  | BinFloat => PrimFloat.float
  end.


Fixpoint evalExprTypePrim_list Tl : Set := match Tl with
  | nil => unit
  | T :: Tl' => evalExprTypePrim T * evalExprTypePrim_list Tl' end.


Fixpoint nthExprTypePrim {Tl DefaultT} n
   (l : evalExprTypePrim_list Tl) (default : evalExprTypePrim DefaultT) :=
  match n with
  | O    => match Tl return evalExprTypePrim_list Tl -> evalExprTypePrim (nth O Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => fst l'
            end l
  | S n' => match Tl return evalExprTypePrim_list Tl -> evalExprTypePrim (nth (S n') Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => nthExprTypePrim n' (snd l') default
            end l
  end. (* Why is it not defined the other way around? *)



(* 1.1. Evaluation as computer types *)


Definition evalExprTypeFloat T := match T with
  | Integer  => Z
  | BinFloat => binary_float Rrnd.prec Rrnd.emax
  end.


Fixpoint evalExprTypeFloat_list Tl : Set := match Tl with
  | nil => unit
  | T :: Tl' => evalExprTypeFloat T * evalExprTypeFloat_list Tl' end.


Fixpoint nthExprTypeFloat {Tl DefaultT} n
   (l : evalExprTypeFloat_list Tl) (default : evalExprTypeFloat DefaultT) :=
  match n with
  | O    => match Tl return evalExprTypeFloat_list Tl -> evalExprTypeFloat (nth O Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => match T with
                          | Integer  => fun l' => Int32.norm (fst l')
                          | BinFloat => fun l' => fst l'
                          end
            end l
  | S n' => match Tl return evalExprTypeFloat_list Tl -> evalExprTypeFloat (nth (S n') Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => nthExprTypeFloat n' (snd l') default
            end l
  end.



(* 1.2. Evaluation as math types *)


Definition evalExprTypeRounded T := match T with
  | Integer  => Z
  | BinFloat => R
  end.


Fixpoint evalExprTypeRounded_list Tl : Set := match Tl with
  | nil => unit
  | T :: Tl' => evalExprTypeRounded T * evalExprTypeRounded_list Tl' end.


Fixpoint evalExprTypeRounded_fun  (Tl : list ExprType) := match Tl with
  | nil      => Prop
  | T :: Tl' => evalExprTypeRounded T -> evalExprTypeRounded_fun Tl' end.


Fixpoint uncurrify {Tl} :=
  match Tl return evalExprTypeRounded_fun Tl -> evalExprTypeRounded_list Tl -> Prop with
  | nil      => fun f l => f
  | _ :: Tl' => fun f l => uncurrify (f (fst l)) (snd l) end.


Fixpoint nthExprTypeRounded {Tl DefaultT} n
   (l : evalExprTypeRounded_list Tl) (default : evalExprTypeRounded DefaultT) :=
  match n with
  | O    => match Tl return evalExprTypeRounded_list Tl -> evalExprTypeRounded (nth O Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => fst l'
            end l
  | S n' => match Tl return evalExprTypeRounded_list Tl -> evalExprTypeRounded (nth (S n') Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => nthExprTypeRounded n' (snd l') default
            end l
  end.



(* 1.3. Evaluation as real numbers *)


Fixpoint evalExprTypeReal_list (Tl : list ExprType) : Set := match Tl with
  | nil      => unit
  | _ :: Tl' => R * evalExprTypeReal_list Tl' end.

(*
Fixpoint evalExprTypeReal_fun  (Tl : list ExprType) := match Tl with
  | nil      => Prop
  | _ :: Tl' => R -> evalExprTypeReal_fun Tl' end. *)


Fixpoint nthExprTypeReal {Tl} n (l : evalExprTypeReal_list Tl) (default : R) :=
  match n with
  | O    => match Tl return evalExprTypeReal_list Tl -> _ with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => fst l'
            end l
  | S n' => match Tl return evalExprTypeReal_list Tl -> _ with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => nthExprTypeReal n' (snd l') default
            end l
  end.



(* Conversions between the different evaluation types *)

Definition P2C {T} : evalExprTypePrim T -> evalExprTypeFloat T :=
  match T with
  | Integer  => fun x => Sint63.to_Z x
  | BinFloat => fun x => Prim2B x
  end.

Fixpoint P2C_list {Tl} : evalExprTypePrim_list Tl -> evalExprTypeFloat_list Tl :=
  match Tl with
  | nil    => fun l => tt
  | _ :: _ => fun l => (P2C (fst l), P2C_list (snd l))
  end.

Definition C2M {T} : evalExprTypeFloat T -> evalExprTypeRounded T :=
  match T with
  | Integer  => fun x => x
  | BinFloat => fun x => B2R x
  end.

Fixpoint C2M_list {Tl} : evalExprTypeFloat_list Tl -> evalExprTypeRounded_list Tl :=
  match Tl with
  | nil    => fun l => tt
  | _ :: _ => fun l => (C2M (fst l), C2M_list (snd l))
  end.

Definition M2R {T} : evalExprTypeRounded T -> R :=
  match T with
  | Integer  => fun x => IZR x
  | BinFloat => fun x => x
  end.

Fixpoint M2R_list {Tl} : evalExprTypeRounded_list Tl -> evalExprTypeReal_list Tl :=
  match Tl with
  | nil    => fun l => tt
  | _ :: _ => fun l => (M2R (fst l), M2R_list (snd l))
  end.

Definition P2M {T} : evalExprTypePrim T -> evalExprTypeRounded T :=
  match T with
  | Integer  => fun x => Sint63.to_Z x
  | BinFloat => fun x => SF2R radix2 (Prim2SF x)
  end.

Fixpoint P2M_list {Tl} : evalExprTypePrim_list Tl -> evalExprTypeRounded_list Tl :=
  match Tl with
  | nil    => fun l => tt
  | _ :: _ => fun l => (P2M (fst l), P2M_list (snd l))
  end.



(* 1.4. Binary arithmetic operations *)


Inductive ArithOp := ADD | SUB | MUL | DIV.

Definition PIOpToFunction OP := match OP with
  | ADD => PrimInt63.add
  | SUB => PrimInt63.sub
  | MUL => PrimInt63.mul
  | DIV => PrimInt63.divs end.

Definition PFOpToFunction OP := match OP with
  | ADD => PrimFloat.add
  | SUB => PrimFloat.sub
  | MUL => PrimFloat.mul
  | DIV => PrimFloat.div end.

Definition SIOpToFunction OP := match OP with
  | ADD => Int32.add
  | SUB => Int32.sub
  | MUL => Int32.mul
  | DIV => Int32.quot end.

Definition FPOpToFunction OP := match OP with
  | ADD => FPadd
  | SUB => FPsub
  | MUL => FPmul
  | DIV => FPdiv end.

Definition ZOpToFunction OP := match OP with
  | ADD => Z.add
  | SUB => Z.sub
  | MUL => Z.mul
  | DIV => Z.quot end.

Definition ROpToFunction OP := match OP with
  | ADD => Rplus
  | SUB => Rminus
  | MUL => Rmult
  | DIV => Rdiv end.

Definition RrndOpToFunction OP md x y :=
  match OP with
  | ADD => @Rrnd.Rnd md (x + y)
  | SUB => @Rrnd.Rnd md (x - y)
  | MUL => @Rrnd.Rnd md (x * y)
  | DIV => @Rrnd.Rnd md (x / y)
  end.


(* 3. Arithmetic expressions as trees with dependent types *)


(* 3.1. Definition of said trees *)

Inductive ArithExpr : list ExprType -> ExprType -> Type :=
  | Int:                forall {Tl},       Z ->                         ArithExpr Tl Integer

  | BinFl:              forall {Tl},       PrimFloat.float ->           ArithExpr Tl BinFloat

  | Var:                forall {Tl} n,                                  ArithExpr Tl (nth n Tl Integer)
                  (*    forall {Tl T} n,   T = (nth n Tl Integer) ->    ArithExpr Tl T *)

  | Op:                 forall {Tl T},     ArithOp ->
                                           ArithExpr Tl T ->
                                           ArithExpr Tl T ->            ArithExpr Tl T

  | OpExact:            forall {Tl},       ArithOp ->
                                           ArithExpr Tl BinFloat ->
                                           ArithExpr Tl BinFloat ->     ArithExpr Tl BinFloat

  | Fma:                forall {Tl},       ArithExpr Tl BinFloat ->
                                           ArithExpr Tl BinFloat ->
                                           ArithExpr Tl BinFloat ->     ArithExpr Tl BinFloat

  | FmaExact:           forall {Tl},       ArithExpr Tl BinFloat ->
                                           ArithExpr Tl BinFloat ->
                                           ArithExpr Tl BinFloat ->     ArithExpr Tl BinFloat

  | Nearbyint:          forall {Tl},       ArithExpr Tl BinFloat ->     ArithExpr Tl BinFloat

  | FastNearbyint:      forall {Tl},       ArithExpr Tl BinFloat ->     ArithExpr Tl BinFloat

  | FastNearbyintToInt: forall {Tl},       ArithExpr Tl BinFloat ->     ArithExpr Tl Integer

  | TruncToInt:         forall {Tl},       ArithExpr Tl BinFloat ->     ArithExpr Tl Integer

  | FloatInj:           forall {Tl},       ArithExpr Tl Integer  ->     ArithExpr Tl BinFloat

(*| Ldexp:              forall {Tl},       Z ->
                                           ArithExpr Tl BinFloat ->
                                           ArithExpr Tl Integer ->      ArithExpr Tl BinFloat *)

  | Sqrt:               forall {Tl T},     ArithExpr Tl T ->            ArithExpr Tl T

  | Let:                forall {Tl T1 T2}, ArithExpr Tl T1 ->
                                           ArithExpr (T1 :: Tl) T2 ->   ArithExpr Tl T2

  | ArrayAcc:           forall {Tl},       array PrimFloat.float ->
                                           ArithExpr Tl Integer ->      ArithExpr Tl BinFloat

  | Assert:             forall {Tl T},    (evalExprTypeRounded T -> evalExprTypeRounded_fun Tl) ->
                                           ArithExpr Tl T ->            ArithExpr Tl T

  | Postcond:           forall {Tl T},    (evalExprTypeRounded T -> evalExprTypeRounded_fun Tl) ->
                                           ArithExpr Tl T ->            ArithExpr Tl T.

Arguments Op                 {Tl} & {T}     OP   t1 t2.
Arguments OpExact            {Tl} &         OP   t1 t2.
Arguments Fma                {Tl} &              t1 t2 t3.
Arguments FmaExact           {Tl} &              t1 t2 t3.
Arguments Nearbyint          {Tl} &              t.
Arguments FastNearbyint      {Tl} &              t.
Arguments FastNearbyintToInt {Tl} &              t.
Arguments TruncToInt         {Tl} &              t.
Arguments FloatInj           {Tl} &              t.
(* Arguments Ldexp              {Tl} &          n   t1 t2. *)
Arguments Sqrt               {Tl} & {T}          t.
Arguments Let                {Tl} & {T1 T2}      t1 t2.
Arguments ArrayAcc           {Tl} &            a t.
Arguments Assert             {Tl} & {T}      P   t.
Arguments Postcond           {Tl} & {T}      P   t.

Set Asymmetric Patterns.


(* 3.2. Definition of evaluation functions *)

Fixpoint evalPrim {Tl T} (t: ArithExpr Tl T) {struct t}
  : evalExprTypePrim_list Tl -> evalExprTypePrim T
  := match t (* in ArithExpr Tl'' T'' return evalExprTypePrim_list Tl'' -> evalExprTypePrim T'' *) with (* uncomment for debugging *)
  | Int                _                    p        => fun l => Uint63.of_Z p
  | BinFl              _                    x        => fun l => x
  | Var                _         n                   => fun l => @nthExprTypePrim _ Integer n l (Uint63.of_Z 0)
  | Op                 Tl' T'      OP       t1 t2    => fun l =>
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> evalExprTypePrim T' with
    | Integer  => fun t1' t2' => PIOpToFunction OP (evalPrim t1' l) (evalPrim t2' l)
    | BinFloat => fun t1' t2' => PFOpToFunction OP (evalPrim t1' l) (evalPrim t2' l)
    end t1 t2
  | OpExact            _           OP       t1 t2    => fun l => PFOpToFunction OP (evalPrim t1 l) (evalPrim t2 l)
  | Fma                _                    t1 t2 t3
  | FmaExact           _                    t1 t2 t3 => fun l => B2Prim (FPfma mode_NE (Prim2B (evalPrim t1 l)) (Prim2B (evalPrim t2 l)) (Prim2B (evalPrim t3 l)))
  | Nearbyint          _                    t        => fun l => B2Prim (FPnearbyint mode_NE (Prim2B (evalPrim t l)))
  | FastNearbyint      _                    t        => fun l => (evalPrim t l + 0x1.8p52 - 0x1.8p52)%float
  | FastNearbyintToInt _                    t        => fun l => (normfr_mantissa (fst (frshiftexp (evalPrim t l + 0x1.8p52)%float)) - 6755399441055744)%uint63
(*| Nearbyint          _                    t        => fun l => Primitive_ops.PrimitiveFloat.nearbyint (PrimFloat.of_uint63 (Uint63.of_Z 0)) Basic.rnd_NE (evalPrim t l) *)
  | TruncToInt         _                    t        => fun l => Uint63.of_Z (FPtrunc (Prim2B (evalPrim t l)))
  | FloatInj           _                    t        => fun l => let x := evalPrim t l in let absx := Sint63.abs x in
    let f := PrimFloat.of_uint63 absx in if (0 <=? x)%sint63 then f else PrimFloat.opp f
(*| FloatInj           _                    t        => fun l => let x := evalPrim t l in let aux1 := PrimInt63.land 0x4000000000000000%uint63 x in
    let shift := 0x3e%uint63 in let sign := PrimInt63.lsr aux1 shift in let aux2 := PrimInt63.asr aux1 shift in
    let f := PrimFloat.of_uint63 (PrimInt63.add (PrimInt63.lxor x aux2) sign) in
    if PrimInt63.eqb sign 0x1%uint63 then f else PrimFloat.opp f *)
(*| Ldexp              _              _       t1 t2    => fun l => PrimFloat.ldshiftexp (evalPrim t1 l) (Uint63.add (evalPrim t2 l) 2101%uint63) ID := 1 *)
  | Sqrt               Tl' T'               t        => fun l =>
    match T' return ArithExpr Tl' T' -> evalExprTypePrim T' with
    | Integer  => fun t' => Uint63.sqrt    (evalPrim t' l)
    | BinFloat => fun t' => PrimFloat.sqrt (evalPrim t' l)
    end t
  | Let                _   _  _             t1 t2    => fun l => let x := evalPrim t1 l in evalPrim t2 (x, l)
  | ArrayAcc           _                  a t        => fun l => get a (evalPrim t l)
  | Assert             _   _            _   t
  | Postcond           _   _            _   t        => fun l => evalPrim t l
  end.

Fixpoint evalFloat {Tl T} (t: ArithExpr Tl T) {struct t}
  : evalExprTypeFloat_list Tl -> mode -> evalExprTypeFloat T
  := match t in ArithExpr Tl'' T'' return evalExprTypeFloat_list Tl'' -> mode -> evalExprTypeFloat T'' with
  | Int                _                    p        => fun l md => Int32.norm p
  | BinFl              _                    x        => fun l md => Prim2B x
  | Var                _         n                   => fun l md => @nthExprTypeFloat _ Integer n l 0%Z
  | Op                 Tl' T'      OP       t1 t2    => fun l md =>
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> evalExprTypeFloat T' with
    | Integer  => fun t1' t2' => SIOpToFunction OP    (evalFloat t1' l md) (evalFloat t2' l md)
    | BinFloat => fun t1' t2' => FPOpToFunction OP md (evalFloat t1' l md) (evalFloat t2' l md)
    end t1 t2
  | OpExact            _           OP       t1 t2    => fun l md => FPOpToFunction OP md (evalFloat t1 l md) (evalFloat t2 l md)
  | Fma                _                    t1 t2 t3
  | FmaExact           _                    t1 t2 t3 => fun l md => FPfma md (evalFloat t1 l md) (evalFloat t2 l md) (evalFloat t3 l md)
  | Nearbyint          _                    t        => fun l md => FPnearbyint mode_NE (evalFloat t l md)
  | FastNearbyint      _                    t        => fun l md => FPsub mode_NE (FPadd mode_NE (evalFloat t l md) (Prim2B 0x1.8p52%float)) (Prim2B 0x1.8p52%float)
  | FastNearbyintToInt _                    t        => fun l md => Int32.norm (FPtrunc (FPsub mode_NE (FPadd mode_NE (evalFloat t l md) (Prim2B 0x1.8p52%float)) (Prim2B 0x1.8p52%float)))
  | TruncToInt         _                    t        => fun l md => Int32.norm (FPtrunc (evalFloat t l md))
  | FloatInj           _                    t        => fun l md => binnorm mode_NE (evalFloat t l md) 0
(*| Ldexp              _              _     t1 t2    => fun l md => FPldexp md (evalFloat t1 l md) (evalFloat t2 l md) *)
  | Sqrt               Tl' T'               t        => fun l md =>
    match T' return ArithExpr Tl' T' -> evalExprTypeFloat T' with
    | Integer  => fun t' => Z.sqrt    (evalFloat t' l md)
    | BinFloat => fun t' => FPsqrt md (evalFloat t' l md)
    end t
  | Let                _   _  _             t1 t2    => fun l md => let x := evalFloat t1 l md in evalFloat t2 (x, l) md
  | ArrayAcc           _                  a t        => fun l md => Prim2B (get a (of_Z (evalFloat t l md)))
  | Assert             _   _            _   t
  | Postcond           _   _            _   t        => fun l md => evalFloat t l md
  end.

Fixpoint evalRounded {Tl T} (t: ArithExpr Tl T) {struct t}
  :  evalExprTypeRounded_list Tl -> mode -> evalExprTypeRounded T
  := match t in ArithExpr Tl'' T'' return evalExprTypeRounded_list Tl'' -> mode -> evalExprTypeRounded T'' with
  | Int                _                    p        => fun l md => p
  | BinFl              _                    x        => fun l md => SF2R radix2 (Prim2SF x)
  | Var                _         n                   => fun l md => @nthExprTypeRounded _ Integer n l 0%Z
  | Op                 Tl' T'      OP       t1 t2    => fun l md =>
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> evalExprTypeRounded T' with
    | Integer  => fun t1' t2' => ZOpToFunction    OP    (evalRounded t1' l md) (evalRounded t2' l md)
    | BinFloat => fun t1' t2' => RrndOpToFunction OP md (evalRounded t1' l md) (evalRounded t2' l md)
    end t1 t2
  | OpExact            _           OP       t1 t2    => fun l md => ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md)
  | Fma                _                    t1 t2 t3 => fun l md => @Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md)
  | FmaExact           _                    t1 t2 t3 => fun l md => (evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)
  | Nearbyint          _                    t
  | FastNearbyint      _                    t        => fun l md => @Rrnd.nearbyint mode_NE (evalRounded t l md)
  | FastNearbyintToInt _                    t        => fun l md => ZnearestE (evalRounded t l md)
  | TruncToInt         _                    t        => fun l md => Ztrunc (evalRounded t l md)
  | FloatInj           _                    t        => fun l md => IZR (evalRounded t l md)
(*| Ldexp              _              _     t1 t2    => fun l md => @Rrnd.ldexp md (evalRounded t1 l md) (evalRounded t2 l md) *)
  | Sqrt               Tl' T'               t        => fun l md =>
    match T' return ArithExpr Tl' T' -> evalExprTypeRounded T' with
    | Integer  => fun t' => Z.sqrt        (evalRounded t' l md)
    | BinFloat => fun t' => @Rrnd.sqrt md (evalRounded t' l md)
    end t
  | Let                _   _  _             t1 t2    => fun l md => let x := evalRounded t1 l md in evalRounded t2 (x, l) md
  | ArrayAcc           _                  a t        => fun l md => SF2R radix2 (Prim2SF (get a (of_Z (evalRounded t l md))))
  | Assert             _   _            _   t
  | Postcond           _   _            _   t        => fun l md => evalRounded t l md
  end.

(* Deprecated *)
Fixpoint evalExact {Tl T} (t: ArithExpr Tl T) {struct t}
  :  evalExprTypeRounded_list Tl -> evalExprTypeRounded T
  := match t with
  | Int                _                    p        => fun l => p
  | BinFl              _                    x        => fun l => SF2R radix2 (Prim2SF x)
  | Var                _         n                   => fun l => @nthExprTypeRounded _ Integer n l 0%Z
  | Op                 Tl' T'      OP       t1 t2    => fun l =>
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> evalExprTypeRounded T' with
    | Integer  => fun t1' t2' => ZOpToFunction OP (evalExact t1' l) (evalExact t2' l)
    | BinFloat => fun t1' t2' => ROpToFunction OP (evalExact t1' l) (evalExact t2' l)
    end t1 t2
  | OpExact            _           OP       t1 t2    => fun l => ROpToFunction OP (evalExact t1 l) (evalExact t2 l)
  | Fma                _                    t1 t2 t3
  | FmaExact           _                    t1 t2 t3 => fun l => (evalExact t1 l) * (evalExact t2 l) + (evalExact t3 l)
  | Nearbyint          _                    t
  | FastNearbyint      _                    t        => fun l => 0
  | FastNearbyintToInt _                    t        => fun l => 0%Z
  | TruncToInt         _                    t        => fun l => 0%Z
  | FloatInj           _                    t        => fun l => IZR (evalExact t l)
(*| Ldexp              _              _     t1 t2    => fun l => (evalExact t1 l) * Rpow2 (evalExact t2 l) *)
  | Sqrt               Tl' T'               t        => fun l =>
    match T' return ArithExpr Tl' T' -> evalExprTypeRounded T' with
    | Integer  => fun t' => Z.sqrt (evalExact t' l)
    | BinFloat => fun t' => sqrt   (evalExact t' l)
    end t
  | Let                _   _  _             t1 t2    => fun l => let x := evalExact t1 l in evalExact t2 (x, l)
  | ArrayAcc           _                  a t        => fun l => 0
  | Assert             _   _            _   t
  | Postcond           _   _            _   t        => fun l => evalExact t l
  end.

(* TODO: move to Compute.v *)
Fixpoint evalReal {Tl T} (t: ArithExpr Tl T) {struct t}
  :  evalExprTypeReal_list Tl -> _
  := match t with
  | Int                _                    p        => fun l md => IZR p
  | BinFl              _                    x        => fun l md => B2R (Prim2B x)
  | Var                _         n                   => fun l md => nthExprTypeReal n l 0
  | Op                 Tl' T'      OP       t1 t2    => fun l md =>
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> _ with
    | Integer  => fun t1' t2' => match OP with
      | DIV => Rrnd.trunc       (evalReal t1' l md / evalReal t2' l md)
      | _   => ROpToFunction OP (evalReal t1' l md) (evalReal t2' l md)
      end
    | BinFloat => fun t1' t2' => RrndOpToFunction OP md (evalReal t1' l md) (evalReal t2' l md)
    end t1 t2
  | OpExact            _           OP       t1 t2    => fun l md => ROpToFunction OP (evalReal t1 l md) (evalReal t2 l md)
  | Fma                _                    t1 t2 t3 => fun l md => @Rrnd.fma md (evalReal t1 l md) (evalReal t2 l md) (evalReal t3 l md)
  | FmaExact           _                    t1 t2 t3 => fun l md => evalReal t1 l md * evalReal t2 l md + evalReal t3 l md
  | Nearbyint          _                    t
  | FastNearbyint      _                    t
  | FastNearbyintToInt _                    t        => fun l md => @Rrnd.nearbyint mode_NE (evalReal t l md)
  | TruncToInt         _                    t        => fun l md => Rrnd.trunc (evalReal t l md)
  | FloatInj           _                    t        => fun l md => evalReal t l md
(*| Ldexp              _              _     t1 t2    => fun l md =>
      round radix2 (FLT_exp Rrnd.emin Rrnd.prec) (round_mode md)
        (evalReal t1 l md * Rpower 2 (evalReal t2 l md)) *)
  | Sqrt               Tl' T'               t        => fun l md =>
    match T' return ArithExpr Tl' T' -> _ with
    | Integer  => fun t' => Rrnd.trunc (sqrt (evalReal t' l md))
    | BinFloat => fun t' => @Rrnd.sqrt md    (evalReal t' l md)
    end t
  | Let                _   _  _             t1 t2    => fun l md => let x := evalReal t1 l md in evalReal t2 (x, l) md
  | ArrayAcc           _                  a t        => fun l md => SF2R radix2 (Prim2SF (get a (of_Z (Ztrunc (evalReal t l md)))))
  | Assert             _   _            _   t
  | Postcond           _   _            _   t        => fun l md => evalReal t l md
  end.


Definition convertibleFloat {T} : evalExprTypeFloat T -> Prop :=
  match T with
  | Integer  => fun n => Int32.in_bounds n (* When Integer translates to 32-bit integers *)
  | BinFloat => fun f => @is_finite Rrnd.prec Rrnd.emax f = true
  end.

Definition convertiblePrim {T} : evalExprTypePrim T -> Prop :=
  match T with
  | Integer  => fun n => Int32.in_bounds (to_Z n) (* When Integer translates to 32-bit integers *)
  | BinFloat => fun f => @is_finite_SF (Prim2SF f) = true
  end.

Fixpoint convertibleFloat_list {Tl} : evalExprTypeFloat_list Tl -> Prop :=
  match Tl with
  | nil    => fun lC => True
  | T :: _ => fun lC => convertibleFloat (fst lC) /\ convertibleFloat_list (snd lC)
  end.

Fixpoint convertiblePrim_list {Tl} : evalExprTypePrim_list Tl -> Prop :=
  match Tl with
  | nil    => fun lC => True
  | T :: _ => fun lC => convertiblePrim (fst lC) /\ convertiblePrim_list (snd lC)
  end.

Definition isConversionFloat {T} : evalExprTypeFloat T -> evalExprTypeRounded T -> Prop :=
  match T with
  | Integer  => fun n1 n2 => n1 = n2
  | BinFloat => fun  f  r => @B2R Rrnd.prec Rrnd.emax f = r
  end.

Definition isConversionPrim {T} : evalExprTypePrim T -> evalExprTypeRounded T -> Prop :=
  match T with
  | Integer  => fun n1 n2 => Sint63.to_Z n1 = n2
  | BinFloat => fun  f  r => @SF2R radix2 (Prim2SF f) = r
  end.

Definition eqExprTypeFloat {T} (e1 : evalExprTypeFloat T) (e2 : evalExprTypeRounded T) :=
  convertibleFloat e1 /\ isConversionFloat e1 e2.

Definition eqExprTypePrim {T} (e1 : evalExprTypePrim T) (e2 : evalExprTypeRounded T) :=
  convertiblePrim e1 /\ isConversionPrim e1 e2.


Fixpoint assertions {Tl T} (t : ArithExpr Tl T) : evalExprTypeRounded_list Tl -> _ :=
  match t with

  | Int                _               _
  | BinFl              _               _
  | Var                _     _
  | ArrayAcc           _             _ _        => fun l md => True


  | Op                 _ _     _       t1 t2
  | OpExact            _       _       t1 t2
(*| Ldexp              _         _     t1 t2  *)=> fun l md => assertions t1 l md
                                                   /\ assertions t2 l md

  | Fma                _               t1 t2 t3
  | FmaExact           _               t1 t2 t3 => fun l md => assertions t1 l md
                                                   /\ assertions t2 l md
                                                   /\ assertions t3 l md

  | Nearbyint          _               t
  | FastNearbyint      _               t
  | FastNearbyintToInt _               t
  | TruncToInt         _               t
  | FloatInj           _               t
  | Sqrt               _ _             t        => fun l md => assertions t l md

  | Let                _ _ _           t1 t2    => fun l md => assertions t1 l md
                                                   /\ let x := evalRounded t1 l md in
                                                      assertions t2 (x, l) md

  | Assert             _ _         P   t        => fun l md => let P' := P (evalExact t l) in
                                                   uncurrify P' l /\ assertions t l md

  | Postcond           _ _         _   t        => fun l md => assertions t l  md
  end.

Fixpoint wellDefined {Tl T} (t: ArithExpr Tl T) : evalExprTypeRounded_list Tl -> _ :=
  match t with

  | Int                _                   _
  | BinFl              _                   _
  | Var                _        _                   => fun l md => True

  | Op                 _   T'     OP       t1 t2    => fun l md =>
    let P := wellDefined t1 l md /\ wellDefined t2 l md in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> match T' with Integer => 0%Z | _ => 0 end
    | _   => P
    end

  | OpExact            _          OP       t1 t2    => fun l md =>
    let P := wellDefined t1 l md /\ wellDefined t2 l md in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> 0
    | _   => P
    end

  | Fma                _                   t1 t2 t3
  | FmaExact           _                   t1 t2 t3 => fun l md =>
    wellDefined t1 l md /\ wellDefined t2 l md /\ wellDefined t3 l md

  | Nearbyint          _                   t
  | FastNearbyint      _                   t
  | FastNearbyintToInt _                   t
  | TruncToInt         _                   t
  | FloatInj           _                   t        => fun l md => wellDefined t l md

  | Sqrt               Tl' T'              t        => fun l md => wellDefined t l md /\
    match T' return ArithExpr Tl' T' -> _ with
    | Integer => fun t' => 0 <= IZR (evalRounded t' l md)
    | _       => fun t' => 0 <= evalRounded t' l md
    end t

(*| Ldexp              _             _     t1 t2    => fun l md =>
    wellDefined t1 l md /\ wellDefined t2 l md *)

  | Let                _   _  _            t1 t2    => fun l md =>
    wellDefined t1 l md /\ wellDefined t2 (evalRounded t1 l md, l) md

  | ArrayAcc           _                 _ t
  | Assert             _   _           _   t
  | Postcond           _   _           _   t        => fun l md => wellDefined t l md
  end.


Fixpoint operationsExact {Tl T} (t: ArithExpr Tl T) : evalExprTypeRounded_list Tl -> _ := (* TODO: find better name *)
  match t with

  | Int                _                     _
  | BinFl              _                     _
  | Var                _        _        => fun l md => True

  | Op                 Tl' T'     OP         t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> _ with
    | Integer  => fun t1' t2' =>
      - IZR (Int32.N / 2) <= IZR (ZOpToFunction OP (evalRounded t1' l md) (evalRounded t2' l md)) <= IZR (Int32.N / 2 - 1)
    | BinFloat => fun t1' t2' => Rabs (RrndOpToFunction OP md (evalRounded t1' l md) (evalRounded t2' l md)) <= Rrnd.maxval
    end t1 t2

  | OpExact            _          OP         t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\
    Rabs (ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md)) <= Rrnd.maxval /\
    RrndOpToFunction OP md (evalRounded t1 l md) (evalRounded t2 l md)
     = ROpToFunction OP    (evalRounded t1 l md) (evalRounded t2 l md)

  | Fma                _                     t1 t2 t3 => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\ operationsExact t3 l md /\
    Rabs (@Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md)) <= Rrnd.maxval

  | FmaExact           _                     t1 t2 t3 => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\ operationsExact t3 l md /\
    Rabs ((evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)) <= Rrnd.maxval /\
    @Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md) =
    (evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)

  | Nearbyint          _                     t        => fun l md => operationsExact t l md

  | FastNearbyint      _                     t        => fun l md => operationsExact t l md /\
   -2251799813685248 <= evalRounded t l md <= 2251799813685247

  | FastNearbyintToInt _                     t        => fun l md => operationsExact t l md /\
    -2147483648 <= evalRounded t l md <= 2147483647

  | TruncToInt         _                     t        => fun l md => operationsExact t l md /\
   (- Int32.N / 2 <= Ztrunc (evalRounded t l md)  <= Int32.N / 2 - 1)%Z

  | FloatInj           _                     t        => fun l md => operationsExact t l md /\ Rabs (IZR (evalRounded t l md)) <= Rpow2 53

  | Sqrt               _   _                 t        => fun l md => operationsExact t l md

(*| Ldexp              _             n       t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\
    Rabs (evalRounded t1 l md) <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec) /\
    IZR (n + evalRounded t2 l md) <= IZR Rrnd.emax *)

  | ArrayAcc           _                   a t        => fun l md => operationsExact t l md /\
   (0 <= evalRounded t l md < Uint63.to_Z (PArray.length a))%Z

  | Let                _   _  _              t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 (evalRounded t1 l md, l) md

  | Assert             _   _           _     t
  | Postcond           _   _           _     t        => fun l md => operationsExact t l md
  end.


Fixpoint wellBehaved {Tl T} (t: ArithExpr Tl T) : evalExprTypeRounded_list Tl -> _ := (* TODO: rename *)
  match t with

  | Int                _                      _
  | BinFl              _                      _
  | Var                _        _                     => fun l md => True

  | Op                 Tl' T'     OP         t1 t2    => fun l md => wellBehaved t1 l md /\ wellBehaved t2 l md /\ let P :=
    match T' return ArithExpr Tl' T' -> ArithExpr Tl' T' -> _ with
    | Integer  => fun t1' t2' => - IZR (Int32.N / 2) <= IZR (ZOpToFunction OP (evalRounded t1' l md) (evalRounded t2' l md)) <= IZR (Int32.N / 2 - 1)
    | BinFloat => fun t1' t2' => Rabs (RrndOpToFunction OP md (evalRounded t1' l md) (evalRounded t2' l md)) <= Rrnd.maxval end t1 t2 in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> match T' with Integer => 0%Z | _ => 0 end
    | _   => P
    end

  | OpExact            _          OP         t1 t2    => fun l md => let P := wellBehaved t1 l md /\ wellBehaved t2 l md /\
    Rabs (ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md)) <= Rrnd.maxval /\
    RrndOpToFunction OP md (evalRounded t1 l md) (evalRounded t2 l md) = ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md) in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> 0
    |_    => P
    end

  | Fma                _                     t1 t2 t3 => fun l md =>
    wellBehaved t1 l md /\ wellBehaved t2 l md /\ wellBehaved t3 l md /\
    Rabs (@Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md)) <= Rrnd.maxval

  | FmaExact           _                     t1 t2 t3 => fun l md =>
    wellBehaved t1 l md /\ wellBehaved t2 l md /\ wellBehaved t3 l md /\
    Rabs ((evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)) <= Rrnd.maxval /\
    @Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md) =
    (evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)

  | Nearbyint          _                     t        => fun l md => wellBehaved t l md

  | FastNearbyint      _                     t        => fun l md => wellBehaved t l md /\
    -2251799813685248 <= evalRounded t l md <= 2251799813685247

  | FastNearbyintToInt _                     t        => fun l md => wellBehaved t l md /\
    -2147483648 <= evalRounded t l md <= 2147483647 (* TODO: - ... - 1/2 <= ... < ... + 1/2 *)

  | TruncToInt         _                     t        => fun l md => wellBehaved t l md /\
   (- Int32.N / 2 <= Ztrunc (evalRounded t l md) <= Int32.N / 2 - 1)%Z

  | FloatInj           _                     t        => fun l md => wellBehaved t l md /\ Rabs (IZR (evalRounded t l md)) <= Rpow2 53

  | Sqrt               Tl' T'                t        => fun l md => wellBehaved t l md /\
    match T' return ArithExpr Tl' T' -> _ with
    | Integer => fun t' => 0 <= IZR (evalRounded t' l md)
    | _       => fun t' => 0 <= evalRounded t' l md
    end t

(*| Ldexp              _             n       t1 t2    => fun l md => wellBehaved t1 l md /\ wellBehaved t2 l md /\
    Rabs (evalRounded t1 l md)  <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec) /\
    IZR (n + evalRounded t2 l md) <= IZR Rrnd.emax *)

  | Let                _   _  _              t1 t2    => fun l md => wellBehaved t1 l md /\ wellBehaved t2 (evalRounded t1 l md, l) md

  | ArrayAcc           _                   a t        => fun l md => wellBehaved t l md /\
   (0 <= evalRounded t l md < Uint63.to_Z (PArray.length a))%Z

  | Assert             _   _           _     t
  | Postcond           _   _           _     t        => fun l md => wellBehaved t l md
  end.


Fixpoint postconditions {Tl T} (t : ArithExpr Tl T) : evalExprTypeRounded_list Tl -> _ :=
  match t with

  | Int                _             _
  | BinFl              _             _
  | Var                _     _                => fun l md => True


  | Op                 _ _     _     t1 t2
  | OpExact            _       _     t1 t2
(*| Ldexp              _         _   t1 t2  *)=> fun l md => postconditions t1 l md
                                                 /\ postconditions t2 l md

  | Fma                _             t1 t2 t3
  | FmaExact           _             t1 t2 t3 => fun l md => postconditions t1 l md
                                                 /\ postconditions t2 l md
                                                 /\ postconditions t3 l md

  | Nearbyint          _             t
  | FastNearbyint      _             t
  | FastNearbyintToInt _             t
  | TruncToInt         _             t
  | FloatInj           _             t
  | Sqrt               _ _           t        => fun l md => postconditions t l md

  | Let                _ _ _         t1 t2    => fun l md => postconditions t1 l md
                                                 /\ let x := evalRounded t1 l md in
                                                    postconditions t2 (x, l) md

  | ArrayAcc           _           a t        => fun l md => True

  | Assert             _ _         _ t        => fun l md => postconditions t l md

  | Postcond           _ _         P t        => fun l md => let P' := P (evalRounded t l md) in
                                                    uncurrify P' l /\ postconditions t l md
  end.


Definition fullyCorrect {Tl T} (t: ArithExpr Tl T) l md :=
  assertions t l md -> (wellBehaved t l md /\ postconditions t l md).


(* TODO: maybe move those proof obligations to the constructors *)
Fixpoint wellFormed {Tl T} (t: ArithExpr Tl T) := match t with
  | Int                _             n        => (- Z.pow_pos 2 (Int32.bits - 1) <=? n)%Z
                                              && (n <? Z.pow_pos 2 (Int32.bits - 1))%Z

  | BinFl              _             x        => is_finite_SF (Prim2SF x)

  | Var                _     _                => true

  | Op                 _ _     _     t1 t2
  | OpExact            _       _     t1 t2
(*| Ldexp              _         _   t1 t2  *)=> wellFormed t1 && wellFormed t2

  | Fma                _             t1 t2 t3
  | FmaExact           _             t1 t2 t3 => wellFormed t1 && wellFormed t2 && wellFormed t3

  | Let                _ _ _         t1 t2    => wellFormed t1 && wellFormed t2

  | ArrayAcc           _           a t        => wellFormed t && finite_array a

  | Nearbyint          _             t
  | FastNearbyint      _             t
  | FastNearbyintToInt _             t
  | TruncToInt         _             t
  | FloatInj           _             t
  | Sqrt               _ _           t
  | Assert             _ _         _ t
  | Postcond           _ _         _ t        => wellFormed t
  end.

Lemma Ztrunc_div_ : forall x y : Z, Ztrunc (IZR x / IZR y) = (x ÷ y)%Z.
Proof. intros x y.
destruct (Zeq_bool y 0) eqn:Hy; [apply Zeq_bool_eq in Hy | apply Zeq_bool_neq in Hy].
- rewrite Hy. unfold Rdiv. now rewrite Rinv_0, Rmult_0_r, Zquot.Zquot_0_r, Ztrunc_IZR.
- now apply Ztrunc_div.
Qed.

Lemma Zfloor_add : forall x n, (Zfloor x + n)%Z = Zfloor (x + IZR n).
Proof. intros x n. symmetry. apply Zfloor_imp. rewrite !plus_IZR.
rewrite Rplus_assoc, (Rplus_comm _ 1), <-Rplus_assoc.
split.
- apply Rplus_le_compat_r, Zfloor_lb.
- apply Rplus_lt_compat_r, Zfloor_ub.
Qed.

Lemma Zfloor_mul : forall x, 0 <= x -> Z.le (Zfloor x * Zfloor x)%Z (Zfloor (x * x)).
Proof. intros x Hx. apply Zfloor_lub. rewrite mult_IZR. apply Rmult_le_compat.
3, 4: apply Zfloor_lb.
all:  apply IZR_le, Zlt_succ_le; unfold Z.succ; apply lt_IZR; rewrite plus_IZR;
      apply Rle_lt_trans with (1 := Hx), Zfloor_ub.
Qed.

Lemma trunc_sqrt: forall n, Zfloor (sqrt (IZR n)) = Z.sqrt n.
Proof. intros [| p | p ]; [now rewrite sqrt_0, Zfloor_IZR | |].
- symmetry. apply Z.sqrt_unique. unfold Z.succ.
  rewrite <-(Zfloor_IZR (Z.pos p)), <-(sqrt_def (IZR (Z.pos p))) at 3 4
    by now apply IZR_le. rewrite Zfloor_add.
  split; [apply Zfloor_mul, sqrt_ge_0 |]. apply (Z.le_lt_trans _ (Z.pos p)).
  + apply le_IZR. rewrite <-(sqrt_def (IZR (Z.pos p))) at 3 by now apply IZR_le.
    apply Zfloor_lb.
  + apply lt_IZR. rewrite <-(sqrt_def (IZR (Z.pos p))) at 1 by now apply IZR_le.
    rewrite mult_IZR. apply Rmult_lt_compat; [apply sqrt_ge_0 | apply sqrt_ge_0 |
      rewrite <-Zfloor_add; rewrite plus_IZR; apply Zfloor_ub..].
- rewrite sqrt_neg; [| now apply IZR_le]. now rewrite Zfloor_IZR.
Qed.

Lemma evalReal_evalRounded {Tl T} :
  forall (t: ArithExpr Tl T) (lM : evalExprTypeRounded_list Tl) md,
  let lR := M2R_list lM in
  evalReal t lR md = M2R (evalRounded t lM md).
Proof.
induction t as [| | | Tl T OP | Tl OP | | | | | | | | Tl T | | | |].
- easy.
- simpl. intros _ _. now rewrite <-B2SF_Prim2B, SF2R_B2SF.
- intros lM. revert n. induction Tl as [| T Tl]; [now destruct n |].
  destruct T; (destruct n; [easy |]); simpl in *; apply IHTl.
- intros lM md lR. destruct OP; destruct T; simpl; unfold lR; rewrite (IHt1 lM), (IHt2 lM);
    try reflexivity; [| | | now unfold Rrnd.nearbyint, round, F2R, scaled_mantissa; simpl;
    rewrite !Rmult_1_r, Ztrunc_div_].
  + now rewrite <-plus_IZR.
  + now rewrite <-minus_IZR.
  + now rewrite <-mult_IZR.
- intros lM md lR. now destruct OP; simpl; unfold lR; rewrite (IHt1 lM), (IHt2 lM).
- intros lM md lR. simpl in *. unfold lR. now rewrite IHt1, IHt2, IHt3.
- intros lM md lR. simpl in *. unfold lR. now rewrite IHt1, IHt2, IHt3.
- intros lM md lR. simpl in *. unfold lR. now rewrite IHt.
- intros lM md lR. simpl in *. unfold lR. now rewrite IHt.
- intros lM md lR. simpl in *. unfold lR, Rrnd.nearbyint.
  now rewrite IHt, round_FIX_IZR.
- intros lM md lR. simpl in *. unfold lR. rewrite <-round_FIX_IZR.
  now rewrite IHt.
- intros lM md lR. simpl in *. unfold lR. apply IHt.
(*intros lM md lR. simpl in *. unfold lR, Rrnd.ldexp. rewrite bpow_exp.
  now rewrite IHt1, IHt2. *)
- intros lM md lR. simpl in *. unfold lR. destruct T.
  + unfold Rrnd.nearbyint, round, F2R, scaled_mantissa. simpl. rewrite 2Rmult_1_r.
    rewrite Ztrunc_floor by apply sqrt_ge_0. apply f_equal. rewrite IHt.
    apply trunc_sqrt.
  + now rewrite IHt.
- intros lM md lR. now destruct T1;
    unfold lR in *; simpl in *; rewrite IHt1;
    fold evalExprTypeReal_list in *; fold evalExprTypeRounded_list in *;
    specialize (IHt2 (evalRounded t1 lM md, lM)); simpl in IHt2;
    rewrite IHt2.
- intros lM md lR. simpl in *. unfold lR. now rewrite IHt, Ztrunc_IZR.
- easy.
- intros lM md lR. simpl in *. unfold lR. now apply IHt.
Qed.

Lemma wellBehaved_decompose {Tl T} :
  forall (t: ArithExpr Tl T) (l : evalExprTypeRounded_list Tl) md,
  wellBehaved t l md <-> wellDefined t l md /\ operationsExact t l md.
Proof.
induction t as [| | | Tl T OP | Tl OP | | | | | | | | Tl T | | | |].
- easy.
- easy.
- easy.
- intros l md. now destruct OP; simpl; rewrite IHt1, IHt2; [| | | destruct T].
- intros l md. now destruct OP; simpl; rewrite IHt1, IHt2.
- intros l md. simpl. now rewrite IHt1, IHt2, IHt3.
- intros l md. simpl. now rewrite IHt1, IHt2, IHt3.
- easy.
- intros l md. simpl. now rewrite IHt.
- intros l md. simpl. now rewrite IHt.
- intros l md. simpl. now rewrite IHt.
- intros l md. simpl. now rewrite IHt.
(*intros l md. simpl. now rewrite IHt1, IHt2. *)
- intros l md. simpl. now rewrite IHt.
- intros l md. simpl. now rewrite IHt1, IHt2.
- intros l md. simpl. now rewrite IHt.
- easy.
- easy.
Qed.


Lemma equivFloat_Int {Tl} : forall n (lC : evalExprTypeFloat_list Tl) md,
  (- Z.pow_pos 2 (Int32.bits - 1) <= n < Z.pow_pos 2 (Int32.bits - 1))%Z ->
  let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat (Int n) lC md) (evalRounded (Int n) lM md).
Proof. intros n lC md H lM. simpl.
split; [apply Int32.in_bounds_norm | apply Int32.norm_in_bounds].
unfold Int32.in_bounds, Int32.N. unfold Int32.bits. revert H.
cbn. lia.
Qed.

Lemma equivPrim_Int {Tl} : forall n (lP : evalExprTypePrim_list Tl),
  (- Z.pow_pos 2 (Int32.bits - 1) <= n < Z.pow_pos 2 (Int32.bits - 1))%Z ->
  let lM := P2M_list lP in
  eqExprTypePrim (evalPrim (Int n) lP) (evalRounded (Int n) lM mode_NE).
Proof. intros n lP H lM. unfold eqExprTypePrim. simpl. rewrite of_Z_spec.
rewrite cmod_small; [| cbn in H |- *; lia]. split; [| easy].
revert H. unfold Int32.in_bounds. cbn. lia.
Qed.

Lemma equivFloat_Op_ADD_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  Rabs (@Rrnd.Rnd md (evalRounded t1 lM md + evalRounded t2 lM md)) <= Rrnd.maxval ->
  eqExprTypeFloat (evalFloat (Op ADD t1 t2) lC md) (evalRounded (Op ADD t1 t2) lM md).
Proof. intros t1 t2 lC md lM [convt1 isconvt1] [convt2 isconvt2] H.
generalize (Bplus_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. simpl round_mode.
  apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]; [assumption.. |]. unfold eqExprTypeFloat; simpl.
  now unfold FPadd; rewrite H1, isconvt1, isconvt2.
Qed.

Lemma Prim2SF2R_Prim2B2R : forall x, SF2R radix2 (Prim2SF x) = B2R (Prim2B x).
Proof. intros x. now rewrite <-SF2R_B2SF, B2SF_Prim2B. Qed.

Lemma equivPrim_Op_ADD_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  Rabs (@Rrnd.Rnd mode_NE (evalRounded t1 lM mode_NE + evalRounded t2 lM mode_NE)) <= Rrnd.maxval ->
  eqExprTypePrim (evalPrim (Op ADD t1 t2) lP) (evalRounded (Op ADD t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [convt1 isconvt1] [convt2 isconvt2] H.
unfold eqExprTypePrim; simpl.
generalize (Bplus_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (Prim2B (evalPrim t1 lP)) (Prim2B (evalPrim t2 lP))).
rewrite <-add_equiv, <-3is_finite_SF_B2SF, <-3SF2R_B2SF, 3B2SF_Prim2B. rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. simpl round_mode.
  apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]; [assumption.. |]. unfold eqExprTypePrim. simpl.
unfold FloatOps.prec, FloatOps.emax, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax in *.
unfold HPrec_gt_0, HPrec_lt_emax in H1. now rewrite H1, isconvt1, isconvt2.
Qed.

Lemma equivFloat_Op_SUB_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  Rabs (@Rrnd.Rnd md (evalRounded t1 lM md - evalRounded t2 lM md)) <= Rrnd.maxval ->
  eqExprTypeFloat (evalFloat (Op SUB t1 t2) lC md) (evalRounded (Op SUB t1 t2) lM md).
Proof. intros t1 t2 lC md lM [convt1 isconvt1] [convt2 isconvt2] H.
generalize (Bminus_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. simpl round_mode.
  apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]; [assumption.. |]. unfold eqExprTypeFloat; simpl.
now unfold FPsub; rewrite H1, isconvt1, isconvt2.
Qed.

Lemma equivPrim_Op_SUB_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  Rabs (@Rrnd.Rnd mode_NE (evalRounded t1 lM mode_NE - evalRounded t2 lM mode_NE)) <= Rrnd.maxval ->
  eqExprTypePrim (evalPrim (Op SUB t1 t2) lP) (evalRounded (Op SUB t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [convt1 isconvt1] [convt2 isconvt2] H.
unfold eqExprTypePrim; simpl.
generalize (Bminus_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (Prim2B (evalPrim t1 lP)) (Prim2B (evalPrim t2 lP))).
rewrite <-sub_equiv, <-3is_finite_SF_B2SF, <-3SF2R_B2SF, 3B2SF_Prim2B. rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. simpl round_mode.
  apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]; [assumption.. |]. unfold eqExprTypePrim. simpl.
unfold FloatOps.prec, FloatOps.emax, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax in *.
unfold HPrec_gt_0, HPrec_lt_emax in H1. now rewrite H1, isconvt1, isconvt2.
Qed.

Lemma equivFloat_Op_MUL_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  Rabs (@Rrnd.Rnd md (evalRounded t1 lM md * evalRounded t2 lM md)) <= Rrnd.maxval ->
  eqExprTypeFloat (evalFloat (Op MUL t1 t2) lC md) (evalRounded (Op MUL t1 t2) lM md).
Proof. intros t1 t2 lC md lM [convt1 isconvt1] [convt2 isconvt2] H.
generalize (Bmult_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. apply Rle_lt_trans with Rrnd.maxval; [assumption |].
  apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]. unfold eqExprTypeFloat. simpl. unfold FPmul. rewrite H2.
split; [now apply andb_true_intro |]. rewrite H1.
unfold Rrnd.Rnd, SpecFloat.fexp, FLT_exp, SpecFloat.emin, Rrnd.emin. now rewrite isconvt1, isconvt2.
Qed.

Lemma equivPrim_Op_MUL_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  Rabs (@Rrnd.Rnd mode_NE (evalRounded t1 lM mode_NE * evalRounded t2 lM mode_NE)) <= Rrnd.maxval ->
  eqExprTypePrim (evalPrim (Op MUL t1 t2) lP) (evalRounded (Op MUL t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [convt1 isconvt1] [convt2 isconvt2] H.
unfold eqExprTypePrim; simpl.
generalize (Bmult_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (Prim2B (evalPrim t1 lP)) (Prim2B (evalPrim t2 lP))).
rewrite <-mul_equiv, <-3is_finite_SF_B2SF, <-3SF2R_B2SF, 3B2SF_Prim2B. rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. apply Rle_lt_trans with Rrnd.maxval; [assumption |].
  apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]. unfold eqExprTypePrim. simpl. unfold FPmul.
unfold FloatOps.prec, FloatOps.emax, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax in *.
unfold HPrec_gt_0, HPrec_lt_emax in H1, H2. rewrite H1, H2, isconvt1, isconvt2.
now split; [apply andb_true_intro |].
Qed.

Lemma equivFloat_Op_DIV_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  evalRounded t2 lM md <> 0 ->
  Rabs (@Rrnd.Rnd md (evalRounded t1 lM md / evalRounded t2 lM md)) <= Rrnd.maxval ->
  eqExprTypeFloat (evalFloat (Op DIV t1 t2) lC md) (evalRounded (Op DIV t1 t2) lM md).
Proof. intros t1 t2 lC md lM [convt1 isconvt1] [convt2 isconvt2] H0 H.
generalize (Bdiv_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. apply Rle_lt_trans with Rrnd.maxval; [assumption |].
  apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]; [now rewrite isconvt2 |]. unfold eqExprTypeFloat. simpl. unfold FPdiv.
rewrite H2. split; [assumption |]. rewrite H1.
unfold Rrnd.Rnd, SpecFloat.fexp, FLT_exp, SpecFloat.emin, Rrnd.emin. now rewrite isconvt1, isconvt2.
Qed.

Lemma equivPrim_Op_DIV_BinFloat {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  evalRounded t2 lM mode_NE <> 0 ->
  Rabs (@Rrnd.Rnd mode_NE (evalRounded t1 lM mode_NE / evalRounded t2 lM mode_NE)) <= Rrnd.maxval ->
  eqExprTypePrim (evalPrim (Op DIV t1 t2) lP) (evalRounded (Op DIV t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [convt1 isconvt1] [convt2 isconvt2] H0 H.
unfold eqExprTypePrim; simpl.
generalize (Bdiv_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (Prim2B (evalPrim t1 lP)) (Prim2B (evalPrim t2 lP))).
rewrite <-div_equiv, <-2is_finite_SF_B2SF, <-3SF2R_B2SF, 3B2SF_Prim2B. rewrite Rlt_bool_true.
2: { rewrite isconvt1, isconvt2. apply Rle_lt_trans with Rrnd.maxval; [assumption |].
  apply Rrnd.maxval_lt. }
intros [H1 [H2 H3]]; [now rewrite isconvt2 |]. unfold eqExprTypePrim. simpl. unfold FPdiv.
unfold FloatOps.prec, FloatOps.emax, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax in *.
unfold HPrec_gt_0, HPrec_lt_emax in H1, H2. now rewrite H1, H2, isconvt1, isconvt2.
Qed.

Lemma equivFloat_Op_ADD_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  - IZR (Int32.N / 2) <= IZR ((evalRounded t1 lM md) + (evalRounded t2 lM md)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypeFloat (evalFloat (Op ADD t1 t2) lC md) (evalRounded (Op ADD t1 t2) lM md).
Proof. intros t1 t2 lC md lM [bndt1 eqt1] [bndt2 eqt2] [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypeFloat. simpl. rewrite eqt1, eqt2.
split; [apply Int32.in_bounds_norm | now apply Int32.norm_in_bounds].
Qed.

Lemma equivPrim_Op_ADD_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  - IZR (Int32.N / 2) <= IZR ((evalRounded t1 lM mode_NE) + (evalRounded t2 lM mode_NE)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypePrim (evalPrim (Op ADD t1 t2) lP) (evalRounded (Op ADD t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [bndt1 eqt1] [bndt2 eqt2] [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypePrim. simpl in *.
rewrite <-eqt1, <-eqt2 in H1, H2 |- *.
now rewrite Sint63.add_spec, Sint63.cmod_small; [| cbn -[evalPrim] in *; lia].
Qed.

Lemma equivFloat_Op_SUB_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  - IZR (Int32.N / 2) <= IZR ((evalRounded t1 lM md) - (evalRounded t2 lM md)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypeFloat (evalFloat (Op SUB t1 t2) lC md) (evalRounded (Op SUB t1 t2) lM md).
Proof. intros t1 t2 lC md lM [bndt1 eqt1] [bndt2 eqt2] [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypeFloat. simpl. rewrite eqt1, eqt2.
split; [apply Int32.in_bounds_norm | now apply Int32.norm_in_bounds].
Qed.

Lemma equivPrim_Op_SUB_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  - IZR (Int32.N / 2) <= IZR ((evalRounded t1 lM mode_NE) - (evalRounded t2 lM mode_NE)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypePrim (evalPrim (Op SUB t1 t2) lP) (evalRounded (Op SUB t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [bndt1 eqt1] [bndt2 eqt2] [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypePrim. simpl in *.
rewrite <-eqt1, <-eqt2 in H1, H2 |- *.
now rewrite Sint63.sub_spec, Sint63.cmod_small; [| cbn -[evalPrim] in *; lia].
Qed.

Lemma equivFloat_Op_MUL_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  - IZR (Int32.N / 2) <= IZR ((evalRounded t1 lM md) * (evalRounded t2 lM md)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypeFloat (evalFloat (Op MUL t1 t2) lC md) (evalRounded (Op MUL t1 t2) lM md).
Proof. intros t1 t2 lC md lM [bndt1 eqt1] [bndt2 eqt2] [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypeFloat. simpl. rewrite eqt1, eqt2.
split; [apply Int32.in_bounds_norm | now apply Int32.norm_in_bounds].
Qed.

Lemma equivPrim_Op_MUL_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  - IZR (Int32.N / 2) <= IZR ((evalRounded t1 lM mode_NE) * (evalRounded t2 lM mode_NE)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypePrim (evalPrim (Op MUL t1 t2) lP) (evalRounded (Op MUL t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [bndt1 eqt1] [bndt2 eqt2] [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypePrim. simpl in *.
rewrite <-eqt1, <-eqt2 in H1, H2 |- *.
now rewrite Sint63.mul_spec, Sint63.cmod_small; [| cbn -[evalPrim] in *; lia].
Qed.

Lemma equivFloat_Op_DIV_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
 (evalRounded t2 lM md <> 0)%Z ->
  - IZR (Int32.N / 2) <= IZR (Z.quot (evalRounded t1 lM md) (evalRounded t2 lM md)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypeFloat (evalFloat (Op DIV t1 t2) lC md) (evalRounded (Op DIV t1 t2) lM md).
Proof. intros t1 t2 lC md lM [bndt1 eqt1] [bndt2 eqt2] H0 [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypeFloat. simpl. rewrite eqt1, eqt2.
split; [apply Int32.in_bounds_norm | now apply Int32.norm_in_bounds].
Qed.

Lemma equivPrim_Op_DIV_Integer {Tl} : forall (t1 t2 : ArithExpr Tl Integer)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
 (evalRounded t2 lM mode_NE <> 0)%Z ->
  - IZR (Int32.N / 2) <= IZR (Z.quot (evalRounded t1 lM mode_NE) (evalRounded t2 lM mode_NE)) <= IZR (Int32.N / 2 - 1) ->
  eqExprTypePrim (evalPrim (Op DIV t1 t2) lP) (evalRounded (Op DIV t1 t2) lM mode_NE).
Proof. intros t1 t2 lP lM [bndt1 eqt1] [bndt2 eqt2] H0 [H1 H2].
rewrite <-opp_IZR in H1. apply le_IZR in H1, H2. unfold eqExprTypePrim. simpl in *.
rewrite <-eqt1 in H1, H2 |- *. rewrite <-eqt2 in H0, H1, H2 |- *.
assert (H: Sint63.to_Z (evalPrim t1 lP) <> Sint63.to_Z Sint63.min_int).
{ revert bndt1. unfold Int32.in_bounds. cbn -[evalPrim]. lia. } clear eqt1.
now rewrite Sint63.div_spec; [| left].
Qed.


Lemma equivFloat_OpExact {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat) OP
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  match OP with DIV => evalRounded t2 lM md <> 0 | _ => True end ->
  Rabs (ROpToFunction OP (evalRounded t1 lM md) (evalRounded t2 lM md)) <= Rrnd.maxval ->
  RrndOpToFunction OP md (evalRounded t1 lM md) (evalRounded t2 lM md) = ROpToFunction OP (evalRounded t1 lM md) (evalRounded t2 lM md) ->
  eqExprTypeFloat (evalFloat (OpExact OP t1 t2) lC md) (evalRounded (OpExact OP t1 t2) lM md).
Proof. intros t1 t2 OP lC md lM eqt1 eqt2 H0 H1 H2. simpl.
rewrite <-H2 in H1 |- *. destruct OP.
- now apply equivFloat_Op_ADD_BinFloat.
- now apply equivFloat_Op_SUB_BinFloat.
- now apply equivFloat_Op_MUL_BinFloat.
- now apply equivFloat_Op_DIV_BinFloat.
Qed.

Lemma equivPrim_OpExact {Tl} : forall (t1 t2 : ArithExpr Tl BinFloat) OP
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  match OP with DIV => evalRounded t2 lM mode_NE <> 0 | _ => True end ->
  Rabs (ROpToFunction OP (evalRounded t1 lM mode_NE) (evalRounded t2 lM mode_NE)) <= Rrnd.maxval ->
  RrndOpToFunction OP mode_NE (evalRounded t1 lM mode_NE) (evalRounded t2 lM mode_NE) = ROpToFunction OP (evalRounded t1 lM mode_NE) (evalRounded t2 lM mode_NE) ->
  eqExprTypePrim (evalPrim (OpExact OP t1 t2) lP) (evalRounded (OpExact OP t1 t2) lM mode_NE).
Proof. intros t1 t2 OP lC lM eqt1 eqt2 H0 H1 H2. simpl.
rewrite <-H2 in H1 |- *. destruct OP.
- now apply equivPrim_Op_ADD_BinFloat.
- now apply equivPrim_Op_SUB_BinFloat.
- now apply equivPrim_Op_MUL_BinFloat.
- now apply equivPrim_Op_DIV_BinFloat.
Qed.

Lemma equivFloat_Fma {Tl} : forall (t1 t2 t3 : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  eqExprTypeFloat (evalFloat t3 lC md) (evalRounded t3 lM md) ->
  Rabs (@Rrnd.fma md (evalRounded t1 lM md) (evalRounded t2 lM md) (evalRounded t3 lM md)) <= Rrnd.maxval ->
  eqExprTypeFloat (evalFloat (Fma t1 t2 t3) lC md) (evalRounded (Fma t1 t2 t3) lM md).
Proof. intros t1 t2 t3 lC md lM [convt1 isconvt1] [convt2 isconvt2] [convt3 isconvt3] H.
generalize (Bfma_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md) (evalFloat t3 lC md)).
unfold eqExprTypeFloat. simpl. rewrite Rlt_bool_true.
{ intros [H1 [H2 H3]]; [assumption.. |]. now unfold FPfma; rewrite H1, isconvt1, isconvt2, isconvt3. }
rewrite isconvt1, isconvt2, isconvt3. simpl round_mode.
apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.
Qed.

Lemma equivPrim_Fma {Tl} : forall (t1 t2 t3 : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  eqExprTypePrim (evalPrim t3 lP) (evalRounded t3 lM mode_NE) ->
  Rabs (@Rrnd.fma mode_NE (evalRounded t1 lM mode_NE) (evalRounded t2 lM mode_NE) (evalRounded t3 lM mode_NE)) <= Rrnd.maxval ->
  eqExprTypePrim (evalPrim (Fma t1 t2 t3) lP) (evalRounded (Fma t1 t2 t3) lM mode_NE).
Proof. intros t1 t2 t3 lP lM [convt1 isconvt1] [convt2 isconvt2] [convt3 isconvt3] H.
generalize (Bfma_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE
 (P2C (evalPrim t1 lP)) (P2C (evalPrim t2 lP)) (P2C (evalPrim t3 lP))).
unfold eqExprTypePrim. simpl.
unfold isConversionPrim in isconvt1, isconvt2, isconvt3.
rewrite <-4is_finite_SF_B2SF, 3B2SF_Prim2B.
rewrite <-B2SF_Prim2B, SF2R_B2SF in isconvt1, isconvt2, isconvt3.
 rewrite Rlt_bool_true.
{ intros [H1 [H2 H3]]; [assumption.. |]. rewrite Prim2SF_B2Prim. split; [easy |].
  unfold FPfma. change Rrnd.prec with prec in H1 |- *. change Rrnd.emax with emax in H1 |- *.
  rewrite SF2R_B2SF. now rewrite H1, isconvt1, isconvt2, isconvt3. }
change Rrnd.prec with prec. change Rrnd.emax with emax.
rewrite isconvt1, isconvt2, isconvt3. simpl round_mode.
apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.
Qed.

Lemma equivFloat_FmaExact {Tl} : forall (t1 t2 t3 : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t1 lC md) (evalRounded t1 lM md) ->
  eqExprTypeFloat (evalFloat t2 lC md) (evalRounded t2 lM md) ->
  eqExprTypeFloat (evalFloat t3 lC md) (evalRounded t3 lM md) ->
  Rabs (evalRounded t1 lM md * evalRounded t2 lM md + evalRounded t3 lM md) <= Rrnd.maxval ->
  (@Rrnd.fma md (evalRounded t1 lM md) (evalRounded t2 lM md) (evalRounded t3 lM md))
     = evalRounded t1 lM md * evalRounded t2 lM md + evalRounded t3 lM md->
  eqExprTypeFloat (evalFloat (FmaExact t1 t2 t3) lC md) (evalRounded (FmaExact t1 t2 t3) lM md).
Proof. intros t1 t2 t3 lC md lM [convt1 isconvt1] [convt2 isconvt2] [convt3 isconvt3] H0 H1.
simpl. rewrite <-H1 in H0 |- *. now apply equivFloat_Fma.
Qed.

Lemma equivPrim_FmaExact {Tl} : forall (t1 t2 t3 : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t1 lP) (evalRounded t1 lM mode_NE) ->
  eqExprTypePrim (evalPrim t2 lP) (evalRounded t2 lM mode_NE) ->
  eqExprTypePrim (evalPrim t3 lP) (evalRounded t3 lM mode_NE) ->
  Rabs (evalRounded t1 lM mode_NE * evalRounded t2 lM mode_NE + evalRounded t3 lM mode_NE) <= Rrnd.maxval ->
  (@Rrnd.fma mode_NE (evalRounded t1 lM mode_NE) (evalRounded t2 lM mode_NE) (evalRounded t3 lM mode_NE))
    = evalRounded t1 lM mode_NE * evalRounded t2 lM mode_NE + evalRounded t3 lM mode_NE ->
  eqExprTypePrim (evalPrim (FmaExact t1 t2 t3) lP) (evalRounded (FmaExact t1 t2 t3) lM mode_NE).
Proof. intros t1 t2 t3 lP lM [convt1 isconvt1] [convt2 isconvt2] [convt3 isconvt3] H0 H1.
simpl. rewrite <-H1 in H0 |- *. now apply equivPrim_Fma.
Qed.

Lemma equivFloat_Nearbyint {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
  eqExprTypeFloat (evalFloat (Nearbyint t) lC md) (evalRounded (Nearbyint t) lM md).
Proof. intros t lC md lM [fint eqt].
generalize (Bnearbyint_correct _ _ HPrec_lt_emax mode_NE (evalFloat t lC md)).
unfold eqExprTypeFloat. simpl. intros [H0 [H1 _]]. unfold FPnearbyint. rewrite H1, H0.
now split; [| rewrite <-eqt].
Qed.

Lemma equivPrim_Nearbyint {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
  eqExprTypePrim (evalPrim (Nearbyint t) lP) (evalRounded (Nearbyint t) lM mode_NE).
Proof. intros t lP lM [fint eqt].
generalize (Bnearbyint_correct _ _ HPrec_lt_emax mode_NE (P2C (evalPrim t lP))).
unfold eqExprTypePrim. simpl.
rewrite <-2is_finite_SF_B2SF.
intros [H0 [H1 _]]. unfold FPnearbyint.
rewrite <-B2SF_Prim2B, SF2R_B2SF, Prim2B_B2Prim.
change prec with Rrnd.prec. change emax with Rrnd.emax.
rewrite <-eqt, H1, H0. rewrite B2SF_Prim2B. split; [easy |].
now rewrite <-B2SF_Prim2B, SF2R_B2SF.
Qed.

Lemma ZnearestE_plus_even : forall x n, Z.even n = true -> (ZnearestE x + n = ZnearestE (x + IZR n))%Z.
Proof. intros x n Hneven. unfold ZnearestE, Zceil.
rewrite Ropp_plus_distr, <-opp_IZR, <-2Zfloor_add, plus_IZR.
ring_simplify (x + IZR n - (IZR (Zfloor x) + IZR n)).
rewrite Z.even_add_even by now apply Z.even_spec.
case negb, Rcompare; ring.
Qed.

Lemma aux_2 : generic_format radix2 (fexp prec emax) (Rpow2 53 - 1).
Proof.
simpl. rewrite <-minus_IZR. simpl. apply generic_format_FLT.
exists (Float radix2 9007199254740991 0); [| easy..].
unfold F2R. simpl. symmetry. apply Rmult_1_r.
Qed.

Lemma aux_3 : forall x', x' <= Rpow2 53 - 1 ->
  round radix2 (fexp prec emax) ZnearestE x' < Rpow2 53.
Proof. intros x' Hx'.
apply Rle_lt_trans with (Rpow2 53 - 1); [| lra]. now apply round_le_generic;
 [now apply FLT_exp_valid | apply valid_rnd_N | apply aux_2 |].
Qed.

Lemma aux_4 : forall (x : binary_float prec emax),
  -2251799813685248 <= B2R x <= 2251799813685247 ->
  Rpow2 52 <= B2R x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1.
Proof. intros x Hx.
cbn -[IZR Rplus Ropp Rmult Rinv]. unfold F2R; simpl. lra.
Qed.

Lemma fastnearbyint_correct : forall x, is_finite (Prim2B x) = true ->
    -2251799813685248 <= B2R (Prim2B x) <= 2251799813685247 -> (* TODO: float --> R *)
    Uint63.to_Z (normfr_mantissa (fst (frshiftexp (x + 6755399441055744)))) =
   (ZnearestE (SF2R radix2 (Prim2SF x)) + 6755399441055744)%Z.
Proof. intros x Hfinx Hx.

(* C3 *)
destruct frshiftexp as (m, e) eqn:Heqaux. simpl.

(* C4 *)
rewrite normfr_mantissa_equiv.


(* A2 *)
assert (Hbndexpr_aux : Rpow2 52 <= B2R (Prim2B x) + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1)
  by now apply aux_4.
(* A3 <- A2 *)
generalize (Bplus_correct prec emax Hprec Hmax mode_NE (Prim2B x) (Prim2B 6755399441055744)
  Hfinx).
rewrite Rlt_bool_true; [intros [Hplus_1 [Hplus_2 Hplus_3]]; [easy |] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  generalize (aux_4 _ Hx); cbn -[Rle Rplus IZR Prim2B]. lra. }
(* clear Hplus_2 Hplus_3 Hfinx. *)
(* A4 <- A3, A2 *)
assert (Hx' : Rpow2 52 <= B2R (Prim2B (x + 6755399441055744)) < Rpow2 53).
{ rewrite add_equiv, Hplus_1. split.
  - now apply round_ge_generic;
     [apply FLT_exp_valid | apply valid_rnd_N | apply generic_format_bpow | apply aux_4].
  - now apply aux_3, aux_4. }
(* clear Hplus_1. *)
(* A5 <- A4 *)
assert (Hfinsx : is_finite_strict (Prim2B (x + 6755399441055744)) = true).
{ unfold is_finite_strict. destruct (Prim2B (x + 6755399441055744)); [.. | easy]; simpl in Hx'; lra. }
(* clear Hx. *)
(* A6 <- A5, C3 *)
generalize (frshiftexp_equiv (x + 6755399441055744)).
rewrite Heqaux. intros Hfrexp_aux. simpl.
generalize (Bfrexp_correct prec emax Hprec (Prim2B (x + 6755399441055744)) Hfinsx).
rewrite <-Hfrexp_aux. intros [Hfrexp_1 [Hfrexp_2 Hfrexp_3]]; [easy |].
clear Hfinsx Heqaux Hfrexp_aux (* Hfrexp_1 Hfrexp_3 *).
(* A7 <- A6 *)
generalize (Bnormfr_mantissa_correct prec emax Hprec (Prim2B m) Hfrexp_2). intros Hnormfr.
(* clear Hfrexp_2. *)
(* C5 <- A7, C4 *)
destruct (Prim2B m) as [| | | sm mm em Hem]; [easy.. |].

(* C6 <- C5 *)
destruct Hnormfr as [Hnormfr_1 [Hnormfr_2 ->]]. rewrite Hnormfr_1. simpl.
(* clear Hem Hnormfr_1 Hnormfr_2. *)

(* <- *)
set (e' := mag_val _ _ (mag radix2 (B2R (Prim2B (x + 6755399441055744))))).
fold e' in Hfrexp_3. rewrite add_equiv in Hx', Hfrexp_1.
rewrite Hfrexp_3 in Hfrexp_1. rewrite Hfrexp_1 in Hplus_1, Hx'.
assert (He' : e' = 53%Z).
{ clear -Hx' Hfrexp_2. rewrite <-(Rabs_pos_eq (B2R _)) in Hx'.
  2: { clear Hfrexp_2. clearbody e'. generalize (bpow_gt_0 radix2 e').
    cbn -[Rle Rlt Rmult B2R prec] in Hx'. nra. }
  revert Hx' Hfrexp_2. generalize (Rabs (B2R (B754_finite sm mm (- prec) Hem))).
  intros r H0 Hr. generalize H0; intros H1.
  destruct H0 as [H00 H01]. destruct H1 as [H10 H11].
  apply (Rmult_le_compat_r (Rpow2 (-54))) in H00; [| now apply bpow_ge_0].
  apply (Rmult_lt_compat_r (Rpow2 (-54))) in H01; [| now apply bpow_gt_0].
  apply (Rmult_le_compat_r (Rpow2 (-52))) in H10; [| now apply bpow_ge_0].
  apply (Rmult_lt_compat_r (Rpow2 (-52))) in H11; [| now apply bpow_gt_0].
  rewrite <-bpow_plus in H00, H01, H10, H11. simpl Z.add in H00, H01, H10, H11.
  assert (Hr' : 0 < r) by lra.
  change (/ 2) with (Rpow2 (-1)) in Hr. change 1 with (Rpow2 0) in Hr.
  assert (Haux: Rpow2 (-54) * Rpow2 (e') < 1 < Rpow2 (-52) * Rpow2 (e')) by nra.
  change 1 with (Rpow2 0) in Haux. rewrite <-2bpow_plus in Haux.
  destruct Haux as [Hauxl Hauxr]. apply lt_bpow in Hauxl, Hauxr. lia. }
rewrite He' in Hplus_1. rewrite <-2Prim2SF2R_Prim2B2R in Hplus_1.
unfold B2R, F2R in Hplus_1. simpl in Hplus_1. field_simplify in Hplus_1; [| lra].
clear -Hbndexpr_aux Hplus_1 Hx'. destruct sm; [unfold B2R, F2R in Hx'; simpl in Hx' |].
{ assert (IZR (Z.neg mm) < 0) by now apply IZR_lt. cbn -[IZR Rle Rmult Rinv bpow] in Hx'.
  generalize (bpow_gt_0 radix2 e'). nra. }
simpl in Hplus_1. apply eq_IZR. rewrite Hplus_1.
unfold round, F2R, scaled_mantissa; simpl. unfold cexp.
rewrite <-2Prim2SF2R_Prim2B2R in Hbndexpr_aux.
rewrite mag_unique_pos with (e := 53%Z) by (simpl Z.sub; lra).
cbn. unfold F2R. simpl. rewrite 3Rmult_1_r. f_equal.
symmetry. now apply ZnearestE_plus_even.
Qed.

Lemma equivFloat_FastNearbyint {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
 -2251799813685248 <= evalRounded t lM md <= 2251799813685247 ->
  eqExprTypeFloat (evalFloat (FastNearbyint t) lC md) (evalRounded (FastNearbyint t) lM md).
Proof. intros t lC md lM [finx eqt] [Hx0 Hx1]. simpl.
unfold eqExprTypeFloat, convertibleFloat, isConversionFloat in *.
change Rrnd.prec with prec in *. change Rrnd.emax with emax in *.
rewrite <-eqt in Hx0, Hx1 |- *. set (x := evalFloat t lC md).
fold x in finx, Hx0, Hx1 |- *.

generalize (Bplus_correct prec emax Hprec Hmax mode_NE x (Prim2B 6755399441055744) finx eq_refl).
rewrite Rlt_bool_true; [intros [Hplus_1 [Hplus_2 Hplus_3]] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  cut (Rpow2 52 <= @B2R prec emax x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
   [unfold bpow, Z.pow_pos; simpl; lra |]. now apply aux_4. }
generalize (Bminus_correct prec emax Hprec Hmax mode_NE
  (@Bplus prec emax _ _ mode_NE x (Prim2B 6755399441055744)) (Prim2B 6755399441055744) Hplus_2 eq_refl).
rewrite Rlt_bool_true; [intros [Hminus_1 [Hminus_2 Hminus_3]] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  rewrite Hplus_1. unfold round, F2R, scaled_mantissa, cexp. simpl Fnum. simpl Fexp.
  rewrite mag_unique_pos with (e := 53%Z); [cbn; unfold F2R; simpl; rewrite 3Rmult_1_r |].
  2: { cut (Rpow2 52 <= @B2R prec emax x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
   [unfold bpow, Z.pow_pos; simpl; lra |]. now apply aux_4. }
  rewrite <-2minus_IZR; simpl. unfold Z.sub. rewrite ZnearestE_plus_even by easy.
  rewrite opp_IZR. rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r, <-opp_IZR.
  generalize (valid_rnd_N (fun n => negb (Z.even n))). intros Hmon.
  apply Hmon in Hx0, Hx1. rewrite Generic_proof.Znearest_IZR in Hx0, Hx1.
  split; apply IZR_le; lia. } split; [easy |].
unfold FPsub, FPadd. change Rrnd.prec with prec. change Rrnd.emax with emax.
unfold HPrec_gt_0, HPrec_lt_emax.
rewrite Hminus_1, Hplus_1. set (x' := round _ _ _ (_ + _)).
assert (Hx' : x' = x') by easy. unfold x' at 2 in Hx'. clearbody x'.
unfold round, F2R, scaled_mantissa, cexp in Hx'. simpl in Hx'.
rewrite mag_unique_pos with (e := 53%Z) in Hx'.
2: { cut (Rpow2 52 <= @B2R prec emax x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
 [unfold bpow, Z.pow_pos; simpl; lra |]. now apply aux_4. }
cbn in Hx' |- *. unfold F2R in Hx' |- *. simpl in Hx' |- *. rewrite 3Rmult_1_r in Hx'.
rewrite <-ZnearestE_plus_even, plus_IZR in Hx' by easy. rewrite Hx'.
ring_simplify (IZR (ZnearestE (@B2R prec emax x)) + 6755399441055744 - 6755399441055744 * 1).
unfold Rrnd.nearbyint. unfold round at 2. unfold F2R, scaled_mantissa; simpl.
rewrite 2Rmult_1_r. apply round_generic; [apply valid_rnd_N |].
clear -Hx0 Hx1. apply (valid_rnd_N (fun n => negb (Z.even n))) in Hx0, Hx1.
rewrite Generic_proof.Znearest_IZR in Hx0, Hx1. apply generic_format_FLT.
now exists (Float radix2 (ZnearestE (@B2R prec emax x)) 0); [unfold F2R; simpl; ring | simpl; lia |].
Qed.

Lemma equivPrim_FastNearbyint {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
 -2251799813685248 <= evalRounded t lM mode_NE <= 2251799813685247 ->
  eqExprTypePrim (evalPrim (FastNearbyint t) lP) (evalRounded (FastNearbyint t) lM mode_NE).
Proof. intros t lP lM [finx eqt] [Hx0 Hx1]. simpl.
unfold eqExprTypePrim, convertiblePrim, isConversionPrim in *.
rewrite <-B2SF_Prim2B, is_finite_SF_B2SF in finx |- *.
rewrite <-eqt, Prim2SF2R_Prim2B2R in Hx0, Hx1 |- *.
set (x := (evalPrim t lP)). fold x in finx, Hx0, Hx1.
rewrite sub_equiv, add_equiv.
generalize (Bplus_correct prec emax Hprec Hmax mode_NE (Prim2B x) (Prim2B 6755399441055744) finx).
rewrite Rlt_bool_true; [intros [Hplus_1 [Hplus_2 Hplus_3]]; [easy |] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  cut (Rpow2 52 <= B2R (Prim2B x) + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
   [unfold bpow, Z.pow_pos; simpl; lra |]. now apply aux_4. }
generalize (Bminus_correct prec emax Hprec Hmax mode_NE
  (Bplus mode_NE (Prim2B x) (Prim2B 6755399441055744)) (Prim2B 6755399441055744) Hplus_2).
rewrite Rlt_bool_true; [intros [Hminus_1 [Hminus_2 Hminus_3]]; [easy |] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  rewrite Hplus_1. unfold round, F2R, scaled_mantissa, cexp. simpl Fnum. simpl Fexp.
  rewrite mag_unique_pos with (e := 53%Z); [cbn; unfold F2R; simpl; rewrite 3Rmult_1_r |].
  2: { cut (Rpow2 52 <= B2R (Prim2B x) + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
   [unfold bpow, Z.pow_pos; simpl; lra |]. now apply aux_4. }
  rewrite <-2minus_IZR; simpl. unfold Z.sub. rewrite ZnearestE_plus_even by easy.
  rewrite opp_IZR. rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r, <-opp_IZR.
  generalize (valid_rnd_N (fun n => negb (Z.even n))). intros Hmon.
  apply Hmon in Hx0, Hx1. rewrite Generic_proof.Znearest_IZR in Hx0, Hx1.
  split; apply IZR_le; lia. } split; [easy |].
rewrite SF2R_B2SF, Hminus_1, Hplus_1. set (x' := round _ _ _ (_ + _)).
assert (Hx' : x' = x') by easy. unfold x' at 2 in Hx'. clearbody x'.
unfold round, F2R, scaled_mantissa, cexp in Hx'. simpl in Hx'.
rewrite mag_unique_pos with (e := 53%Z) in Hx'.
2: { cut (Rpow2 52 <= B2R (Prim2B x) + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
 [unfold bpow, Z.pow_pos; simpl; lra |]. now apply aux_4. }
cbn in Hx' |- *. unfold F2R in Hx' |- *. simpl in Hx' |- *. rewrite 3Rmult_1_r in Hx'.
rewrite <-ZnearestE_plus_even, plus_IZR in Hx' by easy. rewrite Hx'.
ring_simplify (IZR (ZnearestE (B2R (Prim2B x))) + 6755399441055744 - 6755399441055744 * 1).
unfold Rrnd.nearbyint. unfold round at 2. unfold F2R, scaled_mantissa; simpl.
rewrite 2Rmult_1_r. apply round_generic; [apply valid_rnd_N |].
clear -Hx0 Hx1. apply (valid_rnd_N (fun n => negb (Z.even n))) in Hx0, Hx1.
rewrite Generic_proof.Znearest_IZR in Hx0, Hx1. apply generic_format_FLT.
now exists (Float radix2 (ZnearestE (B2R (Prim2B x))) 0); [unfold F2R; simpl; ring | simpl; lia |].
Qed.

Lemma equivFloat_FastNearbyintToInt {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
  (-2147483648 <= evalRounded t lM md <= 2147483647)%R ->
  eqExprTypeFloat (evalFloat (FastNearbyintToInt t) lC md) (evalRounded (FastNearbyintToInt t) lM md).
Proof. intros t lC md lM [finx eqt] [Hx0 Hx1]. simpl.
unfold eqExprTypeFloat, convertibleFloat, isConversionFloat in *.
change Rrnd.prec with prec in *. change Rrnd.emax with emax in *.
rewrite <-eqt in Hx0, Hx1 |- *. set (x := evalFloat t lC md).
fold x in finx, Hx0, Hx1 |- *.

generalize (Bplus_correct prec emax Hprec Hmax mode_NE x (Prim2B 6755399441055744) finx eq_refl).
rewrite Rlt_bool_true; [intros [Hplus_1 [Hplus_2 _]] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  cut (Rpow2 52 <= @B2R prec emax x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
   [unfold bpow, Z.pow_pos; simpl; lra |]. apply aux_4. lra. }
generalize (Bminus_correct prec emax Hprec Hmax mode_NE
  (@Bplus prec emax _ _ mode_NE x (Prim2B 6755399441055744)) (Prim2B 6755399441055744) Hplus_2 eq_refl).
rewrite Rlt_bool_true; [intros [Hminus_1 _] |].
2: { apply Rlt_trans with (Rpow2 53); [| now apply bpow_lt].
  rewrite <-round_NE_abs by now apply FLT_exp_valid. apply aux_3, Rabs_le.
  rewrite Hplus_1. unfold round, F2R, scaled_mantissa, cexp. simpl Fnum. simpl Fexp.
  rewrite mag_unique_pos with (e := 53%Z); [cbn; unfold F2R; simpl; rewrite 3Rmult_1_r |].
  2: { cut (Rpow2 52 <= @B2R prec emax x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
   [unfold bpow, Z.pow_pos; simpl; lra |]. apply aux_4. lra. }
  rewrite <-2minus_IZR; simpl. unfold Z.sub. rewrite ZnearestE_plus_even by easy.
  rewrite opp_IZR. rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r, <-opp_IZR.
  generalize (valid_rnd_N (fun n => negb (Z.even n))). intros Hmon.
  apply Hmon in Hx0, Hx1. rewrite Generic_proof.Znearest_IZR in Hx0, Hx1.
  split; apply IZR_le; lia. } split; [apply Int32.in_bounds_norm |].
unfold FPsub, FPadd. change Rrnd.prec with prec. change Rrnd.emax with emax.
unfold FPtrunc, HPrec_gt_0, HPrec_lt_emax.
assert (H : @Btrunc Rrnd.prec Rrnd.emax
     (@Bminus prec emax Hprec Hmax mode_NE (@Bplus prec emax Hprec Hmax mode_NE x (Prim2B 6755399441055744))
        (Prim2B 6755399441055744)) = ZnearestE (@B2R prec emax x)).
{ apply eq_IZR. rewrite Btrunc_correct by easy.
  change Rrnd.prec with prec. change Rrnd.emax with emax.
  rewrite Hminus_1, Hplus_1. set (x' := round _ _ _ (_ + _)).
assert (Hx' : x' = x') by easy. unfold x' at 2 in Hx'. clearbody x'.
unfold round, F2R, scaled_mantissa, cexp in Hx'. simpl in Hx'.
rewrite mag_unique_pos with (e := 53%Z) in Hx'.
2: { cut (Rpow2 52 <= @B2R prec emax x + B2R (Prim2B 6755399441055744) <= Rpow2 53 - 1);
 [unfold bpow, Z.pow_pos; simpl; lra |]. apply aux_4. lra. }
cbn in Hx' |- *. unfold F2R in Hx' |- *. simpl in Hx' |- *. rewrite 3Rmult_1_r in Hx'.
rewrite <-ZnearestE_plus_even, plus_IZR in Hx' by easy. rewrite Hx'.
ring_simplify (IZR (ZnearestE (@B2R prec emax x)) + 6755399441055744 - 6755399441055744 * 1).
rewrite round_generic. 2: apply valid_rnd_ZR.
{ apply round_generic; [apply valid_rnd_N |].
  clear -Hx0 Hx1. apply (valid_rnd_N (fun n => negb (Z.even n))) in Hx0, Hx1.
  rewrite Generic_proof.Znearest_IZR in Hx0, Hx1. apply generic_format_FLT.
now exists (Float radix2 (ZnearestE (@B2R prec emax x)) 0); [unfold F2R; simpl; ring | simpl; lia |]. }
apply generic_round_generic; auto with typeclass_instances; [now apply fexp_correct |].
rewrite <-round_FIX_IZR. apply generic_format_round; auto with typeclass_instances. }

rewrite Int32.norm_in_bounds; [easy |]. rewrite H.
split; cbn.
- apply Z.le_trans with (2 := Znearest_ge_floor _ _). now apply Zfloor_lub.
- apply Z.le_trans with (1 := Znearest_le_ceil _ _). now apply Zceil_glb.
Qed.

Lemma equivPrim_FastNearbyintToInt {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
  -2147483648 <= evalRounded t lM mode_NE <= 2147483647 ->
  eqExprTypePrim (evalPrim (FastNearbyintToInt t) lP) (evalRounded (FastNearbyintToInt t) lM mode_NE).
Proof. intros t lP lM [finx eqt] H. simpl.
unfold eqExprTypePrim, convertiblePrim, isConversionPrim in *.
rewrite <-B2SF_Prim2B, is_finite_SF_B2SF in finx.
rewrite <-eqt, Prim2SF2R_Prim2B2R in H |- *.
set (x := evalPrim t lP). generalize (fastnearbyint_correct x).
set (i := normfr_mantissa _).
intros Hx. rewrite Sint63.sub_spec. unfold to_Z. cbn in H. fold x in H.
destruct H as [Hx0 Hx1]. set (Rx := B2R (Prim2B x)). fold Rx in Hx0, Hx1.
assert (HRx : (-2147483648 <= ZnearestE Rx <= 2147483647)%Z).
{ split; cbn.
  - apply Z.le_trans with (2 := Znearest_ge_floor _ _). now apply Zfloor_lub.
  - apply Z.le_trans with (1 := Znearest_le_ceil _ _). now apply Zceil_glb. }
assert (Hi : (φ (i)%uint63 < φ (min_int)%uint63)%Z).
{ rewrite Hx; [| easy | unfold Rx in Hx0, Hx1; lra].
  unfold min_int, Uint63.to_Z, x. simpl.
  rewrite Prim2SF2R_Prim2B2R. fold x Rx. lia. }
destruct (Uint63.ltbP i min_int) as [_ | Hi_]; [| easy].
rewrite Hx; [| easy | unfold Rx in Hx0, Hx1; lra]. cbn.
unfold Z.sub. rewrite <-Z.add_assoc. simpl. rewrite Z.add_0_r.
rewrite cmod_small; [| rewrite Prim2SF2R_Prim2B2R; fold Rx; cbn; lia].
rewrite Prim2SF2R_Prim2B2R. now fold Rx.
Qed.

Lemma equivFloat_TruncToInt {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
  (- Int32.N / 2 <= Ztrunc (evalRounded t lM md) <= Int32.N / 2 - 1)%Z ->
  eqExprTypeFloat (evalFloat (TruncToInt t) lC md) (evalRounded (TruncToInt t) lM md).
Proof. intros t lC md lM [fint eqt] H.
generalize (Btrunc_correct _ _ HPrec_lt_emax (evalFloat t lC md)).
unfold eqExprTypeFloat. simpl. rewrite round_FIX_IZR. intros H0. apply eq_IZR in H0.
rewrite <-eqt, <-H0 in H |- *. unfold FPtrunc.
rewrite Int32.norm_in_bounds; [| easy]. now split.
Qed.

Lemma equivPrim_TruncToInt {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
  (- Int32.N / 2 <= Ztrunc (evalRounded t lM mode_NE) <= Int32.N / 2 - 1)%Z ->
  eqExprTypePrim (evalPrim (TruncToInt t) lP) (evalRounded (TruncToInt t) lM mode_NE).
Proof. intros t lP lM [fint eqt] H.
generalize (Btrunc_correct _ _ HPrec_lt_emax (P2C (evalPrim t lP))).
unfold eqExprTypePrim. simpl. rewrite round_FIX_IZR. intros H0. apply eq_IZR in H0.
revert H. rewrite <-eqt, <-B2SF_Prim2B, SF2R_B2SF.
change prec with Rrnd.prec. change emax with Rrnd.emax.
rewrite <-H0. unfold FPtrunc. intros H.
now rewrite Sint63.of_Z_spec, Sint63.cmod_small; [| clear -H; cbn in *; lia].
Qed.

Lemma PrimInt63_opp_involutive : forall x, (- - x)%uint63 = x.
Proof. intros x. apply Uint63.to_Z_inj.
now rewrite 2Uint63.opp_spec, <-Z.sub_0_l, Zdiv.Zminus_mod_idemp_r, Z.sub_0_l,
  Z.opp_involutive, Z.mod_small; [| apply Uint63.to_Z_bounded].
Qed.

Lemma PrimInt63_opp_inj : forall x y, (- x)%uint63 = (- y)%uint63 -> x = y.
Proof. intros x y H.
rewrite <-(PrimInt63_opp_involutive x), <-(PrimInt63_opp_involutive y).
now apply f_equal.
Qed.

Lemma lesb_ltb : forall x, lesb 0 x = Uint63.ltb x min_int.
Proof. intros x.
destruct (Uint63.ltb x min_int) eqn:H; destruct (lesb 0 x) eqn:H'; [easy | | | easy].
{ destruct (lebP 0 x) as [_ | P]; [easy |]. clear H'. change (to_Z 0) with 0%Z in P.
  unfold to_Z in P. rewrite H in P. generalize (Uint63.to_Z_bounded x); lia. }
destruct (lebP 0 x) as [P | _]; [| easy]. clear H'. change (to_Z 0) with 0%Z in P.
unfold to_Z in P. rewrite H in P.
destruct (Uint63.ltbP x min_int) as [_ | P']; [easy |]. clear H.
destruct (Uint63.eqb (- x) 0) eqn:H.
{ apply eqb_correct in H. change 0%uint63 with (- 0)%uint63 in H.
  apply PrimInt63_opp_inj in H. rewrite H in P'. cbn in P'. lia. }
destruct (eqbP (- x) 0) as [_ | P'']; [easy |].
assert (H': x <> 0%uint63) by now intros ->. apply Zle_lt_or_eq in P.
destruct P as [P | P]; [generalize (Uint63.to_Z_bounded (- x)); lia |].
change 0%Z with (- 0)%Z in P. apply Z.opp_inj in P.
change 0%Z with (Uint63.to_Z 0) in P. apply Uint63.to_Z_inj in P.
now rewrite <- P in P''.
Qed.

Lemma generic_format_fexp_IZR : forall n prec emax, (0 < prec)%Z -> (3 - prec < emax)%Z ->
  (Z.abs n <= 2 ^ prec)%Z -> generic_format radix2 (fexp prec emax) (IZR n).
Proof. intros n prec emax Hprec Hemax H.
apply generic_format_abs_inv. rewrite <-abs_IZR.
apply generic_format_FLT. unfold SpecFloat.emin. apply Zle_lt_or_eq in H.
destruct H as [H | H].
- now apply (FLT_spec _ _ _ _ (Float radix2 (Z.abs n) 0));
   [unfold F2R; simpl; rewrite Rmult_1_r
   |simpl; rewrite Z.abs_involutive
   |simpl Fexp; lia].
- rewrite H. now apply (FLT_spec _ _ _ _ (Float radix2 1 prec));
   [unfold F2R; simpl; rewrite Rmult_1_l; destruct prec
   |simpl Fnum; apply Zpower_gt_1
   |simpl Fexp; lia].
Qed.

Lemma equivFloat_FloatInj {Tl} : forall (t : ArithExpr Tl Integer)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
  Rabs (IZR (evalRounded t lM md)) <= Rpow2 53 ->
  eqExprTypeFloat (evalFloat (FloatInj t) lC md) (evalRounded (FloatInj t) lM md).
Proof. intros t lC md lM [bndt eqt] H.
generalize (binary_normalize_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (evalRounded t lM md) 0%Z false).
simpl. rewrite Rlt_bool_true.
2: { unfold F2R. simpl. rewrite Rmult_1_r.
  apply (Rle_lt_trans _ (IZR (Z.pow_pos 2 53))); [| now apply IZR_lt].
  rewrite <-round_NE_abs; [| now apply fexp_correct]. unfold Rpow2 in H.
  apply round_le_generic; [now apply fexp_correct | apply valid_rnd_N | | apply H].
  now apply generic_format_fexp_IZR. }
unfold F2R, eqExprTypeFloat. simpl. rewrite Rmult_1_r. intros [H1 [H2 _]]. rewrite eqt.
split; [easy | unfold binnorm; rewrite H1].
apply round_generic; [apply valid_rnd_N |]. rewrite <-abs_IZR in H.
apply le_IZR in H. now apply generic_format_fexp_IZR.
Qed.

Lemma equivPrim_FloatInj {Tl} : forall (t : ArithExpr Tl Integer)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
  Rabs (IZR (evalRounded t lM mode_NE)) <= Rpow2 53 ->
  eqExprTypePrim (evalPrim (FloatInj t) lP) (evalRounded (FloatInj t) lM mode_NE).
Proof. intros t lP lM [bndt eqt] H.
generalize (binary_normalize_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (evalRounded t lM mode_NE) 0%Z false).
simpl. rewrite Rlt_bool_true.
2: { unfold F2R. simpl. rewrite Rmult_1_r.
  apply (Rle_lt_trans _ (IZR (Z.pow_pos 2 53))); [| now apply IZR_lt].
  rewrite <-round_NE_abs; [| now apply fexp_correct]. unfold Rpow2 in H.
  apply round_le_generic; [now apply fexp_correct | apply valid_rnd_N | | apply H].
  now apply generic_format_fexp_IZR. }
unfold F2R, eqExprTypePrim. simpl. rewrite Rmult_1_r. revert H.
rewrite <-eqt. unfold to_Z, Sint63.abs. rewrite lesb_ltb.
rewrite <-is_finite_SF_B2SF.
intros H [H1 [H2 _]]. rewrite <-B2SF_Prim2B, SF2R_B2SF.
destruct Uint63.ltb eqn:Haux'.
- apply Uint63.ltb_spec in Haux'. rewrite of_int63_equiv.
  change prec with Rrnd.prec. change emax with Rrnd.emax.
  split; [assumption |]. unfold HPrec_gt_0, HPrec_lt_emax in H1.
  rewrite H1. apply round_generic; [apply valid_rnd_N |].
  rewrite <-abs_IZR in H. apply le_IZR in H.
  now apply generic_format_fexp_IZR.
(* keyword "rew" *)
- rewrite is_finite_SF_B2SF in H2 |- *.
  rewrite opp_equiv, is_finite_Bopp, B2R_Bopp, of_int63_equiv.
  generalize (binary_normalize_correct prec emax Hprec Hmax mode_NE
   (Uint63.to_Z ((- evalPrim t lP)%sint63)%uint63) 0 false).
  unfold F2R. simpl. rewrite Rmult_1_r. rewrite Rlt_bool_true.
  2: { rewrite <-Rabs_Ropp, <-round_NE_opp, <-opp_IZR, <-round_NE_abs; [| now apply fexp_correct].
    apply (Rle_lt_trans _ (Rpow2 53)); [| now apply IZR_lt].
    apply round_le_generic; [now apply fexp_correct | apply valid_rnd_N | | assumption].
    now apply generic_format_fexp_IZR. }
  intros [H'1 [H'2 _]]. split; [easy |].
  change Rrnd.prec with prec. change Rrnd.emax with emax. (* TODO: get rid of those lines? *)
  rewrite H'1, opp_IZR. apply f_equal.
  rewrite opp_IZR, <-Rabs_Ropp, Ropp_involutive, <-abs_IZR in H.
  apply le_IZR in H. apply round_generic; [apply valid_rnd_N |].
  now apply generic_format_fexp_IZR.
Qed.

Lemma Uint63_to_Z_sqrt : forall x, Uint63.to_Z (Uint63.sqrt x) = Z.sqrt (Uint63.to_Z x).
Proof. intros x.
generalize (Uint63.sqrt_spec x). rewrite 2Z.pow_2_r. intros H.
symmetry. now apply Z.sqrt_unique.
Qed.

Lemma Uint63_sqrt_small : forall x, (Uint63.sqrt x <? min_int = true)%uint63.
Proof. intros x. apply Uint63.ltb_spec.
generalize (Uint63.sqrt_spec x), (Uint63.to_Z_bounded x).
change wB with 9223372036854775808%Z.
change (Uint63.to_Z min_int) with 4611686018427387904%Z. lia.
Qed.

Lemma in_bounds_to_Z_Uint63_sqrt : forall x,
 (Uint63.to_Z x <= 2 ^ 62 - 1)%Z ->
  Int32.in_bounds (Uint63.to_Z (Uint63.sqrt x)).
Proof. intros x H0.
generalize (Uint63.sqrt_spec x), (Uint63.to_Z_bounded x).
rewrite Uint63_to_Z_sqrt. change wB with 9223372036854775808%Z.
intros [H1 _] H2. unfold Int32.in_bounds. simpl. lia.
Qed.

Lemma equivFloat_Sqrt_Integer {Tl} : forall (t : ArithExpr Tl Integer)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
 (0 <= evalRounded t lM md)%Z ->
(* TODO: replace hypothesis above with
  - IZR (Int32.N / 2) <= IZR (evalRounded t1 lM md) <= IZR (Int32.N / 2 - 1) -> *)
  eqExprTypeFloat (evalFloat (Sqrt t) lC md) (evalRounded (Sqrt t) lM md).
Proof. intros t lC md lM [bndt eqt] nonnegt.

unfold eqExprTypeFloat. simpl. rewrite eqt in bndt. rewrite eqt. split; [| easy].
clear -bndt nonnegt. revert bndt. unfold convertibleFloat, Int32.in_bounds.
generalize (Z.sqrt_spec (evalRounded t lM md) nonnegt). simpl. lia.
Qed.

Lemma equivPrim_Sqrt_Integer {Tl} : forall (t : ArithExpr Tl Integer)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
 (0 <= evalRounded t lM mode_NE)%Z ->
(* TODO: replace hypothesis above with
  - IZR (Int32.N / 2) <= IZR (evalRounded t1 lM mode_NE) <= IZR (Int32.N / 2 - 1) -> *)
  eqExprTypePrim (evalPrim (Sqrt t) lP) (evalRounded (Sqrt t) lM mode_NE).
Proof. intros t lP lM [bndt eqt] nonnegt.

unfold eqExprTypePrim. simpl in *. rewrite eqt in bndt. rewrite <-eqt in bndt, nonnegt |- *.
change 0%Z with (to_Z 0) in nonnegt. apply Sint63.leb_spec in nonnegt.
unfold to_Z. rewrite lesb_ltb in nonnegt. rewrite nonnegt, Uint63_sqrt_small.
split; [| apply Uint63_to_Z_sqrt]. unfold to_Z in bndt. rewrite nonnegt in bndt.
unfold convertiblePrim, Int32.in_bounds in bndt. simpl in bndt.
apply in_bounds_to_Z_Uint63_sqrt. lia.
Qed.

Lemma equivFloat_Sqrt_BinFloat {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lC : evalExprTypeFloat_list Tl) md, let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
  0 <= evalRounded t lM md ->
  eqExprTypeFloat (evalFloat (Sqrt t) lC md) (evalRounded (Sqrt t) lM md).
Proof. intros t lC md lM [fint B2Rt] H. simpl.
generalize (Bsqrt_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t lC md)).
intros [H1 [H2' H3]].
assert (H2 : is_finite (@Bsqrt Rrnd.prec Rrnd.emax HPrec_gt_0 HPrec_lt_emax md (evalFloat t lC md)) = true).
{ destruct evalFloat; [easy.. | destruct s; [| easy]].
  rewrite <-B2Rt in H. simpl in H. unfold F2R in H. simpl in H.
  generalize (bpow_gt_0 radix2 e). intros H'.
  assert (H'' : 0 <= IZR (Z.neg m)) by nra. now apply le_IZR in H''. } clear H2'.
unfold eqExprTypeFloat. simpl. unfold FPsqrt. split; [assumption |]. rewrite H1.
unfold Rrnd.sqrt, Rrnd.Rnd, SpecFloat.fexp, FLT_exp, SpecFloat.emin, Rrnd.emin.
now rewrite B2Rt.
Qed.

Lemma equivPrim_Sqrt_BinFloat {Tl} : forall (t : ArithExpr Tl BinFloat)
 (lP : evalExprTypePrim_list Tl), let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
  0 <= evalRounded t lM mode_NE ->
  eqExprTypePrim (evalPrim (Sqrt t) lP) (evalRounded (Sqrt t) lM mode_NE).
Proof. intros t lP lM [fint B2Rt] H. simpl.
generalize (Bsqrt_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE (P2C (evalPrim t lP))).
rewrite <-is_finite_SF_B2SF.
intros [H1 [H2' H3]]. simpl in fint, B2Rt. unfold P2C in *.
rewrite <-B2SF_Prim2B, SF2R_B2SF in B2Rt. rewrite <-B2SF_Prim2B in fint.
assert (H2 : is_finite_SF (B2SF (@Bsqrt Rrnd.prec Rrnd.emax HPrec_gt_0 HPrec_lt_emax mode_NE (Prim2B (evalPrim t lP)))) = true).
{ destruct Prim2B; [easy.. | destruct s; [| easy]].
  rewrite <-B2Rt in H. simpl in H. unfold F2R in H. simpl in H.
  generalize (bpow_gt_0 radix2 e). intros H'.
  assert (H'' : 0 <= IZR (Z.neg m)) by nra. now apply le_IZR in H''. } clear H2'.
unfold eqExprTypePrim. simpl. unfold FPsqrt.
rewrite <-B2SF_Prim2B, SF2R_B2SF.
rewrite sqrt_equiv. split; [assumption |].
unfold FloatOps.prec, FloatOps.emax, Rrnd.prec, Rrnd.emax, Format64.prec,
  Format64.emax in *. unfold HPrec_gt_0, HPrec_lt_emax in H1.
 now rewrite H1, B2Rt.
Qed.

Lemma equivFloat_ArrayAcc {Tl} : forall (t : ArithExpr Tl Integer) a
 (lC : evalExprTypeFloat_list Tl) md,
  finite_array a = true -> let lM := C2M_list lC in
  eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md) ->
  (0 <= evalRounded t lM md < Uint63.to_Z (PArray.length a))%Z ->
  eqExprTypeFloat (evalFloat (ArrayAcc a t) lC md) (evalRounded (ArrayAcc a t) lM md).
Proof. intros t a lC md H' lM [fint B2Rt] H. simpl. unfold eqExprTypeFloat.
rewrite Prim2SF2R_Prim2B2R, B2Rt. split; [| easy]. unfold finite_array in H'.
set (P := fun n '(i, b) => (Z.of_N n <= Uint63.to_Z (PArray.length a))%Z -> b = true ->
  i = Z.of_N n /\ forall j, (0 <= j < Z.of_N n)%Z -> is_finite (Prim2B a.[of_Z j]) = true).
set (f := fun '(i, b) => (Z.succ i, b && is_finite_SF (Prim2SF a.[of_Z i]))).
generalize (N.iter_ind (Z * bool) f (0%Z, true) P). intros H''.
cut (forall n, P n (N.iter n f (0%Z, true))).
2: { apply H''; [intros _ _; split; [easy | lia] |].
  intros n [i b]. simpl. intros IHn H1 H2.
  destruct IHn as [IHn_1 IHn_2]; [lia | now apply andb_prop in H2 |].
  split; [lia |]. intros j Hj'. rewrite IHn_1 in H2.
  rewrite <-B2SF_Prim2B, is_finite_SF_B2SF in H2.
  assert (Hj : (0 <= j < Z.of_N n)%Z \/ j = Z.of_N n) by lia. clear Hj'.
  now destruct Hj as [Hj | ->]; [now apply IHn_2 | now apply andb_prop in H2]. }
intros Haux. specialize (Haux (Z.to_N φ (PArray.length a)%uint63)).
unfold P in Haux. revert H' Haux. destruct N.iter as [i b].
simpl. intros -> Hè. now apply Hè; [lia | | lia].
Qed.

Lemma equivPrim_ArrayAcc {Tl} : forall (t : ArithExpr Tl Integer) a
 (lP : evalExprTypePrim_list Tl),
  finite_array a = true -> let lM := P2M_list lP in
  eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE) ->
  (0 <= evalRounded t lM mode_NE < Uint63.to_Z (PArray.length a))%Z ->
  eqExprTypePrim (evalPrim (ArrayAcc a t) lP) (evalRounded (ArrayAcc a t) lM mode_NE).
Proof. intros t a lP H' lM [fint B2Rt] H. simpl. unfold eqExprTypeFloat.
apply (f_equal of_Z) in B2Rt. rewrite of_to_Z in B2Rt. rewrite B2Rt. split; [| easy].
unfold finite_array in H'.
set (P := fun n '(i, b) => (Z.of_N n <= Uint63.to_Z (PArray.length a))%Z -> b = true ->
  i = Z.of_N n /\ forall j, (0 <= j < Z.of_N n)%Z -> is_finite (Prim2B a.[of_Z j]) = true).
set (f := fun '(i, b) => (Z.succ i, b && is_finite_SF (Prim2SF a.[of_Z i]))).
generalize (N.iter_ind (Z * bool) f (0%Z, true) P). intros H''.
cut (forall n, P n (N.iter n f (0%Z, true))).
2: { apply H''; [intros _ _; split; [easy | lia] |].
  intros n [i b]. simpl. intros IHn H1 H2.
  destruct IHn as [IHn_1 IHn_2]; [lia | now apply andb_prop in H2 |].
  split; [lia |]. intros j Hj'. rewrite IHn_1 in H2.
  rewrite <-B2SF_Prim2B, is_finite_SF_B2SF in H2.
  assert (Hj : (0 <= j < Z.of_N n)%Z \/ j = Z.of_N n) by lia. clear Hj'.
  now destruct Hj as [Hj | ->]; [now apply IHn_2 | now apply andb_prop in H2]. }
intros Haux. specialize (Haux (Z.to_N φ (PArray.length a)%uint63)).
unfold P in Haux. revert H' Haux. destruct N.iter as [i b] eqn:Hô.
simpl. intros -> Hè. rewrite <-B2SF_Prim2B, is_finite_SF_B2SF.
now apply Hè; [lia | | lia].
Qed.

Theorem equivFloat {Tl T} :
  forall (t: ArithExpr Tl T) (lC : evalExprTypeFloat_list Tl) md,
  convertibleFloat_list lC -> let lM := C2M_list lC in
  wellBehaved t lM md -> wellFormed t = true ->
    eqExprTypeFloat (evalFloat t lC md) (evalRounded t lM md).
Proof. simpl. intros t lC md HlC. rewrite wellBehaved_decompose. intros [IWD IOE] IWF. (* TODO: get rid of wellBehaved_decompose *)
induction t as [| | | Tl T OP | Tl OP | | | | | | | | Tl T | | | |].
2: { simpl in IWF |- *; intros. rewrite <-B2SF_Prim2B in IWF |- *.
     rewrite SF2R_B2SF. split; [| easy]. simpl. now rewrite <-is_finite_SF_B2SF. }
15, 16: now apply IHt.

- apply equivFloat_Int. simpl in IWF. apply andb_prop in IWF.
  now rewrite <-Zle_is_le_bool, <-Zlt_is_lt_bool in IWF.

- revert n IWD IOE IWF.

  induction Tl as [| T Tl]; [now destruct n |].
  destruct T; (destruct n; simpl in *; [| apply IHTl]); [| easy..].
  intros _ _ _.
  split; [apply Int32.in_bounds_norm | now apply Int32.norm_in_bounds].


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].

  destruct T.
  + destruct OP; simpl in *.
    * now apply equivFloat_Op_ADD_Integer; [apply IHt1 | apply IHt2 |].
    * now apply equivFloat_Op_SUB_Integer; [apply IHt1 | apply IHt2 |].
    * now apply equivFloat_Op_MUL_Integer; [apply IHt1 | apply IHt2 |].
    * now apply equivFloat_Op_DIV_Integer; [apply IHt1 | apply IHt2 | |].
  + destruct OP; simpl in *.
    * now apply equivFloat_Op_ADD_BinFloat; [apply IHt1 | apply IHt2 |].
    * now apply equivFloat_Op_SUB_BinFloat; [apply IHt1 | apply IHt2 |].
    * now apply equivFloat_Op_MUL_BinFloat; [apply IHt1 | apply IHt2 |].
    * now apply equivFloat_Op_DIV_BinFloat; [apply IHt1 | apply IHt2 | |].


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 morphOp]].

  now apply equivFloat_OpExact; destruct OP; simpl in *; try apply IHt1; try apply IHt2.


- simpl in *. apply andb_prop in IWF.
  destruct IWF as [IWF IWFt3]. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 [IOEt3 morphOp]]].
  destruct IWD as [IWDt1 [IWDt2 IWDt3]].

  now apply equivFloat_Fma; [apply IHt1 | apply IHt2 | apply IHt3 |].


- simpl in *. apply andb_prop in IWF.
  destruct IWF as [IWF IWFt3]. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 [IOEt3 morphOp]]].
  destruct IWD as [IWDt1 [IWDt2 IWDt3]].

  now apply equivFloat_FmaExact; [apply IHt1 | apply IHt2 | apply IHt3 | |].


- now apply equivFloat_Nearbyint, IHt.


- simpl in *. now apply equivFloat_FastNearbyint; [apply IHt |].


- simpl in *. now apply equivFloat_FastNearbyintToInt; [apply IHt |].


- simpl in *. now apply equivFloat_TruncToInt; [apply IHt |].


- simpl in *. now apply equivFloat_FloatInj; [apply IHt |].

- destruct T; simpl in *.
  + apply equivFloat_Sqrt_Integer; [now apply IHt |].
    destruct IWD as [_ IWD]. apply le_IZR. lra.
  + apply equivFloat_Sqrt_BinFloat; [now apply IHt | lra].


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IWD as [IWDt1 IWDt2].
  destruct IOE as [IOEt1 IOEt2].
  destruct (IHt1 lC) as [fint1 B2Rt1]; try easy.
  destruct T1; simpl in *;
   [now rewrite B2Rt1 in fint1 |- *; try easy; apply IHt2 |].
  specialize (IHt2 (evalFloat t1 lC md, lC)).
  simpl in IHt2. rewrite B2Rt1 in IHt2.
  now apply IHt2.

- simpl in *. apply andb_prop in IWF.
  now apply equivFloat_ArrayAcc; [| apply IHt |].
Qed.

Theorem equivPrim {Tl T} :
  forall (t: ArithExpr Tl T) (lP : evalExprTypePrim_list Tl),
  convertiblePrim_list lP -> let lM := P2M_list lP in
  wellBehaved t lM mode_NE -> wellFormed t = true ->
    eqExprTypePrim (evalPrim t lP) (evalRounded t lM mode_NE).
Proof. simpl. intros t lP HlP. rewrite wellBehaved_decompose. intros [IWD IOE] IWF.
induction t as [| | | Tl T OP | Tl OP | | | | | | | | Tl T | | | |]; [| easy | ..].
15, 16: now apply IHt.

- apply equivPrim_Int. simpl in IWF. apply andb_prop in IWF.
  now rewrite <-Zle_is_le_bool, <-Zlt_is_lt_bool in IWF.

- revert n IWD IOE IWF.

  induction Tl as [| T Tl]; [now destruct n |].
  destruct T; (destruct n; simpl in *; [| apply IHTl]); [easy.. | split; [easy |] | easy].
  unfold isConversionPrim. now rewrite <-B2SF_Prim2B, SF2R_B2SF.


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].

  destruct T.
  + destruct OP; simpl in *.
    * now apply equivPrim_Op_ADD_Integer; [apply IHt1 | apply IHt2 |].
    * now apply equivPrim_Op_SUB_Integer; [apply IHt1 | apply IHt2 |].
    * now apply equivPrim_Op_MUL_Integer; [apply IHt1 | apply IHt2 |].
    * now apply equivPrim_Op_DIV_Integer; [apply IHt1 | apply IHt2 | |].
  + destruct OP; simpl in *.
    * now apply equivPrim_Op_ADD_BinFloat; [apply IHt1 | apply IHt2 |].
    * now apply equivPrim_Op_SUB_BinFloat; [apply IHt1 | apply IHt2 |].
    * now apply equivPrim_Op_MUL_BinFloat; [apply IHt1 | apply IHt2 |].
    * now apply equivPrim_Op_DIV_BinFloat; [apply IHt1 | apply IHt2 | |].


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 morphOp]].

  now apply equivPrim_OpExact; destruct OP; simpl in *; try apply IHt1; try apply IHt2.


- simpl in *. apply andb_prop in IWF.
  destruct IWF as [IWF IWFt3]. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 [IOEt3 morphOp]]].
  destruct IWD as [IWDt1 [IWDt2 IWDt3]].

  now apply equivPrim_Fma; [apply IHt1 | apply IHt2 | apply IHt3 |].


- simpl in *. apply andb_prop in IWF.
  destruct IWF as [IWF IWFt3]. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 [IOEt3 morphOp]]].
  destruct IWD as [IWDt1 [IWDt2 IWDt3]].

  now apply equivPrim_FmaExact; [apply IHt1 | apply IHt2 | apply IHt3 | |].


- now apply equivPrim_Nearbyint, IHt.


- simpl in *. now apply equivPrim_FastNearbyint; [apply IHt |].


- simpl in *. now apply equivPrim_FastNearbyintToInt; [apply IHt |].


- simpl in *. now apply equivPrim_TruncToInt; [apply IHt |].


- simpl in *. now apply equivPrim_FloatInj; [apply IHt |].


- destruct T; simpl in *.
  + apply equivPrim_Sqrt_Integer; [now apply IHt |].
    destruct IWD as [_ IWD]. apply le_IZR. lra.
  + apply equivPrim_Sqrt_BinFloat; [now apply IHt | lra].


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IWD as [IWDt1 IWDt2].
  destruct IOE as [IOEt1 IOEt2].
  destruct (IHt1 lP) as [fint1 B2Rt1]; try easy.
  destruct T1; simpl in *;
   [now rewrite <-B2Rt1 in IWDt2, IOEt2 |- *; now apply IHt2 |].
  specialize (IHt2 (evalPrim t1 lP, lP)).
  simpl in IHt2. rewrite <-B2Rt1 in IWDt2, IOEt2 |- *.
  now apply IHt2.

- simpl in *. apply andb_prop in IWF.
  now apply equivPrim_ArrayAcc; [| apply IHt |].
Qed.
