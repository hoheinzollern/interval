From Coq Require Import Reals ZArith Psatz Fourier_util.
From Flocq Require Import Raux.
From Coquelicot Require Import Coquelicot AutoDerive.
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat bigop.

Require Import Stdlib.
Require Import Coquelicot.
Require Import Xreal.
Require Import Interval.

Section powerRZMissing.

Lemma powerRZ_ind (P : Z -> (R -> R) -> Prop) :
  P 0%Z (fun x => 1) ->
  (forall n, P (Z.of_nat n) (fun x => x ^ n)) ->
  (forall n, P ((-(Z.of_nat n))%Z) (fun x => / x ^ n)) ->
  (forall f g, f =1 g -> forall n, P n f -> P n g) ->
  forall (m : Z), P m (fun x => powerRZ x m).
Proof.
move => H0 Hpos Hneg Hext m.
case: m => [|p|p].
- by rewrite /=.
- rewrite -positive_nat_Z.
  apply: Hext. move => x.
  by rewrite -pow_powerRZ.
  exact: Hpos.
- rewrite /powerRZ.
  apply: Hext. move => x.
  by [].
  rewrite -Pos2Z.opp_pos.
  rewrite -positive_nat_Z.
  exact: Hneg.
Qed.

Lemma is_derive_powerRZ (n : Z) (x : R):
  ((0 <= n)%Z \/ x <> 0) ->
  is_derive (fun x : R => powerRZ x n) x (IZR n * (powerRZ x (n - 1))).
Proof.
move => Hnx.
move: (is_derive_n_powerRZ n 1 x Hnx).
case Hn : n => [|p|p] /= .
- by rewrite !Rmult_0_l; move => _; apply: is_derive_const.
- rewrite big_ord_recl /= big_ord0 /=  subn0 Rmult_1_r.
  rewrite INR_IZR_INZ positive_nat_Z.
  rewrite pow_powerRZ.
  congr (is_derive _ _ (_ * powerRZ _ _)).
  rewrite -> Nat2Z.inj_sub by now rewrite Nat.le_succ_l; apply Pos2Nat.is_pos.
  now rewrite positive_nat_Z.
- rewrite big_ord_recl /= big_ord0 /= addn0 Rmult_1_r.
  rewrite INR_IZR_INZ positive_nat_Z.
  by rewrite Pos2Nat.inj_add.
Qed.

Lemma is_derive_powerRZS (n : Z) (x : R):
  ((1 <= n)%Z \/ x <> 0) ->
  is_derive (fun x : R => powerRZ x (n+1)) x (IZR (n+1) * (powerRZ x n)).
Proof.
move => Hnx.
move: (is_derive_powerRZ (n+1) x).
rewrite Z.add_simpl_r // ; apply.
case: Hnx => [Hn | Hx].
  left; lia.
by right.
Qed.

Lemma ex_derive_powerRZ (n : Z) (x : R):
  ((0 <= n)%Z \/ x <> 0) ->
  ex_derive (fun x : R => powerRZ x n) x.
Proof.
move => H.
apply: (ex_derive_is_derive ((fun x : R => powerRZ x (n)))).
exact: is_derive_powerRZ.
Qed.

Lemma ex_derive_powerRZS (n : Z) (x : R):
  ((1 <= n)%Z \/ x <> 0) ->
  ex_derive (fun x : R => powerRZ x (n+1)) x.
Proof.
move => H.
apply: ex_derive_powerRZ.
case: H => [Hn | Hx].
  left; lia.
by right.
Qed.

Lemma is_RInt_powerRZ (alpha : Z) (a b : R) (HneqN1 : alpha <> (-1)%Z) (H : 0 < a <= b) :
is_RInt (powerRZ^~ alpha) a b
    ((powerRZ b (alpha + 1) - powerRZ a (alpha + 1)) / IZR (alpha + 1)).
Proof.
have neq0 : IZR (alpha + 1) <> 0.
  apply: not_0_IZR.
  by rewrite Z.add_move_0_r; exact: HneqN1.
pose F := fun x => powerRZ x (alpha+1) / IZR (alpha + 1).
have -> : ((powerRZ b (alpha + 1) - powerRZ a (alpha + 1)) / IZR (alpha + 1)) = F b - F a.
rewrite /F.
field => // .
have xneq0 : forall x, Rmin a b <= x <= Rmax a b -> x <> 0.
  move => x [Hax Hxb].
  apply: Rgt_not_eq.
  apply: (Rlt_le_trans 0 (Rmin a b) x) => // .
  by case: H => [H0a Hab]; rewrite Rmin_left.
apply: is_RInt_derive => x Hx.
rewrite /F.
have -> : (powerRZ x alpha) = ((IZR (alpha+1)) * ((powerRZ x alpha)) / (IZR (alpha+1))).
  by field.
rewrite !/Rdiv.
apply: is_derive_scal_l.
apply: is_derive_powerRZS.
by right; apply xneq0.
apply: ex_derive_continuous.
apply: (ex_derive_n_powerRZ alpha 1).
by right; apply xneq0.
Qed.

Lemma int_x_alpha alpha A B (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) :
is_RInt (powerRZ^~ alpha) A B
((powerRZ B (alpha + 1) - powerRZ A (alpha + 1)) / IZR (alpha + 1)).
Proof.
apply: is_RInt_powerRZ => // .
Qed.


End powerRZMissing.

Section CoquelicotMissing.

(* this one should be in Coquelicot to relieve users *)
Lemma continuous_Rdiv_1_x x (H : x <> 0) : continuous (Rdiv 1) x.
Proof.
apply: (continuous_ext (fun (x : R) => (/ x))).
  by move => x0; rewrite /Rdiv Rmult_1_l.
exact: continuous_Rinv.
Qed.

End CoquelicotMissing.

(* Bertrand Integral:                          *)
(* RInt (fun x=> x^alpha (ln x)^beta A B for   *)
(* alpha in Z, beta in N, A, B (finite) reals  *)
Definition Bertrand alpha beta A B (I : R) :=
  is_RInt (fun x => powerRZ x alpha * (pow (ln x) beta)) A B I.

(* Function computing the Bertrand integral:   *)

Fixpoint f (alpha : Z) (beta : nat) (A B : R) {struct beta} :=
  match beta with
    | 0 => (powerRZ B (alpha+1)- powerRZ A (alpha+1)) / (IZR (alpha + 1))
    | S m =>
      (powerRZ B (alpha+1) * (pow (ln B) (beta)) -
       powerRZ A (alpha+1) * (pow (ln A) beta)) / (IZR (alpha + 1)) -
      (INR beta) / (IZR (alpha+1)) * f alpha m A B end.

(* limit of the Bertrand integral              *)
Definition Bertrand_lim alpha beta (A : R) (I : R) :=
  is_RInt_gen (fun x => powerRZ x alpha * (pow (ln x) beta)) (at_point A) (Rbar_locally p_infty) I.

(* Function computing the limit of the Bertrand integral *)
Fixpoint f_lim (alpha : Z) (beta : nat) (A : R) {struct beta} :=
  match beta with
    | 0 => (- powerRZ A (alpha+1)) / (IZR (alpha + 1))
    | S m =>
       - ( powerRZ A (alpha+1) * (pow (ln A) beta)) / (IZR (alpha + 1)) -
      (INR beta) / (IZR (alpha+1)) * f_lim alpha m A end.

(* Variables (A B : R). *)

(* Eval cbn in f 1 3 A B. *)

Lemma one_step_by_parts alpha beta (A : R) (B : R) (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) :
  forall I, Bertrand alpha beta A B I ->
  Bertrand alpha (S beta) A B
     ((powerRZ B (alpha+1) * (pow (ln B) (S beta)) -
       powerRZ A (alpha+1) * (pow (ln A) (S beta))) / (IZR (alpha + 1)) -
      (INR (S beta)) / (IZR (alpha+1)) * I).
Proof.
have Salpha_neq_0 :   IZR (alpha + 1) <> 0.
  by apply: not_0_IZR; lia.
move => I HABI.
rewrite/Bertrand.
pose f := (fun x => Rdiv (powerRZ x (alpha+1)) (IZR(alpha+1))).
pose f' := (fun x => powerRZ x alpha).
pose g := (fun x => pow (ln x) (beta.+1)).
pose g' := (fun x => (1 / x) * (INR (beta.+1) * pow (ln x) beta)).
set f'g := (fun x : R => scal (f' x) (g x)).
pose fg' := (fun t => scal (f t) (g' t)).
pose f'gplusfg' := (fun t : R => plus (f'g t) (fg' t)).
apply (is_RInt_ext (fun x => minus (f'gplusfg' x) (fg' x))) => [x HX|].
rewrite /f'gplusfg' /fg' /f /g /f'g.
by rewrite /minus -plus_assoc plus_opp_r plus_zero_r /scal.
apply: is_RInt_minus.
- apply: (is_RInt_ext (fun t : R => plus (scal (f' t) (g t)) (scal (f t) (g' t)))) =>[x Hx|].
    by [].
  have -> : ((powerRZ B (alpha + 1) * ln B ^ beta.+1 -
      powerRZ A (alpha + 1) * ln A ^ beta.+1) / IZR (alpha + 1)) = (minus (scal (f B) (g B)) (scal (f A) (g A))).
    rewrite /f /g /minus /opp /plus /scal /mult  /= /mult /= .
    by field.
  apply: (is_RInt_scal_derive f g f' g' A B) => x Hx.
  have xgt0 : x > 0 by case: Hx; rewrite Rmin_left; lra.
  + rewrite /f /f'.
    apply: (is_derive_ext (fun x0 => scal (powerRZ x0 (alpha + 1)) (1 / IZR (alpha + 1)))) => [t|].
      by rewrite /scal /= /mult /=;field.
    have -> : powerRZ x alpha = scal (IZR (alpha+1) * (powerRZ x alpha)) (1 / IZR (alpha + 1)).
      by rewrite /scal /mult /= /mult /=; field.
    apply: is_derive_scal_l.
    apply: (is_derive_powerRZS alpha x).
    by lra.
  + rewrite /g /g'.
    have -> : (1 / x * (INR beta.+1 * ln x ^ beta)) = (INR beta.+1 * ( / x) * ln x ^ beta.+1.-1).
      rewrite -pred_Sn; field.
      by case: Hx; rewrite Rmin_left; lra.
    apply: (is_derive_pow).
    apply: is_derive_ln.
    by case: Hx; rewrite Rmin_left; lra.
  + have Hxneq0 : x <> 0 by rewrite Rmin_left in Hx; lra.
    apply: ex_derive_continuous.
    apply: ex_derive_powerRZ; right => // .
  + have Hxgt0 : x > 0 by rewrite Rmin_left in Hx; lra.
    have Hxneq0 : x <> 0 by lra.
    apply: continuous_mult.
    apply: continuous_Rdiv_1_x => // .
    apply: continuous_mult; first exact: continuous_const.
    (* intermediary lemmas needed here *)
    apply: ex_derive_continuous.
    apply: ex_derive_is_derive.
    apply: is_derive_pow.
    by apply: is_derive_ln.
    move: HABI; rewrite /Bertrand.
    suff Hx : forall x, Rmin A B < x < Rmax A B -> (fun x => scal (INR beta.+1 / IZR (alpha + 1)) (powerRZ x alpha * ln x ^ beta)) x = fg' x => [HABI|t HAtB].
      apply: is_RInt_ext.
      exact: Hx.
      apply: is_RInt_scal => // .
    have Hxgt0 : t > 0 by rewrite Rmin_left in HAtB; lra.
    have Hxneq0 : t <> 0 by lra.
    rewrite /fg' /f /g'.
    rewrite powerRZ_add // .
    rewrite /scal /= /mult /=.
    field; lra.
Qed.

Lemma f_correct alpha beta A B (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) :
 Bertrand alpha beta A B (f alpha beta A B).
Proof.
elim: beta => [|m HIm] // .
  rewrite /f /Bertrand.
  apply: (is_RInt_ext (fun x => powerRZ x alpha)).
  + by move => x Hx; rewrite pow_O Rmult_1_r.
  exact: int_x_alpha.
by move: (one_step_by_parts alpha m A B H Halpha _ HIm).
Qed.

Lemma f_correct_RInt alpha beta A B (H : 0 < A <= B) (Halpha:  alpha <> (-1)%Z) : f alpha beta A B = RInt (fun x => powerRZ x alpha * (pow (ln x) beta)) A B.
Proof.
  symmetry.
  apply: is_RInt_unique.
  exact: f_correct.
Qed.

Lemma is_lim_RInv_p_infty:
  is_lim Rinv p_infty 0.
Proof.
suff -> : 0 = real (Rbar_inv p_infty) => //.
exact: (is_lim_inv (fun x => x) p_infty p_infty).
Qed.

Lemma is_lim_RInv_m_infty:
  is_lim Rinv m_infty 0.
Proof.
suff -> : 0 = real (Rbar_inv m_infty) => //.
exact: (is_lim_inv (fun x => x) m_infty m_infty).
Qed.


Lemma is_lim_powerRZ_0 :
  forall alpha, (alpha < 0)%Z ->
  is_lim (fun x => powerRZ x alpha) p_infty 0.
Proof.
intros alpha Halpha.
apply: (powerRZ_ind (fun n f => (n < 0)%Z -> is_lim f p_infty (0%R))) => // [n Hn|n Hn|].
- move: Hn. have -> : 0%Z = (Z.of_nat 0%N)%Z by [].
  rewrite -Nat2Z.inj_lt; lia.
- elim: n Hn => [|m Hm Hn] // .
  rewrite /= .
  apply: (is_lim_ext_loc (fun x => / x * / x^m)).
    exists 0 => x Hx.
    field.
    split.
      by apply: pow_nonzero; lra.
      by lra.
  case: m Hm Hn => [|m Hm] Hn.
  + move => _ /=.
    have -> : 0 = real (Rbar_mult (Finite 0) (Finite 1)) by apply eq_sym, Rmult_0_l.
    apply: (is_lim_mult (fun x => / x) (fun x => / 1) p_infty 0 1) => // .
    exact: is_lim_RInv_p_infty.
    by rewrite Rinv_1; exact: is_lim_const.

  have -> : 0 = real (Rbar_mult (Finite 0) (Finite 0)) by apply eq_sym, Rmult_0_l.
  apply: (is_lim_mult (fun x => / x) (fun x => / x^m.+1) p_infty 0 0) => // .
  exact: is_lim_RInv_p_infty.
  apply: Hm.
  lia.
move => f g Hfg n H1 H2.
apply: (is_lim_ext f g _ _ Hfg).
by apply: H1.
Qed.

Lemma is_lim_pow_infty n : is_lim (fun x => x^n.+1) p_infty p_infty.
Proof.
elim: n => [|n Hn].
- apply: (is_lim_ext id) => // .
  by move => y; rewrite pow_1.
- apply: (is_lim_ext (fun x => x * x^n.+1)).
    by move => y.
  have {2}-> : p_infty = Rbar_mult p_infty p_infty => // .
  apply: is_lim_mult => // .
Qed.

Lemma is_lim_pow_0 (f : R -> R) n :
  is_lim f p_infty 0 ->
  is_lim (fun x => (f x)^n.+1) p_infty 0.
Proof.
elim: n => [|n Hn].
- apply: (is_lim_ext f) => // .
  by move => y; rewrite pow_1.
- move =>  Hf0.
apply: (is_lim_ext (fun x => (f x) * (f x)^n.+1)).
  by move => y.
have {1}-> : 0 = real (Rbar_mult 0 0) by apply eq_sym, Rmult_0_l.
apply: (is_lim_mult f (fun x => (f x)^n.+1) p_infty 0 0) => //.
exact: Hn.
Qed.


Lemma Rbar_mult_p_l y (Hy : 0 < y) :
  Rbar_mult y p_infty = p_infty.
Proof.
rewrite /Rbar_mult /Rbar_mult'.
case: (Rle_dec 0 y) => Hy1; last by lra.
by case: (Rle_lt_or_eq_dec 0 y Hy1) => // ; lra.
Qed.

Lemma Rbar_mult_p_r y (Hy : 0 < y) :
  Rbar_mult p_infty y = p_infty.
Proof.
by rewrite Rbar_mult_comm; exact: Rbar_mult_p_l.
Qed.

Lemma Rbar_mult_m_l y (Hy : 0 < y) :
  Rbar_mult y m_infty = m_infty.
Proof.
rewrite /Rbar_mult /Rbar_mult'.
case: (Rle_dec 0 y) => Hy1; last by lra.
by case: (Rle_lt_or_eq_dec 0 y Hy1) => // ; lra.
Qed.

Lemma Rbar_mult_m_r y (Hy : 0 < y) :
  Rbar_mult m_infty y = m_infty.
Proof.
by rewrite Rbar_mult_comm; exact: Rbar_mult_m_l.
Qed.

(* TODO: variant with a composition *)
Lemma is_lim_Rpower y (Hy : 0 < y) :
  is_lim (fun x => Rpower x y) p_infty p_infty.
Proof.
rewrite /Rpower.
apply: is_lim_comp => // .
exact: is_lim_exp_p.
apply: (is_lim_ext (fun x => scal y (ln x))).
  by move => x0.
have {2}-> :  p_infty = Rbar_mult y p_infty.
  by rewrite Rbar_mult_p_l.
apply (is_lim_scal_l ln y p_infty p_infty).
exact: is_lim_ln_p.
exists 0 => x0 Hx0 //.
Qed.

Lemma x_alpha_0 alpha (Halpha : (alpha < -1)%Z) :
  is_lim (powerRZ^~ (alpha + 1)%Z) p_infty (0%R).
Proof.
apply: is_lim_powerRZ_0.
by lia.
Qed.

Lemma Rpower_pos {x y} (Hx : 0 < x) (Hy : 0 <= y) : Rpower x y > 0.
Proof.
rewrite /Rpower.
by apply: exp_pos.
Qed.

Lemma is_derive_Rpower {x y} (Hx : 0 < x) (Hy : 0 <= y) :
  is_derive (fun t => Rpower t y) x (y * Rpower x (y - 1)).
Proof.
move: (is_derive_n_Rpower 1 y x Hx) => /=.
by rewrite big_ord_recl big_ord0 /= Rminus_0_r Rmult_1_r.
Qed.

Lemma ln_Rpower x y (Hx : 0 < x) (Hy : 0 <= y) : ln (Rpower x y) = y * ln x.
Proof.
rewrite /Rpower // .
by rewrite ln_exp.
Qed.

Lemma x_alpha_beta alpha beta (Halpha : (alpha < -1)%Z) :
  is_lim (fun x => powerRZ x (alpha + 1)%Z * (pow (ln x) beta.+1)) p_infty (0%R).
Proof.
have Halpah1 : IZR (alpha + 1) < 0.
  by apply: (IZR_lt _ 0); lia.
have Hbeta1 : INR beta.+1 > 0.
  apply: lt_0_INR.
  exact: Nat.lt_0_succ.
have foo :  0 < IZR (- (alpha + 1)) / INR beta.+1.
  rewrite opp_IZR.
  by apply: RIneq.Rdiv_lt_0_compat => // ; lra.
set X := fun x => Rpower x ((IZR (Z.opp (alpha + 1))) / INR beta.+1).
(* First we rewrite our function *)
have Htransform:
  forall x,
    x > 0 ->
    powerRZ x (alpha + 1) * ln x ^ beta.+1 =
    pow (-((INR beta.+1) / IZR (alpha + 1)) * (ln (X x) * / (X x))) beta.+1.
  move => x Hx.
  have HXgt0 : X x > 0.
    by apply: Rpower_pos => // ; lra.
  have -> : -((INR beta.+1) / IZR (alpha + 1)) * (ln (X x) / (X x)) =
          (-((INR beta.+1) / IZR (alpha + 1)) * ln (X x)) / (X x).
    field.
    by split; lra.
  rewrite -ln_Rpower ?Rpow_mult_distr => // .
  + have -> : Rpower (X x) (-(INR beta.+1 / IZR (alpha + 1))) =
          x.
      rewrite Rpower_mult.
      rewrite opp_IZR.
      have -> : (- IZR ((alpha + 1)) / INR beta.+1 * -(INR beta.+1 / IZR (alpha + 1))) = 1 by field; lra.
      exact: Rpower_1.
  + rewrite Rmult_comm.
    congr (_ * _).
    have Hpow_pos :  Rpower x (IZR (- (alpha + 1)) / INR beta.+1) > 0.
      by apply: Rpower_pos => // ; lra.
    rewrite -Rinv_pow /X; try lra.
    rewrite -Rpower_pow ?Rpower_mult -?Rpower_Ropp // .
    have -> : (- (IZR (- (alpha + 1)) / INR beta.+1 * INR beta.+1)) = IZR (alpha + 1)%Z.
      by rewrite opp_IZR; field; lra.
    by rewrite powerRZ_Rpower.
  apply: Ropp_0_ge_le_contravar.
  apply: Rle_ge.
  rewrite /Rdiv.
  apply: Rmult_le_pos_neg => // ; try lra.
  by apply: Rlt_le; apply: Rinv_lt_0_compat.
(* now we can show its limit *)
apply: (is_lim_ext_loc (fun x => (- (INR beta.+1 / IZR (alpha + 1)) * (ln (X x) * / X x))
               ^ beta.+1) ).
  by exists 0; move => x Hx ; rewrite Htransform // .
apply: is_lim_pow_0.
have -> : 0 = real (Rbar_mult (- (INR beta.+1 / IZR (alpha + 1))) 0) by apply eq_sym, Rmult_0_r.
apply (is_lim_scal_l (fun (x : R) => (ln (X x) * / X x)) (- (INR beta.+1 / IZR (alpha + 1))) p_infty 0).
apply: (is_lim_comp (fun x => ln x / x) X p_infty 0 p_infty).
  + exact: is_lim_div_ln_p.
  + apply: is_lim_Rpower => // .
  + exists 0 => x Hx // .
Qed.

Lemma f_lim_is_lim alpha beta A (H : 0 < A) (Halpha : (alpha < -1)%Z):
   filterlim (f alpha beta A) (Rbar_locally p_infty)
   (locally (f_lim alpha beta A)).
elim: beta => [ | beta Hbeta].
- rewrite /f /f_lim /Rdiv /Rminus.
  rewrite -[locally _]/(Rbar_locally (Rbar_mult (Finite _) (Finite _))).
  rewrite -[filterlim _ _ _]/(is_lim _ p_infty _).
  apply: is_lim_mult => // .
  + apply: is_lim_plus.
    * exact: x_alpha_0.
    * exact: is_lim_const.
    * rewrite /is_Rbar_plus /= .
      by apply f_equal, f_equal, Rplus_0_l.
  + apply is_lim_const.
- rewrite /f /f_lim -/f -/f_lim /Rdiv /Rminus.
  rewrite -[locally _]/(Rbar_locally (Finite _)).
  rewrite -[filterlim _ _ _]/(is_lim _ p_infty _).
  apply: is_lim_plus.
  + apply: is_lim_mult.
    * apply: is_lim_plus.
        - exact: x_alpha_beta.
        - exact: is_lim_const.
        - done.
    * exact: is_lim_const.
    * done.
  + apply: is_lim_opp.
    apply: is_lim_mult.
    * exact: is_lim_const.
    * rewrite -[locally _]/(Rbar_locally (Finite _)) in Hbeta.
      exact Hbeta.
    * done.
  + by rewrite Rplus_0_l.
Qed.

Lemma f_lim_correct alpha beta A (H : 0 < A) (Halpha : (alpha < -1)%Z) :
 Bertrand_lim alpha beta A (f_lim alpha beta A).
Proof.
rewrite /Bertrand_lim.
apply prodi_to_single_l.
apply: (filterlimi_lim_ext_loc (f alpha beta A)).
  exists A => x Hx.
  apply f_correct.
  apply (conj H).
  exact: Rlt_le.
  exact: Zlt_not_eq.
exact: f_lim_is_lim.
Qed.

Section BertrandLogNeg.

(* in this section we focus on integrals of the shape *)
(* int(1 / (x * ln^beta), x=a..infinity), a>1, beta>1   *)

Definition f_neg (a : R) (beta : nat) :=
  - / ((INR beta) * (ln a)^beta).

Lemma continuous_f_neg x beta (H0x : 0 < x) (Hx1 : x <> 1):
  continuous (fun x0 : R => / (x0 * ln x0 ^ beta)) x.
Proof.
have Hlnn0 x1 beta1 :  0 < x1 -> 1 <> x1 -> ln x1 ^ beta1 <> 0.
  by move => H0x1 Hx10; apply: pow_nonzero; case: (Rlt_dec 1 x1) => H; move: (ln_increasing 1 x1); move: (ln_increasing x1 1); rewrite ln_1; lra.
apply: continuous_comp.
  apply: continuous_mult; first exact: continuous_id.
  apply: (continuous_comp ln (fun x => pow x beta)).
    by apply: continuous_ln; lra.
  by apply: ex_derive_continuous; apply: ex_derive_pow; exact: ex_derive_id.
apply: continuous_Rinv.
apply: Rmult_integral_contrapositive; split; try lra.
apply: Hlnn0; lra.
Qed.

Lemma is_derive_f_neg :
  forall beta x,
  beta <> 0%N ->
  0 < x -> x <> 1 ->
  is_derive (fun x : R => f_neg x beta) x (/ (x * (ln x)^beta.+1)).
Proof.
intros beta x Hbeta Hx1 Hx2.
rewrite /f_neg -[/(_ * _)]Ropp_involutive.
apply: is_derive_opp.
assert (H: (ln x <> 0)%R).
  rewrite <- ln_1.
  contradict Hx2.
  exact (ln_inv x 1 Hx1 Rlt_0_1 Hx2).
auto_derive.
- refine (conj Hx1 (conj _ I)).
  apply Rmult_integral_contrapositive.
  split.
    now apply not_0_INR.
  now apply pow_nonzero.
- destruct beta as [|beta].
    easy.
  simpl Nat.pred.
  simpl pow.
  field.
  repeat split.
  now apply pow_nonzero.
  exact H.
  now apply Rgt_not_eq.
  now apply not_0_INR.
Qed.

Lemma f_neg_correct_RInt_0_1 a b beta (Hab1 : 0 < a <= b) (Hb1 : b < 1) (Hbeta : beta <> 0%N) : is_RInt (fun x => / (x * (ln x)^beta.+1)) a b (f_neg b beta - f_neg a beta).
Proof.
have Hbetn0 : INR beta <> 0 by apply: not_0_INR; case: beta Hbeta.
have Hlnn0 x beta1 : 0 < x < 1 -> ln x ^ beta1 <> 0.
  by move => Hx0; apply: pow_nonzero; move: (ln_increasing x 1); rewrite ln_1;lra.
have Hder : forall x, 0 < x < 1 -> is_derive (fun x => f_neg x beta) x (/ (x * (ln x)^beta.+1)).
  move => x Hax.
  apply is_derive_f_neg.
  now destruct beta.
  apply Hax.
  now apply Rlt_not_eq.
apply: (is_RInt_derive (fun x => f_neg x beta) _).
  by move => x Hx; apply: Hder; rewrite Rmin_left ?Rmax_right in Hx; try lra.
move => x. (rewrite Rmin_left ?Rmax_right; try (by lra)).
move => Hx.
apply: continuous_comp.
  apply: continuous_mult; first exact: continuous_id.
  apply: (continuous_comp ln (fun x => pow x beta.+1)).
    by apply: continuous_ln; lra.
  by apply: ex_derive_continuous; apply: ex_derive_pow; exact: ex_derive_id.
apply: continuous_Rinv.
apply: Rmult_integral_contrapositive; split; try lra.
by apply: Hlnn0; lra.
Qed.

Lemma f_neg_correct_RInt_a_infty a b beta (Ha : 1 < a <= b) (Hbeta : beta <> 0%N) : is_RInt (fun x => / (x * (ln x)^beta.+1)) a b (f_neg b beta - f_neg a beta).
Proof.
have Hbetn0 : INR beta <> 0 by apply: not_0_INR; case: beta Hbeta.
have Hlnn0 x beta1 : a <= x -> ln x ^ beta1 <> 0.
    by move => Hx0; apply: pow_nonzero; move: (ln_increasing 1 x); rewrite ln_1; lra.
have Hder : forall x, a <= x -> is_derive (fun x => f_neg x beta) x (/ (x * (ln x)^beta.+1)).
  move => x Hax.
  apply is_derive_f_neg.
  now destruct beta.
  apply Rlt_trans with (1 := Rlt_0_1).
  now apply Rlt_le_trans with a.
  apply Rgt_not_eq.
  now apply Rlt_le_trans with a.
apply: (is_RInt_derive (fun x => f_neg x beta) _).
  by move => x Hx; apply: Hder; rewrite Rmin_left in Hx; try lra.
move => x. (rewrite Rmin_left; last by lra); move => Hx.
apply: continuous_comp.
  apply: continuous_mult; first exact: continuous_id.
  apply: (continuous_comp ln (fun x => pow x beta.+1)).
    by apply: continuous_ln; lra.
  by apply: ex_derive_continuous; apply: ex_derive_pow; exact: ex_derive_id.
apply: continuous_Rinv.
apply: Rmult_integral_contrapositive; split; try lra.
by apply: Hlnn0; lra.
Qed.

Lemma filterlim_sqr_m_infty:
  filterlim (pow^~ 2%N) (Rbar_locally m_infty) (Rbar_locally p_infty).
Proof.
apply: (filterlim_ext (fun x => x * x)); first by move => y; rewrite /= ?Rmult_1_r.
suff -> : p_infty = Rbar_mult m_infty m_infty => // .
  apply: filterlim_comp_2; try exact: filterlim_id.
  exact: filterlim_Rbar_mult.
Qed.

Lemma is_lim_sqr_infty:
  is_lim (pow^~ 2%N) m_infty p_infty.
Proof.
apply: (is_lim_ext (fun x => x * x)); first by move => y; rewrite /= ?Rmult_1_r.
suff -> : p_infty = Rbar_mult m_infty m_infty => // .
  by apply: is_lim_mult => // .
Qed.

Lemma filterlim_pow_infty n : filterlim (pow^~ n.+1) (Rbar_locally p_infty) (Rbar_locally p_infty).
Proof.
elim: n => [|n Hn].
  apply: (filterlim_ext (fun x => x)).
    by move => x; rewrite pow_1.
  exact: filterlim_id.
apply: (filterlim_ext (fun x => x * (pow x n.+1))).
  by move => x.
apply: filterlim_comp_2; first exact: filterlim_id.
  exact: Hn.
exact: filterlim_Rbar_mult.
Qed.

Lemma filterlim_pow_m_even n : ~~ odd n.+1 -> filterlim (fun x => pow x n.+1) (Rbar_locally m_infty) (Rbar_locally p_infty).
Proof.
move => Hodd.
rewrite -(odd_double_half n.+1).
rewrite -[odd n.+1]Bool.negb_involutive Hodd /= add0n. (*ugly *)
rewrite -mul2n.
apply: filterlim_ext.
move => y; by rewrite pow_mult.
apply: (filterlim_comp _ _ _ (fun x => x ^ 2) (fun x => x ^ (uphalf n))).
apply: filterlim_sqr_m_infty.
case: n Hodd => [|n] // Hodd.
exact: filterlim_pow_infty.
Qed.


Lemma filterlim_pow_m_odd n : odd n.+1 -> filterlim (fun x => pow x n.+1) (Rbar_locally m_infty) (Rbar_locally m_infty).
Proof.
move => Hodd.
case: n Hodd => [|n] Hodd.
- apply: (filterlim_ext id).
    by move => x /=; rewrite Rmult_1_r.
  exact: filterlim_id.
apply: (filterlim_ext (fun x => x * pow x n.+1)).
  by move => x.
apply: filterlim_comp_2.
  exact: filterlim_id.
by apply: filterlim_pow_m_even.
by apply: filterlim_Rbar_mult.
Qed.

(*
Lemma is_lim_pow_m_infty n : is_lim (fun x => pow x n.+1) m_infty (if odd n.+1 then m_infty else p_infty).
Proof.
rewrite -{1}(odd_double_half n.+1).
case : ifP => Hodd.
suff {2}-> : m_infty = Rbar_mult m_infty (if (uphalf n) is m.+1 then p_infty else 1).
  apply: is_lim_mult => // .
  rewrite -mul2n.
  apply: is_lim_ext. move => y. by rewrite pow_mult.
  apply: (is_lim_comp (fun x => x ^(uphalf n)) (fun x => x ^ 2)).
  case Hhalf: (uphalf n) => [|m].
    apply: (is_lim_ext (fun x => 1)). by move => y; rewrite pow_O.
    exact: is_lim_const.
  exact: is_lim_pow_infty.
  exact: is_lim_sqr_infty.
  by exists 0 .
  case: (uphalf n) => // ; rewrite /ex_Rbar_mult; lra.
  case: (uphalf n) => // ; rewrite Rbar_mult_m_r // ; lra.

rewrite add0n -mul2n.
apply: is_lim_ext.
move => y; by rewrite pow_mult.
case: n Hodd => // n Hodd.
apply: (is_lim_comp (fun x => x ^ (n.+2)./2) (fun x => x ^2) _ _ p_infty).
apply: is_lim_pow_infty.
exact: is_lim_sqr_infty.
by exists 1.
Qed.

Lemma is_lim_pow_m_odd n : odd n.+1 -> is_lim (fun x => pow x n.+1) m_infty m_infty.
Proof.
move => Hodd.
by move: (is_lim_pow_m_infty n); rewrite Hodd.
Qed.

Lemma is_lim_pow_m_even n : ~~ odd n.+1 -> is_lim (fun x => pow x n.+1) m_infty p_infty.
Proof.
move => Hodd.
move: (is_lim_pow_m_infty n); case: ifPn => // Heven.
by rewrite Heven in Hodd.
Qed.
*)

Lemma f_neg_correct_RInt_gen_0_a a beta (Ha : 0 < a < 1) (Hbeta : beta <> 0%N) : is_RInt_gen (fun x => / (x * (ln x)^beta.+1)) (at_right 0) (at_point a) (f_neg a beta).
Proof.
apply prodi_to_single_r.
have apos : 0 < a by lra.
set ap := mkposreal a apos.
apply: (filterlimi_lim_ext_loc).
  exists ap => x Hx1 Hx2.
  apply f_neg_correct_RInt_0_1 => // ;move/ball_to_lra: Hx1 => /=; lra.
  rewrite -{2}[f_neg _ _ ]Rminus_0_r.
apply: (filterlim_comp _ _ _  (fun x => f_neg x beta) (fun x => f_neg a beta - x) (at_right 0) _ (* (Rbar_locally 0) *) _) ;last first.
rewrite /Rminus. apply: continuous_plus.
    exact: filterlim_const.
  exact: filterlim_opp.
rewrite /f_neg.
apply: filterlim_comp; last first.
  rewrite -[0]Ropp_0.
  exact: (filterlim_opp 0).
case HEvenOdd: (odd beta); last first.
- rewrite -[locally 0]/(Rbar_locally (Rbar_inv p_infty)).
  apply (filterlim_comp _ _ _ (fun x => INR beta*ln x ^ beta) Rinv _ (Rbar_locally p_infty)).
    have -> : p_infty = Rbar_mult (INR beta) p_infty.
      by rewrite Rbar_mult_p_l // ; apply: lt_0_INR; apply/ltP; case: beta Hbeta HEvenOdd.
    suff: filterlim (fun x => (ln x)^beta) (at_right 0) (Rbar_locally p_infty).
      move => Hln.
      apply: filterlim_comp; last first.
        exact: filterlim_Rbar_mult_l.
      exact: Hln.
    apply: (filterlim_comp _ _ _ _ (fun x => x ^beta)) => //; try apply: is_lim_ln_0.
    case: beta Hbeta HEvenOdd => [|beta] Hbeta HevenOdd // .
    by apply: filterlim_pow_m_even; by rewrite HevenOdd.
  exact: is_lim_RInv_p_infty.
- rewrite -[locally 0]/(Rbar_locally (Rbar_inv m_infty)).
  apply (filterlim_comp _ _ _ (fun x => INR beta*ln x ^ beta) Rinv _ (Rbar_locally m_infty)).
    have -> : m_infty = Rbar_mult (INR beta) m_infty.
      by rewrite Rbar_mult_m_l // ; apply: lt_0_INR; apply/ltP; case: beta Hbeta HEvenOdd.
    suff: filterlim (fun x => (ln x)^beta) (at_right 0) (Rbar_locally m_infty).
      move => Hln.
      apply: filterlim_comp; first exact: Hln.
        exact: filterlim_Rbar_mult_l.
    apply: (filterlim_comp _ _ _ _ (fun x => x ^ beta)); try apply: is_lim_ln_0.
    case: beta Hbeta HEvenOdd => [|beta] Hbeta HevenOdd // .
    by apply: filterlim_pow_m_odd; by rewrite HevenOdd.
  by apply: is_lim_RInv_m_infty.
Qed.

Lemma f_neg_correct_RInt_gen_a_infty a beta (Ha : 1 < a) (Hbeta : beta <> 0%N) : is_RInt_gen (fun x => / (x * (ln x)^beta.+1)) (at_point a) (Rbar_locally p_infty) (- f_neg a beta).
Proof.
apply prodi_to_single_l.
apply: (filterlimi_lim_ext_loc).
  exists a => x Hx.
  by apply f_neg_correct_RInt_a_infty => // ; lra.
  rewrite -Rminus_0_l.
apply: (filterlim_comp _ _ _  (fun x => f_neg x beta) (fun x => x - f_neg a beta) (* (Rbar_locally' p_infty) *) _ (* (Rbar_locally 0) *) _);last first.
rewrite /Rminus. apply: continuous_plus 0%R _ _.
    exact: filterlim_id.
  exact: filterlim_const.
rewrite /f_neg.
apply: filterlim_comp.
  apply: (is_lim_inv (fun x => INR beta*ln x ^ beta) (p_infty) (p_infty)) => // .

  have {2} -> : p_infty = Rbar_mult (INR beta) p_infty.
    by rewrite Rbar_mult_p_l // ; apply: lt_0_INR; apply/ltP; case: beta Hbeta.
  apply: is_lim_mult; first exact: is_lim_const.
    apply: (filterlim_comp _ _ _ _ (fun x => x ^beta)) => // ; try apply: is_lim_ln_p.
      by case :beta Hbeta => [| beta] // Hbeta; apply: is_lim_pow_infty.
  by apply: not_0_INR; case: beta Hbeta.
rewrite -[0]Ropp_0.
exact: (filterlim_opp 0).
Qed.

End BertrandLogNeg.

Section ExponentInQ.

End ExponentInQ.

Section ZeroToEpsilon.

(*
The following definition stems from the fact that
'RInt (x^alpha * (ln x)^beta) 0 eps' =
RInt_gen (u^(2 - alpha) * (ln u) ^ beta) (1/eps) p_infty
*)

Definition f0eps (alpha : Z) (beta : nat) (epsilon : R) (B : R) :=
  (-1) ^ beta * f (- 2 - alpha) beta (/ epsilon) B.

Definition f0eps_lim (alpha : Z) (beta : nat) (epsilon : R) :=
  (-1) ^ beta * f_lim (- 2 - alpha) beta (/ epsilon).


Lemma pow_negx x n : pow (- x) n = (pow (-1) n) * pow x n.
  have -> : - x = -1 * x by ring.
  by rewrite Rpow_mult_distr.
Qed.

Lemma subst_lemma alpha beta epsilon (eta : R) (Heps : 0 < epsilon) (Heta : 0 < eta <= epsilon) (Halpha : -1 < IZR alpha) :
  RInt_gen
    (fun x => powerRZ x alpha * pow (ln x) beta)
    (at_point eta)
    (at_point epsilon) =
  - RInt
      (fun x => - (pow (-1) beta) * powerRZ x (- 2 - alpha) * (pow (ln x) beta))
      (1 / epsilon)
      (1 / eta).
Proof.
  have Hint : ex_RInt (fun x : R => powerRZ x alpha * ln x ^ beta) eta epsilon.
  eexists.
  apply: f_correct => // .
  suff: (-1 < alpha)%Z by lia.
  apply: lt_IZR => // .
  (* should be a lemma *)
  have -> : RInt_gen (fun x : R => powerRZ x alpha * ln x ^ beta) (at_point eta) (at_point epsilon) = RInt (fun x : R => powerRZ x alpha * ln x ^ beta) eta epsilon.
    apply is_RInt_gen_unique; rewrite is_RInt_gen_at_point.
    exact: RInt_correct => // .
  pose g := fun x => Rinv x.
  pose dg := fun x => - 1 / x^2.
  have {1}-> : 1 / eta = (g eta).
    by rewrite /g; field; lra.
  have {1}-> : 1 / epsilon = (g epsilon).
    by rewrite /g; field; lra.
  rewrite -(RInt_comp _ _ dg).
  rewrite -opp_RInt_swap ; first congr (opp _) ; last by apply: ex_RInt_swap.
  symmetry; apply: RInt_ext.
  move => x Hx.
  rewrite Rmin_right in Hx; try lra.
  rewrite Rmax_left in Hx; try lra.
  have Hxneg0 : x <> 0 by lra.
  have Hinv : / x <> 0.
    by apply: Rinv_neq_0_compat.
  have -> : scal (dg x)(- (-1) ^ beta * powerRZ (g x) (-2 - alpha) * ln (g x) ^ beta) =
            (dg x) * (- (-1) ^ beta * powerRZ (g x) (-2 - alpha) * ln (g x) ^ beta) by [].
  rewrite /dg /g.
  rewrite powerRZ_add ?ln_Rinv; try lra.
  rewrite -> (powerRZ_neg _ 2), powerRZ_neg, Rinv_involutive by easy.
  rewrite [(- ln x) ^beta] pow_negx.
  replace (powerRZ x alpha * ln x ^ beta) with ((-1)^beta * (-1)^beta * (powerRZ x alpha * ln x ^ beta)).
  rewrite /(powerRZ x 2) /=.
  now field.
  rewrite -Rpow_mult_distr.
  have -> : -1 * -1 = 1 by ring. by rewrite pow1 Rmult_1_l.
  move => x Hx.
  rewrite Rmin_right in Hx; try lra.
  rewrite Rmax_left in Hx; try lra.
  apply: continuous_mult.
    apply: continuous_mult.
      exact: continuous_const.
    apply: ex_derive_continuous.
    apply: ex_derive_powerRZ.
    by rewrite /g; right; apply: Rinv_neq_0_compat; lra.
  rewrite /g.
  apply: continuous_ext.
    move => x0.
    by rewrite pow_powerRZ.
  apply: (continuous_comp ln (fun x => powerRZ x (Z.of_nat beta))).
    by apply: continuous_ln; apply: Rinv_0_lt_compat; lra.
  apply: ex_derive_continuous.
    by apply: ex_derive_powerRZ; left; apply: Zle_0_nat.
  move => x Hx.
  rewrite Rmin_right in Hx; try lra.
  rewrite Rmax_left in Hx; try lra.
  split.
    rewrite /g /dg.
    apply: (is_derive_inv (fun x => x) x 1); last by lra.
    exact: is_derive_id.
  rewrite /dg.
  apply: continuous_mult; first exact: continuous_const.
  apply: continuous_Rinv_comp.
    apply: (continuous_ext (fun t => t * t)) => [t|].
      by rewrite pow_powerRZ /=; ring.
    by apply: continuous_mult; exact: continuous_id.
  by apply: pow_nonzero; lra.
Qed.

Lemma f0eps_correct alpha beta epsilon (B : R) (Heps : 0 < / B <= epsilon) (HB : 0 < B) (Halpha : (-1 < alpha)%Z) :
  is_RInt_gen ((fun x => powerRZ x alpha * (pow (ln x) beta))) (at_point (/ B)) (at_point epsilon) (f0eps alpha beta epsilon B).
Proof.
  have Hint : ex_RInt (fun x : R => powerRZ x alpha * ln x ^ beta) (/ B) epsilon.
    eexists.
    apply: f_correct => // .
    by lia.
  have HinvepsinvB : 0 < / epsilon <= B.
    split.
      by apply: Rinv_0_lt_compat; by lra.
      by rewrite -[B]Rinv_involutive; try lra;  apply: Rinv_le; lra.
  rewrite is_RInt_gen_at_point.
  suff: f0eps alpha beta epsilon B = RInt (fun x : R => powerRZ x alpha * ln x ^ beta) (/B) epsilon.
    by move ->; apply: RInt_correct.
  rewrite -RInt_gen_at_point; last first.
  + eexists. apply: f_correct; try lra; try lia.
  + rewrite subst_lemma ; try lra. 2: now apply IZR_lt.
    symmetry.
    rewrite /f0eps. rewrite f_correct_RInt; try lra; try lia.
    rewrite (RInt_ext _ (fun x : R => scal (- (-1) ^ beta) (powerRZ x (-2 - alpha) * ln x ^ beta))); last first.
      by move => x Hx; rewrite /scal [in RHS]/= /mult /=; rewrite Rmult_assoc.
    set e1 := (-2 - alpha)%Z; rewrite RInt_scal /scal /= /mult /= .
    ring_simplify; congr(_ * RInt _ _ _) => // ; field; lra.
    rewrite /e1.
    by eexists; apply: f_correct;  first (split; field_simplify; lra); lia.
Qed.

Lemma f0eps_correct_sing alpha beta epsilon sing (B : R) (Heps : 0 < / B <= epsilon) (HB : 0 < B) (Halpha : (-1 < alpha)%Z) :
  is_RInt_gen ((fun x => powerRZ (x - sing) alpha * (pow (ln (x - sing)) beta))) (at_point (sing + / B)) (at_point (sing + epsilon)) (f0eps alpha beta epsilon B).
Proof.
  apply is_RInt_gen_at_point.
  apply: (is_RInt_translation_sub _ (fun x => powerRZ x alpha * ln x ^ beta)).
  apply is_RInt_gen_at_point.
  have H : forall x y, x + y - x = y by move => x y; ring.
  rewrite !H; apply f0eps_correct => // .
Qed.

Lemma f0eps_lim_is_lim alpha beta epsilon (Halpha : (-1 < alpha)%Z) (Heps : 0 < epsilon) :
  filterlim (fun x : R => f0eps alpha beta epsilon (/ x))
            (at_right 0) (locally (f0eps_lim alpha beta epsilon)).
Proof.
apply: filterlim_comp.
exact: filterlim_Rinv_0_right.
rewrite /f0eps /f0eps_lim.
have H x : ((-1) ^ beta * x) = mult ((-1) ^ beta) x by [].
rewrite H.
apply: filterlim_ext.
  by move => x; first rewrite H.
  rewrite -[locally _]/(Rbar_locally (Rbar_mult (Finite _) (Finite _))).
  rewrite -[filterlim _ _ _]/(is_lim _ p_infty _).
  apply: is_lim_mult => // .
  + exact: is_lim_const.
  + apply: f_lim_is_lim; first exact: Rinv_0_lt_compat.
    by lia.
Qed.

Lemma f0eps_lim_is_lim_sing alpha beta epsilon sing (Halpha : (-1 < alpha)%Z) (Heps : 0 < epsilon) :
  filterlim (fun x : R => f0eps alpha beta epsilon (/ (x - sing)))
            (at_right sing) (locally (f0eps_lim alpha beta epsilon)).
Proof.
  apply: (filterlim_comp _ _ _ (fun x => x - sing) (fun x => f0eps alpha beta epsilon (Rinv x)) _ (at_right 0)).
    move => P [eps HepsP].
    rewrite /filtermap /at_right /within /locally.
    exists eps => y Hy Hsing.
    apply: HepsP.
      have Hepspos : 0 < eps by exact: (cond_pos eps).
        by apply/ball_to_lra; split; move/ball_to_lra: Hy; lra.
      lra.
  exact: f0eps_lim_is_lim.
Qed.

Lemma f0eps_lim_correct alpha beta epsilon (Halpha : (-1 < alpha)%Z) (Heps : 0 < epsilon)  :
  is_RInt_gen ((fun x => powerRZ x alpha * (pow (ln x) beta))) (at_right 0) (at_point epsilon) (f0eps_lim alpha beta epsilon).
Proof.
set eps := mkposreal epsilon Heps.
apply prodi_to_single_r.
apply: (filterlimi_lim_ext_loc (fun x => f0eps alpha beta epsilon (/ x))).
  exists (pos_div_2 eps) => y /= Hy1 Hy2.
  move/ball_to_lra in Hy1.
  have {1}-> : y = / / y by rewrite Rinv_involutive; lra.
  rewrite -is_RInt_gen_at_point.
  apply (f0eps_correct); rewrite ?Rinv_involutive; try lra.
  exact: Rinv_0_lt_compat.
  exact Halpha.
exact: f0eps_lim_is_lim.
Qed.

Lemma f0eps_lim_correct_sing alpha beta epsilon sing (Halpha : (-1 < alpha)%Z) (Heps : 0 < epsilon)  :
  is_RInt_gen ((fun x => powerRZ (x - sing) alpha * (pow (ln (x - sing)) beta))) (at_right sing) (at_point (sing + epsilon)) (f0eps_lim alpha beta epsilon).
Proof.
set eps := mkposreal epsilon Heps.
apply prodi_to_single_r.
apply: (filterlimi_lim_ext_loc (fun x => f0eps alpha beta epsilon (/ (x - sing)))).
  exists (pos_div_2 eps) => y /= Hy1 Hy2.
  move/ball_to_lra in Hy1.
  have {1}-> : y = sing + / / (y - sing) by rewrite Rinv_involutive; lra.
  rewrite -is_RInt_gen_at_point.
  apply f0eps_correct_sing; rewrite ?Rinv_involutive; try lra.
  apply: Rinv_0_lt_compat; lra.
  exact Halpha.
exact: f0eps_lim_is_lim_sing.
Qed.

End ZeroToEpsilon.

Module BertrandInterval (I : IntervalOps).

Module J := IntervalExt I.

Section EffectiveBertrand.
(* TODO: factor out the A^alpha+1 and compute ln A only once for efficiency *)

Variable prec : I.precision.

Section Infinity.

Variable a : R.
Variable A : I.type.
Let iA := I.convert A.

Hypothesis Hcontainsa : contains iA (Xreal a).

Section BertrandLogNegInt.

Definition f_neg_int beta :=
  I.inv prec (I.mul prec (I.fromZ prec (Z.of_nat beta)) (I.power_int prec (I.ln prec A) (Z.of_nat beta))).

Lemma f_neg_int_correct beta : contains (I.convert (f_neg_int beta)) (Xreal (- f_neg a beta)).
Proof.
rewrite /f_neg Ropp_involutive.
apply: J.inv_correct.
apply: J.mul_correct.
  rewrite INR_IZR_INZ.
  exact: I.fromZ_correct.
rewrite pow_powerRZ.
apply: J.power_int_correct.
exact: J.ln_correct.
Qed.

End BertrandLogNegInt.

Fixpoint f_int_aux (alpha : Z) (beta : nat) (A_pow_Salpha : I.type) (ln_A : I.type) {struct beta} : I.type :=
  let alphap1 := I.fromZ prec (alpha + 1) in
  match beta with
  | 0 => I.div prec (I.neg A_pow_Salpha) alphap1
  | S m =>
    let beta := Z.of_nat beta in
    I.sub prec (I.div prec (I.neg (I.mul prec A_pow_Salpha (I.power_int prec ln_A beta))) alphap1)
      (I.mul prec (I.div prec (I.fromZ prec beta) alphap1) (f_int_aux alpha m A_pow_Salpha ln_A))
  end.

Definition f_int_fast (alpha : Z) (beta : nat) :=
  let A_pow_Salpha := I.power_int prec A (alpha+1) in
  let ln_A := I.ln prec A in
  f_int_aux alpha beta A_pow_Salpha ln_A.

Fixpoint f_int (alpha : Z) (beta : nat) {struct beta} : I.type :=
  let alphap1' := (alpha + 1)%Z in
  let alphap1 := I.fromZ prec alphap1' in
  match beta with
  | 0 => I.div prec (I.neg (I.power_int prec A alphap1')) alphap1
  | S m =>
    let beta := Z.of_nat beta in
    I.sub prec (I.div prec (I.neg (I.mul prec (I.power_int prec A alphap1') (I.power_int prec (I.ln prec A) beta))) alphap1)
      (I.mul prec (I.div prec (I.fromZ prec beta) alphap1) (f_int alpha m))
  end.

Lemma f_int_correct alpha beta (H : 0 < a) (Halpha:  alpha <> (-1)%Z) :
  contains (I.convert (f_int alpha beta)) (Xreal (f_lim alpha beta a)).
Proof.
have Salphaneq0 : IZR (alpha + 1) <> 0.
  apply: not_0_IZR.
  by rewrite Z.add_move_0_r.
have an0 : not (is_zero a).
  by move: is_zero_spec; case => // ; lra.
have Salphaneq01: not (is_zero (IZR (alpha + 1))).
  move: (is_zero_spec (IZR (alpha + 1))).
  case => // .
elim: beta => [|m HIm].
- rewrite /= .
  apply: J.div_correct.
  apply: J.neg_correct.
  apply: J.power_int_correct => // ; apply: Hcontainsa.
    exact: I.fromZ_correct.
- rewrite /f_int -/f_int /f_lim -/f_lim.
  apply: J.sub_correct.
  apply: J.div_correct.
  apply: J.neg_correct.
  apply: J.mul_correct.
  apply: J.power_int_correct; apply: Hcontainsa.
  rewrite pow_powerRZ.
  apply: J.power_int_correct.
  apply: J.ln_correct; apply: Hcontainsa.
    exact: I.fromZ_correct.
    apply: J.mul_correct => // .
    apply: J.div_correct.
  by rewrite INR_IZR_INZ; apply: I.fromZ_correct.
  exact: I.fromZ_correct.
Qed.

Lemma f_int_fast_f_int alpha beta : f_int_fast alpha beta = f_int alpha beta.
Proof.
elim: beta => [| beta Hbeta] //= .
  rewrite /f_int_fast //= .
  by rewrite -!Hbeta.
Qed.

Lemma f_int_fast_correct alpha beta (H : 0 < a) (Halpha:  alpha <> (-1)%Z) :
  contains (I.convert (f_int_fast alpha beta)) (Xreal (f_lim alpha beta a)).
Proof.
  by rewrite f_int_fast_f_int; exact: f_int_correct.
Qed.

End Infinity.

Section Sing.

Variable epsilon : R.
Variable Epsilon : I.type.
Let iEps := I.convert Epsilon.

Hypothesis HEps : contains iEps (Xreal epsilon).
Hypothesis eps_gt0 : 0 < epsilon.

Definition f0eps_int (alpha : Z) (beta : nat) :=
  let yi := f_int_fast (I.inv prec Epsilon) (- 2 - alpha) beta in
  if Nat.even beta then yi else I.neg yi.

Lemma f0eps_correct (alpha : Z) (beta : nat) (Halpha : (alpha <> -1)%Z) :
  contains (I.convert (f0eps_int alpha beta)) (Xreal (f0eps_lim alpha beta epsilon)).
Proof.
rewrite /f0eps_int /f0eps_lim.
assert (H: contains (I.convert (f_int_fast (I.inv prec Epsilon) (-2 - alpha) beta)) (Xreal (f_lim (-2 - alpha) beta (/ epsilon)))).
{ rewrite f_int_fast_f_int.
  apply: f_int_correct.
  exact: J.inv_correct.
  exact: Rinv_0_lt_compat.
  by lia. }
replace ((-1) ^ beta) with (if Nat.even beta then 1 else -1).
{ case Nat.even.
  now rewrite Rmult_1_l.
  replace (-1 * _) with (-f_lim (-2 - alpha) beta (/ epsilon)) by ring.
  exact: J.neg_correct. }
clear ; induction beta.
easy.
rewrite Nat.even_succ -Nat.negb_even.
rewrite /= -IHbeta.
case Nat.even => /= ; ring.
Qed.

End Sing.

End EffectiveBertrand.

End BertrandInterval.
