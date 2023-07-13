From Coq Require Import Reals Bool List Lia Lra.
From Flocq Require Import Core BinarySingleNaN Operations.

Open Scope R_scope.

(** Signed computer integers: operations and constants **)


Definition Zcentered_modulo a b := let c := Z.quot b 2 in
  ((a + c) mod b - c)%Z.


Module Type Size.
Parameter bits : positive.
End Size.

Module Size64 <: Size.
Definition bits := 64%positive.
End Size64.


Module SI (S : Size).

Definition bits := S.bits.

Definition N := Z.pow_pos 2 bits.
Definition norm n := Zcentered_modulo n N.

Definition in_bounds n := (- (N/2) <= n <= N/2 - 1)%Z.

Lemma in_bounds_norm : forall n, in_bounds (norm n).
Proof.
  intros n. unfold in_bounds, norm, Zcentered_modulo.
  rewrite Z.quot_div_nonneg.
  2: unfold N ; lia.
  2: easy.
  rewrite <- (Z.lt_succ_r _ (N / 2 - 1)).
  unfold Z.succ ; rewrite Z.sub_add.
  rewrite (Z.add_le_mono_r _ _ (N/2)), (Z.add_lt_mono_r _ _ (N/2)).
  rewrite Z.add_opp_diag_l, Z.sub_add. unfold N.
  rewrite Z.pow_pos_fold.
  rewrite Z.add_diag.
  change 2%Z with (2^1)%Z at 9.
  rewrite <- Z.pow_sub_r by lia.
  rewrite <- Z.pow_succ_r by lia.
  unfold Z.succ ; rewrite Z.sub_add.
  apply Z.mod_pos_bound.
  now apply Z.pow_pos_nonneg.
Qed.

Lemma norm_in_bounds : forall n, in_bounds n -> norm n = n.
Proof.
  intros n. unfold in_bounds, norm, Zcentered_modulo.
  rewrite Z.quot_div_nonneg.
  2: unfold N ; lia.
  2: easy.
  rewrite <- (Z.lt_succ_r _ (N / 2 - 1)).
  unfold Z.succ ; rewrite Z.sub_add.
  rewrite (Z.add_le_mono_r _ _ (N/2)), (Z.add_lt_mono_r _ _ (N/2)).
  rewrite <- (Z.add_cancel_r _ _ (N/2)).
  rewrite Z.add_opp_diag_l. rewrite Z.sub_add. unfold N.
  rewrite Z.pow_pos_fold.
  rewrite Z.add_diag.
  change 2%Z with (2^1)%Z at 7.
  rewrite <- Z.pow_sub_r by lia.
  rewrite <- Z.pow_succ_r by lia.
  unfold Z.succ ; rewrite Z.sub_add.
  apply Z.mod_small.
Qed.

Definition add  n1 n2 := norm (n1 + n2)%Z.
Definition sub  n1 n2 := norm (n1 - n2)%Z.
Definition mul  n1 n2 := norm (n1 * n2)%Z.
Definition div  n1 n2 := norm (n1 / n2)%Z. (* Not expected to be useful for now *)
Definition quot n1 n2 := norm (Z.quot n1 n2).

End SI.

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




(** Floating point numbers: operations and constants **)

Definition prec := Rrnd.prec%Z.
Definition emax := Rrnd.emax%Z.

Lemma HPrec_gt_0 : Prec_gt_0 prec. Proof. easy. Qed.
Lemma HPrec_lt_emax : Prec_lt_emax prec emax. Proof. easy. Qed.

Definition binnorm     md m e   := @binary_normalize _ _ HPrec_gt_0 HPrec_lt_emax md m e false.
Definition FPadd       md x y   := @Bplus _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPsub       md x y   := @Bminus _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPmul       md x y   := @Bmult _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPdiv       md x y   := @Bdiv _ _ HPrec_gt_0 HPrec_lt_emax md x y.
Definition FPfma       md x y z := @Bfma _ _ HPrec_gt_0 HPrec_lt_emax md x y z.
Definition FPnearbyint md x     := @Bnearbyint _ _ HPrec_lt_emax md x.
Definition FPtrunc        x     := @Btrunc prec emax x.
Definition FPldexp     md x e   := @Bldexp _ _ HPrec_gt_0 HPrec_lt_emax md x e.
Definition FPsqrt      md x     := @Bsqrt _ _ HPrec_gt_0 HPrec_lt_emax md x.




(** Typed arithmetic expression trees **)




(* 1. Types and operations on them *)


Inductive ExprType := Integer | BinFloat (*| Pair: ExprType -> ExprType -> ExprType *).


(*
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
*)


(* 1.1. Evaluation as computer types *)


Definition evalExprTypeFloat T := match T with
  | Integer  => Z
  | BinFloat => binary_float prec emax
  end.


Fixpoint evalExprTypeFloat_list Tl : Set := match Tl with
  | nil => unit
  | T :: Tl' => evalExprTypeFloat T * evalExprTypeFloat_list Tl' end.


Fixpoint nthExprTypeFloat {Tl DefaultT} n
   (l : evalExprTypeFloat_list Tl) (default : evalExprTypeFloat DefaultT) :=
  match n with
  | O    => match Tl return evalExprTypeFloat_list Tl -> evalExprTypeFloat (nth O Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => fst l'
            end l
  | S n' => match Tl return evalExprTypeFloat_list Tl -> evalExprTypeFloat (nth (S n') Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => nthExprTypeFloat n' (snd l') default
            end l
  end.



(* 1.2. Evaluation as math types *)


Definition evalExprTypeMath T := match T with
  | Integer  => Z
  | BinFloat => R
  end.


Fixpoint evalExprTypeMath_list Tl : Set := match Tl with
  | nil => unit
  | T :: Tl' => evalExprTypeMath T * evalExprTypeMath_list Tl' end.


Fixpoint evalExprTypeMath_fun  (Tl : list ExprType) := match Tl with
  | nil      => Prop
  | T :: Tl' => evalExprTypeMath T -> evalExprTypeMath_fun Tl' end.


Fixpoint uncurrify {Tl} :=
  match Tl return evalExprTypeMath_fun Tl -> evalExprTypeMath_list Tl -> Prop with
  | nil      => fun f l => f
  | _ :: Tl' => fun f l => uncurrify (f (fst l)) (snd l) end.


Fixpoint nthExprTypeMath {Tl DefaultT} n
   (l : evalExprTypeMath_list Tl) (default : evalExprTypeMath DefaultT) :=
  match n with
  | O    => match Tl return evalExprTypeMath_list Tl -> evalExprTypeMath (nth O Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => fst l'
            end l
  | S n' => match Tl return evalExprTypeMath_list Tl -> evalExprTypeMath (nth (S n') Tl DefaultT) with
            | nil      => fun l' => default
            | T :: Tl' => fun l' => nthExprTypeMath n' (snd l') default
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



(* 1.4. Binary arithmetic operations *)


Inductive ArithOp := ADD | SUB | MUL | DIV.

(*
Definition PIOpToFunction OP := match OP with
  | ADD => PrimInt63.add
  | SUB => PrimInt63.sub
  | MUL => PrimInt63.mul
  | DIV => PrimInt63.div end.

Definition PFOpToFunction OP := match OP with
  | ADD => PrimFloat.add
  | SUB => PrimFloat.sub
  | MUL => PrimFloat.mul
  | DIV => PrimFloat.div end.
*)

Definition SIOpToFunction OP := match OP with
  | ADD => Int64.add
  | SUB => Int64.sub
  | MUL => Int64.mul
  | DIV => Int64.quot end.

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

Inductive ArithExprTree : list ExprType -> ExprType -> Type :=
  | Int:       forall {Tl},       Z ->                             ArithExprTree Tl Integer

  | BinFl:     forall {Tl},       Z ->
                                  Z ->                             ArithExprTree Tl BinFloat

  | Var:       forall {Tl} n,                                      ArithExprTree Tl (nth n Tl Integer)
         (*    forall {Tl T} n, T = (nth n Tl Integer) -> ArithExprTree Tl T *)
         (* or forall Tl n, ArithExprTree Tl (nth n Tl Integer) *)

  | Op:        forall {Tl T},     ArithOp ->
                                  ArithExprTree Tl T ->
                                  ArithExprTree Tl T ->            ArithExprTree Tl T

  | OpExact:   forall {Tl},       ArithOp ->
                                  ArithExprTree Tl BinFloat ->
                                  ArithExprTree Tl BinFloat ->     ArithExprTree Tl BinFloat

  | Fma:       forall {Tl},       ArithExprTree Tl BinFloat ->
                                  ArithExprTree Tl BinFloat ->
                                  ArithExprTree Tl BinFloat ->     ArithExprTree Tl BinFloat

  | FmaExact:  forall {Tl},       ArithExprTree Tl BinFloat ->
                                  ArithExprTree Tl BinFloat ->
                                  ArithExprTree Tl BinFloat ->     ArithExprTree Tl BinFloat

  | NearbyInt: forall {Tl},       ArithExprTree Tl BinFloat ->     ArithExprTree Tl BinFloat

  | Trunc:     forall {Tl},       ArithExprTree Tl BinFloat ->     ArithExprTree Tl Integer

  | FloatInj:  forall {Tl},       ArithExprTree Tl Integer  ->     ArithExprTree Tl BinFloat

  | Ldexp:     forall {Tl},       Z ->
                                  ArithExprTree Tl BinFloat ->
                                  ArithExprTree Tl Integer ->      ArithExprTree Tl BinFloat

  | Sqrt:      forall {Tl T},     ArithExprTree Tl T ->            ArithExprTree Tl T

  | Let:       forall {Tl T1 T2}, ArithExprTree Tl T1 ->
                                  ArithExprTree (T1 :: Tl) T2 ->   ArithExprTree Tl T2

  | Assert:    forall {Tl T},    (evalExprTypeMath T -> evalExprTypeMath_fun Tl) ->
                                  ArithExprTree Tl T ->            ArithExprTree Tl T

  | Postcond:  forall {Tl T},    (evalExprTypeMath T -> evalExprTypeMath_fun Tl) ->
                                  ArithExprTree Tl T ->            ArithExprTree Tl T.

Arguments Op        {Tl} & {T}     OP t1 t2.
Arguments OpExact   {Tl} &         OP t1 t2.
Arguments Fma       {Tl} &            t1 t2 t3.
Arguments FmaExact  {Tl} &            t1 t2 t3.
Arguments Let       {Tl} & {T1 T2}    t1 t2.
Arguments NearbyInt {Tl} &            t.
Arguments Trunc     {Tl} &            t.
Arguments FloatInj  {Tl} &            t.
Arguments Ldexp     {Tl} &          n t1 t2.
Arguments Sqrt      {Tl} & {T}        t.
Arguments Assert    {Tl} & {T}      P t.
Arguments Postcond  {Tl} & {T}      P t.

Set Asymmetric Patterns.

(* 3.2. Definition of evaluation functions *)

Fixpoint evalFloat {Tl T} (t: ArithExprTree Tl T) {struct t}
  :  evalExprTypeFloat_list Tl -> mode -> evalExprTypeFloat T
  := match t with
  | Int       _                  p        => fun l md => p
  | BinFl     _                  x  y     => fun l md => binnorm mode_NE x y
  | Var       _         n                 => fun l md => @nthExprTypeFloat _ Integer n l 0%Z
  | Op        Tl' T'      OP     t1 t2    => fun l md =>
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> evalExprTypeFloat T' with
    | Integer  => fun t1' t2' => SIOpToFunction OP    (evalFloat t1' l md) (evalFloat t2' l md)
    | BinFloat => fun t1' t2' => FPOpToFunction OP md (evalFloat t1' l md) (evalFloat t2' l md)
    end t1 t2
  | OpExact   _           OP     t1 t2    => fun l md => FPOpToFunction OP md (evalFloat t1 l md) (evalFloat t2 l md)
  | Fma       _                  t1 t2 t3
  | FmaExact  _                  t1 t2 t3 => fun l md => FPfma md (evalFloat t1 l md) (evalFloat t2 l md) (evalFloat t3 l md)
  | NearbyInt _                  t        => fun l md => FPnearbyint mode_NE (evalFloat t l md)
  | Trunc     _                  t        => fun l md => FPtrunc (evalFloat t l md)
  | FloatInj  _                  t        => fun l md => binnorm mode_NE (evalFloat t l md) 0
  | Ldexp     _              _   t1 t2    => fun l md => FPldexp md (evalFloat t1 l md) (evalFloat t2 l md)
  | Sqrt      Tl' T'             t        => fun l md =>
    match T' return ArithExprTree Tl' T' -> evalExprTypeFloat T' with
    | Integer  => fun t' => Z.sqrt    (evalFloat t' l md)
    | BinFloat => fun t' => FPsqrt md (evalFloat t' l md)
    end t
  | Let       _   _  _           t1 t2    => fun l md => let x := evalFloat t1 l md in evalFloat t2 (x, l) md
  | Assert    _   _            _ t
  | Postcond  _   _            _ t        => fun l md => evalFloat t l md
  end.

Fixpoint evalExact {Tl T} (t: ArithExprTree Tl T) {struct t}
  :  evalExprTypeMath_list Tl -> evalExprTypeMath T
  := match t with
  | Int       _                  p        => fun l => p
  | BinFl     _                  x  y     => fun l => IZR x * Rpow2 y
  | Var       _         n                 => fun l => @nthExprTypeMath _ Integer n l 0%Z
  | Op        Tl' T'      OP     t1 t2    => fun l =>
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> evalExprTypeMath T' with
    | Integer  => fun t1' t2' => ZOpToFunction OP (evalExact t1' l) (evalExact t2' l)
    | BinFloat => fun t1' t2' => ROpToFunction OP (evalExact t1' l) (evalExact t2' l)
    end t1 t2
  | OpExact   _           OP     t1 t2    => fun l => ROpToFunction OP (evalExact t1 l) (evalExact t2 l)
  | Fma       _                  t1 t2 t3
  | FmaExact  _                  t1 t2 t3 => fun l => (evalExact t1 l) * (evalExact t2 l) + (evalExact t3 l)
  | NearbyInt _                  t        => fun l => @Rrnd.nearbyint mode_NE (evalExact t l)
  | Trunc     _                  t        => fun l => Ztrunc (evalExact t l)
  | FloatInj  _                  t        => fun l => IZR (evalExact t l)
  | Ldexp     _              _   t1 t2    => fun l => (evalExact t1 l) * Rpow2 (evalExact t2 l)
  | Sqrt      Tl' T'             t        => fun l =>
    match T' return ArithExprTree Tl' T' -> evalExprTypeMath T' with
    | Integer  => fun t' => Z.sqrt (evalExact t' l)
    | BinFloat => fun t' => sqrt   (evalExact t' l)
    end t
  | Let       _   _  _           t1 t2    => fun l => let x := evalExact t1 l in evalExact t2 (x, l)
  | Assert    _   _            _ t
  | Postcond  _   _            _ t        => fun l => evalExact t l
  end.

Fixpoint evalRounded {Tl T} (t: ArithExprTree Tl T) {struct t}
  :  evalExprTypeMath_list Tl -> mode -> evalExprTypeMath T
  := match t with
  | Int       _                  p        => fun l md => p : evalExprTypeMath Integer
  | BinFl     _                  x  y     => fun l md => IZR x * Rpow2 y
  | Var       _         n                 => fun l md => @nthExprTypeMath _ Integer n l 0%Z
  | Op        Tl' T'      OP     t1 t2    => fun l md =>
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> evalExprTypeMath T' with
    | Integer  => fun t1' t2' => ZOpToFunction    OP    (evalRounded t1' l md) (evalRounded t2' l md)
    | BinFloat => fun t1' t2' => RrndOpToFunction OP md (evalRounded t1' l md) (evalRounded t2' l md)
    end t1 t2
  | OpExact   _           OP     t1 t2    => fun l md => ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md)
  | Fma       _                  t1 t2 t3 => fun l md => @Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md)
  | FmaExact  _                  t1 t2 t3 => fun l md => (evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)
  | NearbyInt _                  t        => fun l md => @Rrnd.nearbyint mode_NE (evalRounded t l md)
  | Trunc     _                  t        => fun l md => Ztrunc (evalRounded t l md)
  | FloatInj  _                  t        => fun l md => IZR (evalRounded t l md)
  | Ldexp     _              _   t1 t2    => fun l md => @Rrnd.ldexp md (evalRounded t1 l md) (evalRounded t2 l md)
  | Sqrt      Tl' T'             t        => fun l md =>
    match T' return ArithExprTree Tl' T' -> evalExprTypeMath T' with
    | Integer  => fun t' => Z.sqrt        (evalRounded t' l md)
    | BinFloat => fun t' => @Rrnd.sqrt md (evalRounded t' l md)
    end t
  | Let       _   _  _           t1 t2    => fun l md => let x := evalRounded t1 l md in evalRounded t2 (x, l) md
  | Assert    _   _            _ t
  | Postcond  _   _            _ t        => fun l md => evalRounded t l md
  end.

(*
Fixpoint evalExactR {Tl T} (t: ArithExprTree Tl T) {struct t} : evalExprTypeReal_list Tl -> _ :=
  match t in ArithExprTree Tl'' T'' return evalExprTypeReal_list Tl'' -> _ with
  | Int       _                  p        => fun l => IZR p
  | BinFl     _                  x  y     => fun l => IZR x * Rpow2 y
  | Var       _         n                 => fun l => nthExprTypeReal n l 0
  | Op        _           OP     t1 t2    => fun l => ROpToFunction OP (evalExactR t1 l) (evalExactR t2 l)
  | OpExact   Tl' T'      OP     t1 t2    => fun l =>
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> _ with
    | Integer  => fun t1' t2' => match OP with
      | DIV => Rrnd.truncint (evalExactR t1' l / evalExactR t2' l)
      | _     => ROpToFunction OP (evalExactR t1' l) (evalExactR t2' l)
      end
    | BinFloat => fun t1' t2' => ROpToFunction OP (evalExactR t1' l) (evalExactR t2' l)
    end t1 t2
  | Fma       _                  t1 t2 t3
  | FmaExact  _                  t1 t2 t3 => fun l => evalExactR t1 l * evalExactR t2 l + evalExactR t3 l
  | NearbyInt _                  t        => fun l => Rrnd.nearbyint (evalExactR t l)
  | Trunc     _                  t        => fun l => Rrnd.truncint (evalExactR t l)
  | Ldexp     _              _   t1 t2    => fun l => evalExactR t1 l * Rpower 2 (evalExactR t2 l)
  | Let       _   _  _           t1 t2    => fun l => let x := evalExactR t1 l in evalExactR t2 (x, l)
  | Assert    _   _            _ t
  | Postcond  _   _            _ t        => fun l => evalExactR t l
  end. *)

Fixpoint evalRoundedR {Tl T} (t: ArithExprTree Tl T) {struct t}
  :  evalExprTypeReal_list Tl -> _
  := match t with
  | Int       _                  p        => fun l md => IZR p
  | BinFl     _                  x  y     => fun l md => IZR x * Rpow2 y
  | Var       _         n                 => fun l md => nthExprTypeReal n l 0
  | Op        Tl' T'      OP     t1 t2    => fun l md =>
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> _ with
    | Integer  => fun t1' t2' => match OP with
      | DIV => Rrnd.trunc       (evalRoundedR t1' l md / evalRoundedR t2' l md)
      | _   => ROpToFunction OP (evalRoundedR t1' l md) (evalRoundedR t2' l md)
      end
    | BinFloat => fun t1' t2' => RrndOpToFunction OP md (evalRoundedR t1' l md) (evalRoundedR t2' l md)
    end t1 t2
  | OpExact   _           OP     t1 t2    => fun l md => ROpToFunction OP (evalRoundedR t1 l md) (evalRoundedR t2 l md)
  | Fma       _                  t1 t2 t3 => fun l md => @Rrnd.fma md (evalRoundedR t1 l md) (evalRoundedR t2 l md) (evalRoundedR t3 l md)
  | FmaExact  _                  t1 t2 t3 => fun l md => evalRoundedR t1 l md * evalRoundedR t2 l md + evalRoundedR t3 l md
  | NearbyInt _                  t        => fun l md => @Rrnd.nearbyint mode_NE (evalRoundedR t l md)
  | Trunc     _                  t        => fun l md => Rrnd.trunc    (evalRoundedR t l md)
  | FloatInj  _                  t        => fun l md => evalRoundedR t l md
  | Ldexp     _              _   t1 t2    => fun l md =>
      round radix2 (FLT_exp Rrnd.emin Rrnd.prec) (round_mode md)
        (evalRoundedR t1 l md * Rpower 2 (evalRoundedR t2 l md))
  | Sqrt      Tl' T'             t        => fun l md =>
    match T' return ArithExprTree Tl' T' -> _ with
    | Integer  => fun t' => Rrnd.trunc (sqrt (evalRoundedR t' l md))
    | BinFloat => fun t' => @Rrnd.sqrt md    (evalRoundedR t' l md)
    end t
  | Let       _   _  _           t1 t2    => fun l md => let x := evalRoundedR t1 l md in evalRoundedR t2 (x, l) md
  | Assert    _   _            _ t
  | Postcond  _   _            _ t        => fun l md => evalRoundedR t l md
  end.

Definition eqExprType {T} := match T return evalExprTypeFloat T -> evalExprTypeMath T -> _ with
  | Integer  => fun n1 n2 => n1 = n2
  | BinFloat => fun  f  r => is_finite f = true /\ B2R f = r
  end.

Fixpoint assertions {Tl T} (t : ArithExprTree Tl T) : evalExprTypeMath_list Tl -> _ :=
  match t with

  | Int       _             _
  | BinFl     _             _  _
  | Var       _     _                => fun l md => True


  | Op        _ _     _     t1 t2
  | OpExact   _       _     t1 t2
  | Ldexp     _         _   t1 t2    => fun l md => assertions t1 l md
                                                 /\ assertions t2 l md

  | Fma       _             t1 t2 t3
  | FmaExact  _             t1 t2 t3 => fun l md => assertions t1 l md
                                                 /\ assertions t2 l md
                                                 /\ assertions t3 l md

  | NearbyInt _             t
  | Trunc     _             t
  | FloatInj  _             t
  | Sqrt      _ _           t        => fun l md => assertions t l md

  | Let       _ _ _         t1 t2    => fun l md => assertions t1 l md
                                                 /\ let x := evalRounded t1 l md in
                                                    assertions t2 (x, l) md

  | Assert    _ _         P t        => fun l md => let P' := P (evalExact t l) in
                                                    uncurrify P' l /\ assertions t l md

  | Postcond  _ _         _ t        => fun l md => assertions t l  md
  end.


Fixpoint wellDefined {Tl T} (t: ArithExprTree Tl T) : evalExprTypeMath_list Tl -> _ :=
  match t with

  | Int       _                 _
  | BinFl     _                 _  _
  | Var       _        _                 => fun l md => True

  | Op        _   T'     OP     t1 t2    => fun l md =>
    let P := wellDefined t1 l md /\ wellDefined t2 l md in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> match T' with Integer => 0%Z | _ => 0 end
    | _   => P
    end

  | OpExact   _          OP     t1 t2    => fun l md =>
    let P := wellDefined t1 l md /\ wellDefined t2 l md in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> 0
    | _   => P
    end

  | Fma       _                 t1 t2 t3
  | FmaExact  _                 t1 t2 t3 => fun l md =>
    wellDefined t1 l md /\ wellDefined t2 l md /\ wellDefined t3 l md

  | NearbyInt _                 t
  | Trunc     _                 t
  | FloatInj  _                 t        => fun l md => wellDefined t l md

  | Sqrt      Tl' T'            t        => fun l md => wellDefined t l md /\
    match T' return ArithExprTree Tl' T' -> _ with
    | Integer => fun t' => IZR (evalRounded t' l md) >= 0
    | _       => fun t' => evalRounded t' l md >= 0
    end t

  | Ldexp     _             _   t1 t2    => fun l md =>
    wellDefined t1 l md /\ wellDefined t2 l md

  | Let       _   _  _          t1 t2    => fun l md =>
    wellDefined t1 l md /\ wellDefined t2 (evalRounded t1 l md, l) md

  | Assert    _   _           _ t
  | Postcond  _   _           _ t        => fun l md => wellDefined t l md
  end.


Fixpoint operationsExact {Tl T} (t: ArithExprTree Tl T) : evalExprTypeMath_list Tl -> _ :=
  match t with

  | Int       _                 _
  | BinFl     _                 _  _
  | Var       _        _                 => fun l md => True

  | Op        Tl' T'     OP     t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> _ with
    | Integer  => fun t1' t2' =>
      - IZR (Int64.N / 2) <= IZR (ZOpToFunction OP (evalRounded t1' l md) (evalRounded t2' l md)) <= IZR (Int64.N / 2 - 1)
    | BinFloat => fun t1' t2' => Rabs (RrndOpToFunction OP md (evalRounded t1' l md) (evalRounded t2' l md)) <= Rrnd.maxval
    end t1 t2

  | OpExact   _          OP     t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\
    Rabs (ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md)) <= Rrnd.maxval /\
    RrndOpToFunction OP md (evalRounded t1 l md) (evalRounded t2 l md)
     = ROpToFunction OP    (evalRounded t1 l md) (evalRounded t2 l md)

  | Fma       _                 t1 t2 t3 => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\ operationsExact t3 l md /\
    Rabs (@Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md)) <= Rrnd.maxval

  | FmaExact  _                 t1 t2 t3 => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\ operationsExact t3 l md /\
    Rabs ((evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)) <= Rrnd.maxval /\
    @Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md) =
    (evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)

  | NearbyInt _                 t
  | Trunc     _                 t        => fun l md => operationsExact t l md

  | FloatInj  _                 t        => fun l md => operationsExact t l md /\ Rabs (IZR (evalRounded t l md)) <= Rpow2 53

  | Sqrt      _   _             t        => fun l md => operationsExact t l md

  | Ldexp     _             n   t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 l md /\
    Rabs (evalRounded t1 l md) <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec) /\
    IZR (n + evalRounded t2 l md) <= IZR Rrnd.emax

  | Let       _   _  _          t1 t2    => fun l md =>
    operationsExact t1 l md /\ operationsExact t2 (evalRounded t1 l md, l) md

  | Assert    _   _           _ t
  | Postcond  _   _           _ t        => fun l md => operationsExact t l md
  end.

Fixpoint wellBehaved {Tl T} (t: ArithExprTree Tl T) : evalExprTypeMath_list Tl -> _ :=
  match t with

  | Int       _                  _
  | BinFl     _                  _  _
  | Var       _        _                 => fun l md => True

  | Op        Tl' T'     OP     t1 t2    => fun l md => wellBehaved t1 l md /\ wellBehaved t2 l md /\ let P :=
    match T' return ArithExprTree Tl' T' -> ArithExprTree Tl' T' -> _ with
    | Integer  => fun t1' t2' => - IZR (Int64.N / 2) <= IZR (ZOpToFunction OP (evalRounded t1' l md) (evalRounded t2' l md)) <= IZR (Int64.N / 2 - 1)
    | BinFloat => fun t1' t2' => Rabs (RrndOpToFunction OP md (evalRounded t1' l md) (evalRounded t2' l md)) <= Rrnd.maxval end t1 t2 in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> match T' with Integer => 0%Z | _ => 0 end
    | _   => P
    end

  | OpExact   _          OP     t1 t2    => fun l md => let P := wellBehaved t1 l md /\ wellBehaved t2 l md /\
    Rabs (ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md)) <= Rrnd.maxval /\
    RrndOpToFunction OP md (evalRounded t1 l md) (evalRounded t2 l md) = ROpToFunction OP (evalRounded t1 l md) (evalRounded t2 l md) in
    match OP with
    | DIV => P /\ evalRounded t2 l md <> 0
    |_    => P
    end

  | Fma       _                 t1 t2 t3 => fun l md =>
    wellBehaved t1 l md /\ wellBehaved t2 l md /\ wellBehaved t3 l md /\
    Rabs (@Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md)) <= Rrnd.maxval

  | FmaExact  _                 t1 t2 t3 => fun l md =>
    wellBehaved t1 l md /\ wellBehaved t2 l md /\ wellBehaved t3 l md /\
    Rabs ((evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)) <= Rrnd.maxval /\
    @Rrnd.fma md (evalRounded t1 l md) (evalRounded t2 l md) (evalRounded t3 l md) =
    (evalRounded t1 l md) * (evalRounded t2 l md) + (evalRounded t3 l md)

  | NearbyInt _                 t
  | Trunc     _                 t        => fun l md => wellBehaved t l md

  | FloatInj  _                 t        => fun l md => wellBehaved t l md /\ Rabs (IZR (evalRounded t l md)) <= Rpow2 53

  | Sqrt      Tl' T'            t        => fun l md => wellBehaved t l md /\
    match T' return ArithExprTree Tl' T' -> _ with
    | Integer => fun t' => IZR (evalRounded t' l md) >= 0
    | _       => fun t' => evalRounded t' l md >= 0
    end t

  | Ldexp     _             n   t1 t2    => fun l md => wellBehaved t1 l md /\ wellBehaved t2 l md /\
    Rabs (evalRounded t1 l md)  <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec) /\
    IZR (n + evalRounded t2 l md) <= IZR Rrnd.emax

  | Let       _   _  _          t1 t2    => fun l md => wellBehaved t1 l md /\ wellBehaved t2 (evalRounded t1 l md, l) md

  | Assert    _   _           _ t
  | Postcond  _   _           _ t        => fun l md => wellBehaved t l md
  end.


Fixpoint postconditions {Tl T} (t : ArithExprTree Tl T) : evalExprTypeMath_list Tl -> _ :=
  match t with

  | Int       _             _
  | BinFl     _             _  _
  | Var       _     _                => fun l md => True


  | Op        _ _     _     t1 t2
  | OpExact   _       _     t1 t2
  | Ldexp     _         _   t1 t2    => fun l md => postconditions t1 l md
                                              /\ postconditions t2 l md

  | Fma       _             t1 t2 t3
  | FmaExact  _             t1 t2 t3 => fun l md => postconditions t1 l md
                                              /\ postconditions t2 l md
                                              /\ postconditions t3 l md

  | NearbyInt _             t
  | Trunc     _             t
  | FloatInj  _             t
  | Sqrt      _ _           t        => fun l md => postconditions t l md

  | Let       _ _ _         t1 t2    => fun l md => postconditions t1 l md
                                              /\ let x := evalRounded t1 l md in
                                                 postconditions t2 (x, l) md

  | Assert    _ _         _ t        => fun l md => postconditions t l md

  | Postcond  _ _         P t        => fun l md => let P' := P (evalRounded t l md) in
                                                 uncurrify P' l /\ postconditions t l md
  end.


Definition fullyCorrect {Tl T} (t: ArithExprTree Tl T) l md :=
  assertions t l md -> (wellBehaved t l md /\ postconditions t l md).

(* TODO: maybe move those proof obligations to the constructors *)
Fixpoint wellFormed {Tl T} (t: ArithExprTree Tl T) := match t with
  | Int          _             n        => (- Z.pow_pos 2 (Int64.bits - 1) <=? n)%Z
                                        && (n <? Z.pow_pos 2 (Int64.bits - 1))%Z

  | BinFl        _             x  y     => (Z.abs x <? radix2 ^ Rrnd.prec)%Z
                                        && (SpecFloat.emin Rrnd.prec Rrnd.emax <=? y)%Z
                                        && (y <=? Rrnd.emax - Rrnd.prec)%Z

  | Var          _     _                => true

  | Op           _ _     _     t1 t2
  | OpExact      _       _     t1 t2
  | Ldexp        _         _   t1 t2    => wellFormed t1 && wellFormed t2

  | Fma          _             t1 t2 t3
  | FmaExact     _             t1 t2 t3 => wellFormed t1 && wellFormed t2 && wellFormed t3

  | Let          _ _ _         t1 t2    => wellFormed t1 && wellFormed t2

  | NearbyInt    _             t
  | Trunc        _             t
  | FloatInj     _             t
  | Sqrt         _ _           t
  | Assert       _ _         _ t
  | Postcond     _ _         _ t        => wellFormed t
  end.

Definition C2M {T} :=
  match T return evalExprTypeFloat T -> evalExprTypeMath T with
  | Integer  => fun x => x
  | BinFloat => fun x => B2R x
  end.

Fixpoint C2M_list {Tl} :=
  match Tl return evalExprTypeFloat_list Tl -> evalExprTypeMath_list Tl with
  | nil    => fun l => tt
  | _ :: _ => fun l => (C2M (fst l), C2M_list (snd l))
  end.

Definition M2R {T} :=
  match T return evalExprTypeMath T -> _ with
  | Integer  => fun x => IZR x
  | BinFloat => fun x => x
  end.

Fixpoint M2R_list {Tl} :=
  match Tl return evalExprTypeMath_list Tl -> evalExprTypeReal_list Tl with
  | nil    => fun l => tt
  | _ :: _ => fun l => (M2R (fst l), M2R_list (snd l))
  end.

Fixpoint is_finite_list {Tl} :=
  match Tl return evalExprTypeFloat_list Tl -> _ with
  | nil           => fun lC => True
  | Integer  :: _ => fun lC => is_finite_list (snd lC)
  | BinFloat :: _ => fun lC => is_finite (fst lC) = true /\ is_finite_list (snd lC)
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

Lemma evalRoundedR_evalRounded {Tl T} :
  forall (t: ArithExprTree Tl T) (lM : evalExprTypeMath_list Tl) md,
  let lR := M2R_list lM in
  evalRoundedR t lR md = M2R (evalRounded t lM md).
Proof.
induction t as [| | | Tl T OP | Tl OP | | | | | | | Tl T | | |].
- easy.
- easy.
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
- intros lM md lR. simpl in *. unfold lR. rewrite <-round_FIX_IZR.
  now rewrite IHt.
- intros lM md lR. simpl in *. unfold lR. now rewrite IHt.
- intros lM md lR. simpl in *. unfold lR, Rrnd.ldexp. rewrite bpow_exp.
  now rewrite IHt1, IHt2.
- intros lM md lR. simpl in *. unfold lR. destruct T.
  + unfold Rrnd.nearbyint, round, F2R, scaled_mantissa. simpl. rewrite 2Rmult_1_r.
    rewrite Ztrunc_floor by apply sqrt_ge_0. apply f_equal. rewrite IHt.
    apply trunc_sqrt.
  + now rewrite IHt.
- intros lM md lR. now destruct T1;
    unfold lR in *; simpl in *; rewrite IHt1;
    fold evalExprTypeReal_list in *; fold evalExprTypeMath_list in *;
    specialize (IHt2 (evalRounded t1 lM md, lM)); simpl in IHt2;
    rewrite IHt2.
- easy.
- intros lM md lR. simpl in *. unfold lR. now apply IHt.
Qed.

Lemma wellBehaved_decompose {Tl T} :
  forall (t: ArithExprTree Tl T) (l : evalExprTypeMath_list Tl) md,
  wellBehaved t l md <-> wellDefined t l md /\ operationsExact t l md.
Proof.
induction t as [| | | Tl T OP | Tl OP | | | | | | | Tl T | | |].
- easy.
- easy.
- easy.
- intros l md. now destruct OP; simpl; rewrite IHt1, IHt2; [| | | destruct T].
- intros l md. now destruct OP; simpl; rewrite IHt1, IHt2.
- intros l md. simpl. now rewrite IHt1, IHt2, IHt3.
- intros l md. simpl. now rewrite IHt1, IHt2, IHt3.
- easy.
- easy.
- intros l md. simpl. now rewrite IHt.
- intros l md. simpl. now rewrite IHt1, IHt2.
- intros l md. simpl. now rewrite IHt.
- intros l md. simpl. now rewrite IHt1, IHt2.
- easy.
- easy.
Qed.


Theorem evalFloat_evalRounded {Tl T} :
  forall (t: ArithExprTree Tl T) (lC : evalExprTypeFloat_list Tl) md,
  is_finite_list lC -> let lM := C2M_list lC in
  wellBehaved t lM md -> wellFormed t = true ->
  eqExprType (evalFloat t lC md) (evalRounded t lM md).
Proof. simpl. intros t lC md HlC. rewrite wellBehaved_decompose. intros [IWD IOE] IWF.
induction t as [| | | Tl T OP | Tl OP | | | | | | | Tl T | | |]; simpl; [easy |..].
13, 14: now apply IHt.


- apply andb_prop in IWF. destruct IWF as [IWF  IWF2].
  apply andb_prop in IWF. destruct IWF as [IWF0 IWF1].
  unfold binnorm.

  generalize (binary_normalize_correct _ _ HPrec_gt_0 HPrec_lt_emax mode_NE z z0 false).
  unfold prec, emax. cbv zeta. rewrite Rlt_bool_true.
  { intros [H1 [H2 H3]]. split; [assumption |].
    rewrite H1. apply round_generic; [apply valid_rnd_round_mode |].
    apply generic_format_FLT. now exists (Float radix2 z z0);
     [| apply Zlt_is_lt_bool | apply Zle_is_le_bool]. }

  rewrite round_generic; [| apply valid_rnd_round_mode |].
  2: { apply generic_format_FLT. now exists (Float radix2 z z0);
    [| apply Zlt_is_lt_bool | apply Zle_is_le_bool]. }

  rewrite <-F2R_Zabs. unfold F2R. simpl Defs.Fnum. simpl Defs.Fexp.
  replace Rrnd.emax with ((Rrnd.emax - z0) + z0)%Z; [| apply Z.sub_add].
  rewrite bpow_plus. apply Rmult_lt_compat_r; [apply bpow_gt_0 |].
  apply Rlt_le_trans with (Rpow2 53).
  { apply Zlt_is_lt_bool in IWF0. now apply IZR_lt. }

  apply bpow_le. replace 53%Z with (0 - (-53))%Z; [| easy].
  apply Z.le_sub_le_add. now apply Zle_is_le_bool in IWF2.


- revert n IWD IOE IWF.

  induction Tl as [| T Tl]; [now destruct n |].
  now destruct T; (destruct n; simpl in *; [| apply IHTl]).


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].

  destruct T.
  { destruct OP.
    1, 2, 3: destruct IWD as [IWDt1 IWDt2].
    4: destruct IWD as [[IWDt1 IWDt2] nonzero_t2].
    all: simpl in IOE.
    all: destruct IOE as [IOEt1 [IOEt2 morphOp]]. all: simpl.
    all: rewrite (IHt1 lC), (IHt2 lC); [| easy..].
    all: apply Int64.norm_in_bounds. all: unfold Int64.in_bounds.
    all: now refine (let '(conj H1 H2) := _ in conj (le_IZR _ _ H1) (le_IZR _ _ H2)). }
  destruct OP.
  1, 2, 3: destruct IWD as [IWDt1 IWDt2].
  4: destruct IWD as [[IWDt1 IWDt2] nonzero_t2].
  all: destruct IOE as [IOEt1 [IOEt2 morphOp]].
  all: simpl in *.

  + destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bplus_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    { intros [H1 [H2 H3]]; [assumption.. | split; [easy |]].
      unfold FPadd, prec, emax in *. now rewrite H1, B2Rt1, B2Rt2. }
    unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2. simpl round_mode.
    apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.

  + destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bminus_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    { intros [H1 [H2 H3]]; [assumption.. | split; [easy |]].
       unfold FPsub, prec, emax in *. now rewrite H1, B2Rt1, B2Rt2. }
    unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2. simpl round_mode.
    change (SpecFloat.fexp 53 1024) with (FLT_exp (-1074) 53).
    apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.

  + destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bmult_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    * intros [H1 [H2 H3]]. split; unfold FPmul, prec, emax.
      -- rewrite H2. apply andb_true_intro. split; easy.
      -- rewrite H1. unfold FPmul. unfold prec, emax in B2Rt1, B2Rt2.
          now rewrite B2Rt1, B2Rt2.
    * unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2.
      apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.

  + destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bdiv_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    * intros [H1 [H2 H3]].
      -- unfold prec, emax in B2Rt1, B2Rt2. now rewrite B2Rt2.
      -- split; unfold FPdiv, prec, emax; [now rewrite H2 |].
         rewrite H1. unfold FPdiv. unfold prec, emax in B2Rt1, B2Rt2.
         now rewrite B2Rt1, B2Rt2.
    * unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2.
      apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 morphOp]].

  destruct OP.
  1, 2, 3: destruct IWD as [IWDt1 IWDt2].
  4: destruct IWD as [[IWDt1 IWDt2] nonzero_t2].
  all: simpl in *.

  + destruct morphOp as [BoundedAdd ExactAdd]. rewrite <-ExactAdd in BoundedAdd.
    destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bplus_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    { intros [H1 [H2 H3]]; [assumption.. | split; [easy |]].
       unfold FPadd, prec, emax in *. now rewrite H1, B2Rt1, B2Rt2. }
    unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2.
    apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.

  + destruct morphOp as [BoundedSub ExactSub]. rewrite <-ExactSub in BoundedSub.
    destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bminus_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    { intros [H1 [H2 H3]]; [assumption.. | split; [easy |]].
       unfold FPsub, prec, emax in *. now rewrite H1, B2Rt1, B2Rt2. }
    unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2.
    apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.

  + destruct morphOp as [BoundedMul ExactMul]. rewrite <-ExactMul in BoundedMul.
    destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bmult_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    * intros [H1 [H2 H3]]. split; unfold FPmul, prec, emax.
      -- rewrite H2. apply andb_true_intro. split; easy.
      -- rewrite H1. unfold FPmul. unfold prec, emax in B2Rt1, B2Rt2.
          now rewrite B2Rt1, B2Rt2.
    * unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2.
      apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.

  + destruct morphOp as [BoundedDiv ExactDiv].
    rewrite <-ExactDiv in BoundedDiv.
    destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2]; try easy.
    generalize (Bdiv_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
    unfold prec, emax. rewrite Rlt_bool_true.
    * intros [H1 [H2 H3]].
      -- unfold prec, emax in B2Rt1, B2Rt2. now rewrite B2Rt2.
      -- split; unfold FPdiv, prec, emax; [now rewrite H2 |].
         rewrite H1. unfold FPdiv. unfold prec, emax in B2Rt1, B2Rt2.
         now rewrite B2Rt1, B2Rt2.
    * unfold prec, emax in B2Rt1, B2Rt2. rewrite B2Rt1, B2Rt2.
      apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWF IWFt3]. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 [IOEt3 morphOp]]].
  destruct IWD as [IWDt1 [IWDt2 IWDt3]].

  destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2],
           (IHt3 lC) as [fint3 B2Rt3]; try easy.
  rewrite <-B2Rt1, <-B2Rt2, <-B2Rt3.
  generalize (Bfma_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md) (evalFloat t3 lC md)).
  unfold prec, emax. rewrite Rlt_bool_true; [now intros [H1 [H2 _]] |].
  unfold prec, emax in B2Rt1, B2Rt2, B2Rt3. rewrite B2Rt1, B2Rt2, B2Rt3.
  apply Rle_lt_trans with Rrnd.maxval; [assumption |]. apply Rrnd.maxval_lt.


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWF IWFt3]. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IOE as [IOEt1 [IOEt2 [IOEt3 morphOp]]].
  destruct IWD as [IWDt1 [IWDt2 IWDt3]].

  destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC) as [fint2 B2Rt2],
           (IHt3 lC) as [fint3 B2Rt3]; try easy.
  rewrite <-B2Rt1, <-B2Rt2, <-B2Rt3.
  generalize (Bfma_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md) (evalFloat t3 lC md)).
  unfold prec, emax. rewrite Rlt_bool_true; [intros [H1 [H2 H3]]; [easy.. |
    unfold FPfma, prec, emax in *; unfold Rrnd.fma in morphOp; now rewrite H1, B2Rt1, B2Rt2, B2Rt3] |].
  unfold prec, emax in B2Rt1, B2Rt2, B2Rt3. rewrite B2Rt1, B2Rt2, B2Rt3.
  destruct morphOp as [BoundedFma ExactFma]. rewrite <-ExactFma in BoundedFma.
  apply Rle_lt_trans with Rrnd.maxval; [easy |]. apply Rrnd.maxval_lt.


- destruct (IHt lC) as [fint B2Rt]; try assumption.
  generalize (Bnearbyint_correct _ _ HPrec_lt_emax mode_NE (evalFloat t lC md)).
  unfold prec, emax. intros [H1 [H2 H3]]. split; unfold FPnearbyint, prec, emax.
  + now rewrite H2.
  + rewrite H1. now apply f_equal.


- destruct (IHt lC) as [fint B2Rt]; try assumption. rewrite <-B2Rt.
  generalize (Btrunc_correct _ _ HPrec_lt_emax (evalFloat t lC md)).
  unfold FPtrunc. rewrite round_FIX_IZR. apply eq_IZR.


- destruct IOE as [IOE Reprt]. generalize (binary_normalize_correct _ _
    HPrec_gt_0 HPrec_lt_emax mode_NE (evalRounded t (C2M_list lC) md) 0%Z false).
  rewrite IHt; try easy. unfold binnorm, prec, emax in *. simpl in *.
  rewrite Rlt_bool_true.
  + rewrite Rabs_Zabs in Reprt. apply le_IZR in Reprt.
    intros [H1 [H2 _]]. unfold binnorm. split; [easy |]. rewrite H1.
    unfold F2R, scaled_mantissa. simpl. rewrite Rmult_1_r.
    apply round_generic; [apply valid_rnd_N |].
    unfold prec, emax, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax.
    unfold SpecFloat.fexp. change (SpecFloat.emin 53 1024) with (-1074)%Z.
    fold (FLT_exp (-1074) 53). apply generic_format_FLT.
    apply Zle_lt_or_eq in Reprt. destruct Reprt as [Reprt | Reprt]; [|
      destruct (Z.abs_spec (evalRounded t (C2M_list lC) md)) as [[_ H] | [_ H]];
      rewrite H in Reprt; clear H].
    * apply (FLT_spec _ _ _ _ (Float radix2 (evalRounded t (C2M_list lC) md) 0)); [| easy..].
      unfold F2R, scaled_mantissa. simpl. now rewrite Rmult_1_r.
    * rewrite Reprt. apply (FLT_spec _ _ _ _ (Float radix2 1 53)); [| easy..].
      unfold F2R, scaled_mantissa. simpl Defs.Fnum. simpl Defs.Fexp. now rewrite Rmult_1_l.
    * rewrite <-(Z.opp_involutive (evalRounded t (C2M_list lC) md)). rewrite Reprt.
      apply (FLT_spec _ _ _ _ (Float radix2 (-1) 53)); [| easy..].
      unfold F2R, scaled_mantissa. simpl Defs.Fnum. simpl Defs.Fexp.
      now rewrite opp_IZR, IZR_NEG, <-Ropp_mult_distr_l, Rmult_1_l.
  + unfold F2R, scaled_mantissa. simpl. rewrite Rmult_1_r.
    apply (Rle_lt_trans _ (IZR (Z.pow_pos 2 53))); [| now apply IZR_lt].
    rewrite <-round_NE_abs; [| now apply fexp_correct]. revert Reprt.
    apply round_le_generic; [now apply fexp_correct | apply valid_rnd_N |].
    unfold Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax.
    unfold SpecFloat.fexp. change (SpecFloat.emin 53 1024) with (-1074)%Z.
    fold (FLT_exp (-1074) 53). apply generic_format_FLT.
    apply (FLT_spec _ _ _ _ (Float radix2 1 53)); [| easy..].
    unfold F2R, scaled_mantissa. simpl Defs.Fnum. simpl Defs.Fexp. now rewrite Rmult_1_l.


(* Very ugly proof *)
- apply andb_prop in IWF. destruct IWF as [IWFt1 IWFt2].
  destruct IWD as [IWDt1 IWDt2].
  destruct IOE as [IOEt1 [IOEt2 BoundedLdexp]].

  destruct (IHt1 lC) as [fint1 B2Rt1], (IHt2 lC); try easy.
  generalize (Bldexp_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t1 lC md) (evalFloat t2 lC md)).
  unfold prec, emax. rewrite Rlt_bool_true.
  { intros [H1 [H2 H3]]. split; unfold FPldexp, prec, emax.
    - now rewrite H2.
    - rewrite H1. now rewrite <-B2Rt1. }
  unfold prec, emax in B2Rt1. rewrite B2Rt1.
  apply Rle_lt_trans with Rrnd.maxval; [| apply Rrnd.maxval_lt].
  destruct BoundedLdexp as [BoundedLdexp_aux1 BoundedLdexp_aux2].
  apply abs_round_le_generic;
   [apply FLT_exp_valid, HPrec_gt_0 | apply valid_rnd_round_mode | |].
  { apply generic_format_FLT.
    now apply (FLT_spec _ _ _ Rrnd.maxval
     (Float radix2 9007199254740991%Z 971%Z)). }

  generalize HPrec_gt_0. intros prec_gt_0.
  generalize (FLT_exp_valid (- 1074) 53). intros valid_exp_FLT.
  destruct (is_finite_strict (evalFloat t1 lC md)) eqn:finst1.
  2: { rewrite <-B2Rt1 in *. destruct (evalFloat t1 lC md) eqn:Ht1; try easy.
    simpl. rewrite Rmult_0_l, Rabs_R0. apply Rmult_le_pos.
    - now apply IZR_le.
    - apply bpow_ge_0. }

  apply le_IZR in BoundedLdexp_aux2.
  apply (bpow_le radix2) in BoundedLdexp_aux2.
  rewrite bpow_plus in BoundedLdexp_aux2.
  apply (Rmult_le_compat_l (9007199254740991 * Rpow2 (- (53)))) in BoundedLdexp_aux2;
   [| apply Rmult_le_pos; [now apply IZR_le | apply bpow_ge_0]].
  rewrite <-Rmult_assoc in BoundedLdexp_aux2.
  rewrite (Rmult_assoc _ _ (Rpow2 z)) in BoundedLdexp_aux2.
  rewrite <-bpow_plus in BoundedLdexp_aux2.
  rewrite Z.add_comm in BoundedLdexp_aux2.
  unfold prec in BoundedLdexp_aux1.
  apply (Rmult_le_compat_r (Rpow2 (evalFloat t2 lC md))) in BoundedLdexp_aux1;
   [| apply bpow_ge_0].
  unfold Rrnd.maxval, Rrnd.prec, Rrnd.emax, Format64.prec, Format64.emax.
  change (1024 - 53)%Z with (- 53 + 1024)%Z.
  rewrite bpow_plus. rewrite <-Rmult_assoc. rewrite Rabs_mult.
  rewrite (Rabs_pos_eq (Rpow2 (evalFloat t2 lC md))); [| apply bpow_ge_0].
  apply
   (Rle_trans
     (Rabs (evalRounded t1 (C2M_list lC) md) * Rpow2 (evalFloat t2 lC md))
     (9007199254740991 * Rpow2 (z - 53) * Rpow2 (evalFloat t2 lC md))
     (9007199254740991 * Rpow2 (-53) * Rpow2 1024)
      BoundedLdexp_aux1
      BoundedLdexp_aux2).


- destruct IWD as [IWD Nonnegt]. destruct T; [now rewrite (IHt lC) |].
  destruct (IHt lC) as [fint B2Rt]; try assumption.
  generalize (Bsqrt_correct _ _ HPrec_gt_0 HPrec_lt_emax md (evalFloat t lC md)).
  unfold prec, emax. intros [H1 [H2 H3]].
  split; unfold FPsqrt, prec, emax; [| now rewrite <-B2Rt].
  destruct evalFloat; [easy.. |]. rewrite <-B2Rt in Nonnegt.
  destruct s eqn:Hs; [| easy]. simpl in Nonnegt.
  unfold F2R, scaled_mantissa in Nonnegt. simpl in Nonnegt.
  rewrite IZR_NEG, <-Ropp_mult_distr_l in Nonnegt.
  assert (IZR (Z.pos m) * Rpow2 e > 0); [| lra].
  apply Rmult_gt_0_compat; [now apply IZR_lt |]. apply bpow_gt_0.


- simpl in IWF. apply andb_prop in IWF.
  destruct IWF as [IWFt1 IWFt2].
  destruct IWD as [IWDt1 IWDt2].
  destruct IOE as [IOEt1 IOEt2].
  destruct T1; simpl in *;
   [now rewrite IHt1; try easy;
    apply IHt2|].
  destruct (IHt1 lC) as [fint1 B2Rt1]; try easy.
  specialize (IHt2 (evalFloat t1 lC md, lC)).
  simpl in IHt2. rewrite B2Rt1 in IHt2.
  now apply IHt2.
Qed.

Theorem evalFloat_evalRounded_full {Tl T} :
  forall (t: ArithExprTree Tl T) (lC : evalExprTypeFloat_list Tl) md,
  is_finite_list lC -> let lM := C2M_list lC in
  fullyCorrect t lM md -> wellFormed t = true -> assertions t lM md ->
    eqExprType (evalFloat t lC md) (evalRounded t lM md) /\ postconditions t lM md.
Proof. intros t lC md HlC.
unfold fullyCorrect.
intros IFC IWF A. apply IFC in A. clear IFC.
destruct A as [IWB IPC].
split; [| assumption]. clear IPC.
now apply evalFloat_evalRounded.
Qed.
