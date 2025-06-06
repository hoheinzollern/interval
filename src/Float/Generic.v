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

From Coq Require Import Reals Bool ZArith.
From Flocq Require Import Zaux Raux Div Sqrt.

Require Import Xreal.
Require Import Basic.

Inductive position : Set :=
  pos_Eq | pos_Lo | pos_Mi | pos_Up.

Inductive ufloat (beta : radix) : Set :=
  | Unan : ufloat beta
  | Uzero : ufloat beta
  | Ufloat : bool -> positive -> Z -> position -> ufloat beta.

Arguments Unan {beta}.
Arguments Uzero {beta}.
Arguments Ufloat {beta} _ _ _ _.

(*
 * Fneg
 *)

Definition Fneg {beta} (f : float beta) :=
  match f with
  | Float s m e => Float (negb s) m e
  | _ => f
  end.

(*
 * Fabs
 *)

Definition Fabs {beta} (f : float beta) :=
  match f with
  | Float s m e => Float false m e
  | _ => f
  end.

(*
 * Fscale
 *)

Definition Fscale {beta} (f : float beta) d :=
  match f with
  | Float s m e => Float s m (e + d)
  | _ => f
  end.

(*
 * Fscale2
 *)

Definition Fscale2 {beta} (f : float beta) d :=
  match f with
  | Float s m e =>
    match radix_val beta, d with
    | Zpos (xO xH), _ => Float s m (e + d)
    | _, Z0 => f
    | _, Zpos nb =>
      Float s (iter_pos (fun x => xO x) nb m) e
    | Zpos (xO r), Zneg nb =>
      Float s (iter_pos (fun x => Pmult r x) nb m) (e + d)
    | _, _ => Fnan
    end
  | _ => f
  end.

(*
 * Fpow2
 *)

Definition Fpow2 {beta} d := Fscale2 (@Float beta false xH 0) d.

(*
 * Fdiv2
 *)

Definition Fdiv2 {beta} (f : float beta) := Fscale2 f (-1).

(*
 * Fcmp
 *
 * 1. Compare signs.
 * 2. Compare position of most significant digits.
 * 3. Compare shifted mantissas.
 *)

Definition shift beta m nb :=
  let r := match radix_val beta with Zpos r => r | _ => xH end in
  iter_pos (Pmult r) nb m.

Definition Fcmp_aux1 m1 m2 :=
  match Z.compare (Zpos m1) (Zpos m2) with
  | Eq => Xeq
  | Lt => Xlt
  | Gt => Xgt
  end.

Definition Fcmp_aux2 beta m1 e1 m2 e2 :=
  let d1 := count_digits beta m1 in
  let d2 := count_digits beta m2 in
  match Z.compare (e1 + Zpos d1)%Z (e2 + Zpos d2)%Z with
  | Lt => Xlt
  | Gt => Xgt
  | Eq =>
    match Zminus e1 e2 with
    | Zpos nb => Fcmp_aux1 (shift beta m1 nb) m2
    | Zneg nb => Fcmp_aux1 m1 (shift beta m2 nb)
    | Z0 => Fcmp_aux1 m1 m2
    end
  end.

Definition Fcmp {beta} (f1 f2 : float beta) :=
  match f1, f2 with
  | Fnan, _ => Xund
  | _, Fnan => Xund
  | Fzero, Fzero => Xeq
  | Fzero, Float false _ _ => Xlt
  | Fzero, Float true _ _ => Xgt
  | Float false _ _, Fzero => Xgt
  | Float true _ _, Fzero => Xlt
  | Float false _ _, Float true _ _ => Xgt
  | Float true _ _, Float false _ _ => Xlt
  | Float false m1 e1, Float false m2 e2 => Fcmp_aux2 beta m1 e1 m2 e2
  | Float true m1 e1, Float true m2 e2 => Fcmp_aux2 beta m2 e2 m1 e1
  end.

(*
 * Fmin
 *)

Definition Fmin {beta} (f1 f2 : float beta) :=
  match Fcmp f1 f2 with
  | Xlt => f1
  | Xeq => f1
  | Xgt => f2
  | Xund => Fnan
  end.

(*
 * Fmax
 *)

Definition Fmax {beta} (f1 f2 : float beta) :=
  match Fcmp f1 f2 with
  | Xlt => f2
  | Xeq => f2
  | Xgt => f1
  | Xund => Fnan
  end.

Definition UtoX {beta} (f : ufloat beta) :=
  match f with
  | Uzero => Xreal R0
  | Ufloat s m e pos_Eq => Xreal (FtoR beta s m e)
  | _ => Xnan
  end.

Definition convert_location l :=
  match l with
  | Bracket.loc_Exact => pos_Eq
  | Bracket.loc_Inexact l =>
    match l with Lt => pos_Lo | Eq => pos_Mi | Gt => pos_Up end
  end.

Definition float_to_ufloat {beta} (x : float beta) : ufloat beta :=
  match x with
  | Fnan => Unan
  | Fzero => Uzero
  | Float s m e => Ufloat s m e pos_Eq
  end.

Definition adjust_pos r d pos :=
  match r with
  | Z0 =>
    match pos with
    | pos_Eq => pos_Eq
    | _ => match d with xH => pos | _ => pos_Lo end
    end
  | Zneg _ => pos_Eq (* dummy *)
  | Zpos _ =>
    let (hd, mid) :=
      match d with
      | xO p => (p, match pos with pos_Eq => pos_Mi | _ => pos_Up end)
      | xI p => (p, match pos with pos_Eq => pos_Lo | _ => pos end)
      | xH => (xH, pos_Eq) (* dummy *)
      end in
    match Z.compare r (Zpos hd) with
    | Lt => pos_Lo
    | Eq => mid
    | Gt => pos_Up
    end
  end.

(*
 * Fround_none
 *)

Definition Fround_none {beta} (uf : ufloat beta) : float beta :=
  match uf with
  | Uzero => Fzero
  | Ufloat s m e pos_Eq => Float s m e
  | _ => Fnan
  end.

(*
 * Fround_at_prec
 *
 * Assume that the position is at exponent ex and that it is pos_Eq if mx is too short.
 *)

Definition need_change mode even_m pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi => negb even_m
    | _ => false
    end
  end.

Definition need_change_radix even_r mode (even_m : bool) pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | pos_Mi => if even_m then false else negb even_r
    | _ => false
    end
  end.

Definition adjust_mantissa mode m pos sign :=
  if need_change mode (match m with xO _ => true | _ => false end) pos sign then Pos.succ m else m.

Definition Fround_at_prec {beta} mode prec (uf : ufloat beta) : float beta :=
  match uf with
  | Unan => Fnan
  | Uzero => Fzero
  | Ufloat sign m1 e1 pos =>
    match (Zpos (count_digits beta m1) - Zpos prec)%Z with
    | Zpos nb =>
      let d := shift beta xH nb in
      match Z.div_eucl (Zpos m1) (Zpos d) with
      | (Zpos m2, r) =>
        let pos2 := adjust_pos r d pos in
        let e2 := (e1 + Zpos nb)%Z in
        Float sign (adjust_mantissa mode m2 pos2 sign) e2
      | _ => Fnan (* dummy *)
      end
    | Z0 => Float sign (adjust_mantissa mode m1 pos sign) e1
    | _ => Float sign m1 e1
    end
  end.

(*
 * Fround_at_exp
 *)

Definition need_change_zero mode pos sign :=
  match mode with
  | rnd_ZR => false
  | rnd_UP => match pos with pos_Eq => false | _ => negb sign end
  | rnd_DN => match pos with pos_Eq => false | _ => sign end
  | rnd_NE =>
    match pos with
    | pos_Up => true
    | _ => false
    end
  end.

Definition Fround_at_exp {beta} mode e2 (uf : ufloat beta) : float beta :=
  match uf with
  | Unan => Fnan
  | Uzero => Fzero
  | Ufloat sign m1 e1 pos =>
    match (e2 - e1)%Z with
    | Zpos nb =>
      match Z.compare (Zpos (count_digits beta m1)) (Zpos nb) with
      | Gt =>
        let d := shift beta xH nb in
        match Z.div_eucl (Zpos m1) (Zpos d) with
        | (Zpos m2, r) =>
          let pos2 := adjust_pos r d pos in
          Float sign (adjust_mantissa mode m2 pos2 sign) e2
        | _ => Fnan (* dummy *)
        end
      | Eq =>
        let d := shift beta xH nb in
        let pos2 := adjust_pos (Zpos m1) d pos in
        if need_change_zero mode pos2 sign then
          Float sign xH e2
        else Fzero
      | Lt =>
        if need_change_zero mode pos_Lo sign then
          Float sign xH e2
        else Fzero
      end
    | Z0 => Float sign (adjust_mantissa mode m1 pos sign) e1
    | _ => Float sign m1 e1
    end
  end.

(*
 * Fround
 *)

Definition Fround {beta} mode prec (x : float beta) :=
  Fround_at_prec mode prec (float_to_ufloat x).

(*
 * Fnearbyint_exact
 *)

Definition Fnearbyint_exact {beta} mode (x : float beta) :=
  Fround_at_exp mode 0 (float_to_ufloat x).

(*
 * Fnearbyint
 *)

Definition Fnearbyint {beta} mode prec x :=
  match x with
  | Float sx mx ex =>
    match Z.compare (Zpos (count_digits beta mx) + ex) (Zpos prec) with
    | Gt => Fround_at_prec mode prec
    | _ => Fround_at_exp mode 0
    end (@Ufloat beta sx mx ex pos_Eq)
  | _ => x
  end.

(*
 * Fmul
 *)

Definition Fmul_aux {beta} (x y : float beta) : ufloat beta :=
  match x, y with
  | Fnan, _ => Unan
  | _, Fnan => Unan
  | Fzero, _ => Uzero
  | _, Fzero => Uzero
  | Float sx mx ex, Float sy my ey =>
    Ufloat (xorb sx sy) (Pmult mx my) (ex + ey) pos_Eq
  end.

Definition Fmul {beta} mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fmul_aux x y).

(*
 * Fadd_slow, Fadd_exact
 *
 * 1. Shift the mantissa with the highest exponent to match the other one.
 * 2. Perform the addition/subtraction.
 * 3. Round to p digits.
 *
 * Complexity is fine as long as px <= p and py <= p and exponents are close.
 *)

Definition Fadd_slow_aux1 beta sx sy mx my e pos : ufloat beta :=
  if eqb sx sy then
    Ufloat sx (Pplus mx my) e pos
  else
    match (Zpos mx + Zneg my)%Z with
    | Z0 => Uzero
    | Zpos p => Ufloat sx p e pos
    | Zneg p => Ufloat sy p e pos
    end.

Definition Fadd_slow_aux2 beta sx sy mx my ex ey pos :=
  match Zminus ex ey with
  | Zpos nb => Fadd_slow_aux1 beta sx sy (shift beta mx nb) my ey pos
  | Zneg nb => Fadd_slow_aux1 beta sx sy mx (shift beta my nb) ex pos
  | Z0 => Fadd_slow_aux1 beta sx sy mx my ex pos
  end.

Definition Fadd_slow_aux {beta} (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan
  | _, Fnan => Unan
  | Fzero, Fzero => Uzero
  | Fzero, Float sy my ey =>
    Ufloat sy my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_slow_aux2 beta sx sy mx my ex ey pos_Eq
  end.

Definition Fadd_slow {beta} mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fadd_slow_aux x y).

Definition Fadd_exact {beta} (x y : float beta) :=
  Fround_none (Fadd_slow_aux x y).

(*
 * Fadd_fast
 *
 * 1. Guess a lower bound on the exponent of the result.
 * 2. Truncate the mantissa (at most one) that extends farther.
 * 3. Shift the (usually other) mantissa to match it.
 * 4. Perform the addition/subtraction.
 * 5. Round to p digits wrt the position given by the truncation.
 *
 * Complexity is fine as long as, either
 *  . px <= p and py <= p, or
 *  . pv <= p and v has same magnitude than the result.
 *)

Definition Fadd_fast_aux1 beta s1 s2 m1 m2 e1 e2 e : ufloat beta :=
  let m1' :=
    match (e1 - e)%Z with
    | Zpos d => shift beta m1 d
    | _ => m1
    end in
  match (e - e2)%Z with
  | Zpos nb =>
    let d := shift beta xH nb in
    match Z.div_eucl (Zpos m2) (Zpos d) with
    | (Zpos m2', r) =>
      let pos := adjust_pos r d pos_Eq in
      Fadd_slow_aux1 beta s1 s2 m1' m2' e pos
    | (Z0, r) =>
      let pos := adjust_pos r d pos_Eq in
      Ufloat s1 m1' e pos
    | _ =>
      Unan (* dummy *)
    end
  | Z0 =>
    Fadd_slow_aux1 beta s1 s2 m1' m2 e pos_Eq
  | _ =>
    Unan (* dummy *)
  end.

Definition Fadd_fast_aux2 beta prec s1 s2 m1 m2 e1 e2 :=
  let d1 := count_digits beta m1 in
  let d2 := count_digits beta m2 in
  let p1 := (Zpos d1 + e1)%Z in
  let p2 := (Zpos d2 + e2)%Z in
  if Zle_bool 2 (Z.abs (p1 - p2)) then
    let e := Z.min (Z.max e1 e2) (Z.max p1 p2 + Z.neg prec) in
    if Zlt_bool e1 e then
      Fadd_fast_aux1 beta s2 s1 m2 m1 e2 e1 e
    else
      Fadd_fast_aux1 beta s1 s2 m1 m2 e1 e2 e
  else
    (* massive cancellation possible *)
    Fadd_slow_aux2 beta s1 s2 m1 m2 e1 e2 pos_Eq.

Definition Fadd_fast_aux {beta} prec (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan
  | _, Fnan => Unan
  | Fzero, Fzero => Uzero
  | Fzero, Float sy my ey =>
    Ufloat sy my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_fast_aux2 beta prec sx sy mx my ex ey
  end.

Definition Fadd_fast {beta} mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fadd_fast_aux prec x y).

Definition Fadd {beta} := @Fadd_slow beta.

(*
 * Fsub
 *)

Definition Fsub_slow_aux {beta} (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan
  | _, Fnan => Unan
  | Fzero, Fzero => Uzero
  | Fzero, Float sy my ey => Ufloat (negb sy) my ey pos_Eq
  | Float sx mx ex, Fzero => Ufloat sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_slow_aux2 beta sx (negb sy) mx my ex ey pos_Eq
  end.

Definition Fsub_slow {beta} mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fsub_slow_aux x y).

Definition Fsub_fast_aux {beta} prec (x y : float beta) :=
  match x, y with
  | Fnan, _ => Unan
  | _, Fnan => Unan
  | Fzero, Fzero => Uzero
  | Fzero, Float sy my ey =>
    Ufloat (negb sy) my ey pos_Eq
  | Float sx mx ex, Fzero =>
    Ufloat sx mx ex pos_Eq
  | Float sx mx ex, Float sy my ey =>
    Fadd_fast_aux2 beta prec sx (negb sy) mx my ex ey
  end.

Definition Fsub_fast {beta} mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fsub_fast_aux prec x y).

Definition Fsub {beta} := @Fsub_slow beta.

(*
 * Fdiv
 *
 * 1. Shift dividend mantissa so that it has at least py + p digits.
 * 2. Perform the euclidean division.
 * 3. Compute position with remainder.
 * 4. Round to p digits.
 *
 * Complexity is fine as long as px <= 2p and py <= p.
 *)

Definition Fdiv_aux2 beta prec m1 e1 m2 e2 :=
  let d1 := Digits.Zdigits beta m1 in
  let d2 := Digits.Zdigits beta m2 in
  let e := (e1 - e2)%Z in
  let (m, e') :=
    match (d2 + prec - d1)%Z with
    | Zpos p => (m1 * Zpower_pos beta p, e + Zneg p)%Z
    | _ => (m1, e)
    end in
  let '(q, r) :=  Zfast_div_eucl m m2 in
  (q, e', Bracket.new_location m2 r Bracket.loc_Exact).

Definition Fdiv_aux {beta} prec (x y : float beta) : ufloat beta :=
  match x, y with
  | Fnan, _ => Unan
  | _, Fnan => Unan
  | _, Fzero => Unan
  | Fzero, _ => Uzero
  | Float sx mx ex, Float sy my ey =>
    match Fdiv_aux2 beta (Zpos prec) (Zpos mx) ex (Zpos my) ey with
    | (Zpos m, e, l) =>
      Ufloat (xorb sx sy) m e (convert_location l)
    | _ => Unan (* dummy *)
    end
  end.

Definition Fdiv {beta} mode prec (x y : float beta) :=
  Fround_at_prec mode prec (Fdiv_aux prec x y).

(*
 * Frem
 *
 * 1. Shift mantissas so that dividend and divisor have the same exponents.
 * 2. Perform the euclidean division.
 * 3. Adjust quotient to closest integer (tie breaking to even).
 * 4. Scale remainder to common exponent.
 * 5. Round remainder to p digits.
 *)

Definition Frem_aux1 beta mx my s e : float beta * ufloat beta :=
  let (q1, r1) := Z.div_eucl (Zpos mx) (Zpos my) in
  let (q2, r2) :=
    match
      match my with
      | xH => false
      | xO p =>
        match Z.compare r1 (Zpos p) with
        | Lt => false
        | Eq =>
          match q1 with
          | Z0 => false
          | Zpos (xO _) => false
          | _ => true
          end
        | Gt => true
        end
      | xI p =>
        match Z.compare r1 (Zpos p) with
        | Lt => false
        | Eq => false
        | Gt => true
        end
      end
    with
    | false => (q1, r1)
    | true => (q1 + 1, r1 - Zpos my)%Z
    end in
 (match q2 with
  | Zpos p => Float s p 0
  | Z0 => Fzero
  | _ => Fnan (* dummy *)
  end,
  match r2 with
  | Zpos p => Ufloat s p e pos_Eq
  | Z0 => Uzero
  | Zneg p => Ufloat (negb s) p e pos_Eq
  end).

Definition Frem_aux {beta} (x y : float beta) :=
  match x, y with
  | Fnan, _ => (Fnan, Unan)
  | _, Fnan => (Fnan, Unan)
  | _, Fzero => (Fnan, Unan)
  | Fzero, _ => (Fzero, Uzero)
  | Float sx mx ex, Float sy my ey =>
    let s := xorb sx sy in
    match (ex - ey)%Z with
    | Zpos nb => Frem_aux1 beta (shift beta mx nb) my s ey
    | Z0 => Frem_aux1 beta mx my s ex
    | Zneg nb => Frem_aux1 beta mx (shift beta my nb) s ex
    end
  end.

Definition Frem {beta} mode prec (x y : float beta) :=
  let (q, r) := Frem_aux x y in
  (q, Fround_at_prec mode prec r).

(*
 * Fsqrt
 *
 * 1. Shift the mantissa so that it has at least 2p-1 digits;
 *    shift it one digit more if the new exponent is not even.
 * 2. Compute the square root s (at least p digits) of the new
 *    mantissa, and its remainder r.
 * 3. Current position: r == 0  =>  Eq,
 *                      r <= s  =>  Lo,
 *                      r >= s  =>  Up.
 * 4. Round to p digits.
 *
 * Complexity is fine as long as p1 <= 2p-1.
 *)

Definition Fsqrt_aux2 beta prec m e :=
  let d := Digits.Zdigits beta m in
  let s := Z.max (2 * prec - d) 0 in
  let e' := (e - s)%Z in
  let (s', e'') := if Z.even e' then (s, e') else (s + 1, e' - 1)%Z in
  let m' :=
    match s' with
    | Zpos p => (m * Zpower_pos beta p)%Z
    | _ => m
    end in
  let (q, r) := Z.sqrtrem m' in
  let l :=
    if Zeq_bool r 0 then Bracket.loc_Exact
    else Bracket.loc_Inexact (if Zle_bool r q then Lt else Gt) in
  (q, Z.div2 e'', l).

Definition Fsqrt_aux {beta} prec (f : float beta) : ufloat beta :=
  match f with
  | Float false m e =>
    match Fsqrt_aux2 beta (Zpos prec) (Zpos m) e with
    | (Zpos m, e, l) =>
      Ufloat false m e (convert_location l)
    | _ => Unan (* dummy *)
    end
  | Float true _ _ => Unan
  | Fzero => Uzero
  | Fnan => Unan
  end.

Definition Fsqrt {beta} mode prec (x : float beta) :=
  Fround_at_prec mode prec (Fsqrt_aux prec x).

(*
 * Fmag
 *)

Definition Fmag {beta} (x : float beta) :=
  match x with
  | Float _ m e => Zplus e (Zpos (count_digits beta m))
  | _ => Z0
  end.
