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

From Coq Require Import Reals List ZArith Psatz.
From Flocq Require Import Zaux.
From Coquelicot Require Import Coquelicot.

Require Import Sig.
Require Import Interval_helper.
Require Import Integral_helper.
Require Import Plot_helper.
Require Import Root_helper.
Require Import Float_full.

Inductive interval_tac_parameters : Set :=
  | i_prec (p : positive)
  | i_bisect (v : R)
  | i_autodiff (v : R)
  | i_taylor (v : R)
  | i_degree (d : nat)
  | i_depth (d : nat)
  | i_fuel (f : positive)
  | i_width (w : Z)
  | i_relwidth (w : positive)
  | i_native_compute
  | i_size (w : positive) (h : positive)
  | i_decimal
  | i_delay.

Require Tactic_float.

Module IntervalTactic (F : FloatOps with Definition sensible_format := true with Definition radix := radix2).

Module Private.

Module I1 := FloatIntervalFull F.
Module IT1 := IntegralTacticAux F I1.
Module PT1 := PlotTacticAux F I1.
Module RT1 := RootTacticAux F I1.
Module I2 := Tactic_float.Interval.
Module IT2 := IntegralTacticAux Tactic_float.Float I2.
Module PT2 := PlotTacticAux Tactic_float.Float I2.
Module RT2 := RootTacticAux Tactic_float.Float I2.

Ltac do_interval_parse params depth :=
  let rec aux fvar bvars prec degree depth native nocheck itm output params :=
    lazymatch params with
    | nil => constr:((fvar, bvars, prec, degree, depth, native, nocheck, itm, output))
    | cons (i_prec ?p) ?t => aux fvar bvars (Some p) degree depth native nocheck itm output t
    | cons (i_degree ?d) ?t => aux fvar bvars prec d depth native nocheck itm output t
    | cons (i_bisect ?x) ?t => aux fvar (cons x bvars) prec degree depth native nocheck itm output t
    | cons (i_autodiff ?x) ?t => aux (Some x) bvars prec degree depth native nocheck itm_autodiff output t
    | cons (i_taylor ?x) ?t => aux (Some x) bvars prec degree depth native nocheck itm_taylor output t
    | cons (i_depth ?d) ?t => aux fvar bvars prec degree d native nocheck itm output t
    | cons i_native_compute ?t => aux fvar bvars prec degree depth true nocheck itm output t
    | cons i_delay ?t => aux fvar bvars prec degree depth native true itm output t
    | cons i_decimal ?t => aux fvar bvars prec degree depth native nocheck itm true t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None R) (@nil R) (@None positive) 10%nat depth false false itm_naive false params.

Ltac do_interval params :=
  match do_interval_parse params 15%nat with
  | (?fvar, ?bvars, ?prec, ?degree, ?depth, ?native, ?nocheck, ?itm, _) =>
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      IT1.IH.do_interval fvar bvars prec degree depth native nocheck itm
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      IT2.IH.do_interval fvar bvars prec degree depth native nocheck itm
    end
  end.

Ltac do_interval_intro t extend params :=
  match do_interval_parse params 5%nat with
  | (?fvar, ?bvars, ?prec, ?degree, ?depth, ?native, ?nocheck, ?itm, ?output) =>
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      IT1.IH.do_interval_intro t extend fvar bvars prec degree depth native nocheck itm output
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      IT2.IH.do_interval_intro t extend fvar bvars prec degree depth native nocheck itm output
    end
  end.

Ltac do_integral_parse params :=
  let rec aux prec degree fuel width native nocheck output params :=
    lazymatch params with
    | nil => constr:((prec, degree, fuel, width, native, nocheck, output))
    | cons (i_prec ?p) ?t => aux (Some p) degree fuel width native nocheck output t
    | cons (i_degree ?d) ?t => aux prec d fuel width native nocheck output t
    | cons (i_fuel ?f) ?t => aux prec degree f width native nocheck output t
    | cons (i_width ?w) ?t => aux prec degree fuel (w, false) native nocheck output t
    | cons (i_relwidth ?w) ?t => aux prec degree fuel (Zneg w, true) native nocheck output t
    | cons i_native_compute ?t => aux prec degree fuel width true nocheck output t
    | cons i_delay ?t => aux prec degree fuel width native true output t
    | cons i_decimal ?t => aux prec degree fuel width native nocheck true t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None positive) 10%nat 100%positive (Zneg 10, true) false false false params.

Ltac do_integral params :=
  match do_integral_parse params with
  | (?prec, ?degree, ?fuel, _, ?native, ?nocheck, _) =>
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      IT1.do_integral prec degree fuel native nocheck
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      IT2.do_integral prec degree fuel native nocheck
    end
  end.

Ltac do_integral_intro y extend params :=
  match do_integral_parse params with
  | (?prec, ?degree, ?fuel, ?width, ?native, ?nocheck, ?output) =>
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      IT1.do_integral_intro y extend prec degree fuel width native nocheck output
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      IT2.do_integral_intro y extend prec degree fuel width native nocheck output
    end
  end.

Ltac do_plot_parse params :=
  let rec aux prec degree width height native params :=
    lazymatch params with
    | nil => constr:((prec, degree, width, height, native))
    | cons (i_prec ?p) ?t => aux (Some p) degree width height native t
    | cons (i_degree ?d) ?t => aux prec d width height native t
    | cons (i_size ?w ?h) ?t => aux prec degree w h native t
    | cons i_native_compute ?t => aux prec degree width height true t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None positive) 10%nat 512%positive 384%positive false params.

Ltac do_plot t x1 x2 params :=
  match do_plot_parse params with
  | (?prec, ?degree, ?width, ?height, ?native) =>
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      PT1.do_plot t x1 x2 prec degree width height native
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      PT2.do_plot t x1 x2 prec degree width height native
    end
  end.

Ltac do_plot_y t x1 x2 y1 y2 params :=
  match do_plot_parse params with
  | (?prec, ?degree, ?width, ?height, ?native) =>
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      PT1.do_plot_y t x1 x2 y1 y2 prec degree width height native
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      PT2.do_plot_y t x1 x2 y1 y2 prec degree width height native
    end
  end.

Ltac do_root_parse params :=
  let rec aux fvar prec depth native nocheck output params :=
    lazymatch params with
    | nil => constr:((fvar, prec, depth, native, nocheck, output))
    | cons (i_autodiff ?v) ?t => aux (Some v) prec depth native nocheck output t
    | cons (i_prec ?p) ?t => aux fvar (Some p) depth native nocheck output t
    | cons (i_depth ?d) ?t => aux fvar prec d native nocheck output t
    | cons i_native_compute ?t => aux fvar prec depth true nocheck output t
    | cons i_delay ?t => aux fvar prec depth native true output t
    | cons i_decimal ?t => aux fvar prec depth native nocheck true t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None R) (@None positive) 15%nat false false false params.

Ltac do_root' Zy params :=
  match do_root_parse params with
  | (?fvar, ?prec, ?depth, ?native, ?nocheck, _) =>
    let x :=
      lazymatch fvar with
      | Some ?v => v
      | None => get_root_var Zy
      end in
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      RT1.do_root x Zy prec depth native nocheck
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      RT2.do_root x Zy prec depth native nocheck
    end
  end.

Ltac do_root_intro' Zy params :=
  match do_root_parse params with
  | (?fvar, ?prec, ?depth, ?native, ?nocheck, ?output) =>
    let x :=
      lazymatch fvar with
      | Some ?v => v
      | None => get_root_var Zy
      end in
    lazymatch prec with
    | Some ?p =>
      let prec := eval vm_compute in (F.PtoP p) in
      RT1.do_root_intro x Zy prec depth native nocheck output
    | None =>
      let prec := eval vm_compute in (Tactic_float.Float.PtoP 53) in
      RT2.do_root_intro x Zy prec depth native nocheck output
    end
  end.

Ltac do_root_intro_prop y1 y2 params :=
  eapply (cut_root y1 y2) ; [
    let H := fresh "H" in
    let K := fresh "K" in
    intros K H ;
    lazymatch y2 with
    | 0%R => idtac
    | _ => apply (Rminus_diag_eq y1 y2) in H
    end ;
    do_root_intro' H params ;
    eexact K
  | ].

Ltac do_root_intro Zy params :=
  lazymatch type of Zy with
  | R =>
    do_root_intro_prop Zy 0%R params
  | Prop =>
    lazymatch Zy with
    | ?y1 = ?y2 => do_root_intro_prop y1 y2 params
    end
  | _ = 0%R =>
    do_root_intro' Zy params
  | ?y1 = ?y2 =>
    let H := fresh "H" in
    assert (H := Rminus_diag_eq y1 y2 Zy) ;
    do_root_intro' H params ;
    clear H
  end.

Ltac do_root Zy params :=
  tryif
    match goal with |- ?G => is_evar G end
  then
    let params := constr:(cons i_delay params) in
    let H := fresh "H" in
    lazymatch type of Zy with
    | R =>
      refine (fun H : Zy = 0%R => _) ;
      do_root_intro' H params
    | Prop =>
      refine (fun H : Zy => _) ;
      do_root_intro H params
    | _ = _ =>
      do_root_intro Zy params
    end ;
    exact (fun K => K)
  else
    lazymatch type of Zy with
    | R =>
      cut (Zy = 0%R) ; [
        let H := fresh "H" in
        intros H ;
        do_root' H params
      | ]
    | Prop =>
      cut Zy ; [
        let H := fresh "H" in
        intros H ;
        do_root H params
      | ]
    | _ = 0%R =>
      do_root' Zy params
    | ?y1 = ?y2 =>
      let H := fresh "H" in
      assert (H := Rminus_diag_eq y1 y2 Zy) ;
      do_root' H params
    end.

End Private.

Import Private.

Tactic Notation "interval" :=
  do_interval (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "interval" constr(t) :=
  do_interval_intro t ie_none (cons i_delay nil) ; exact (fun H => H).

Tactic Notation "interval" constr(t) "lower" :=
  do_interval_intro t ie_upper (cons i_delay nil) ; exact (fun H => H).

Tactic Notation "interval" constr(t) "upper"  :=
  do_interval_intro t ie_lower (cons i_delay nil) ; exact (fun H => H).

Tactic Notation "interval" constr(t) "with" constr(params) :=
  do_interval_intro t ie_none ltac:(tuple_to_list params (cons i_delay nil)) ; exact (fun H => H).

Tactic Notation "interval" constr(t) "lower" "with" constr(params) :=
  do_interval_intro t ie_upper ltac:(tuple_to_list params (cons i_delay nil)) ; exact (fun H => H).

Tactic Notation "interval" constr(t) "upper" "with" constr(params) :=
  do_interval_intro t ie_lower ltac:(tuple_to_list params (cons i_delay nil)) ; exact (fun H => H).

Tactic Notation "interval_intro" constr(t) :=
  do_interval_intro t ie_none (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" :=
  do_interval_intro t ie_upper (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "upper"  :=
  do_interval_intro t ie_lower (@nil interval_tac_parameters) ; intro.

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) :=
  do_interval_intro t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) :=
  do_interval_intro t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "interval_intro" constr(t) "as" simple_intropattern(H) :=
  do_interval_intro t ie_none (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_interval_intro t ie_upper (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_interval_intro t ie_lower (@nil interval_tac_parameters) ; intros H.

Tactic Notation "interval_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "interval_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_interval_intro t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral" :=
  do_integral (@nil interval_tac_parameters).

Tactic Notation "integral" "with" constr(params) :=
  do_integral ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "integral" constr(t) :=
  do_integral_intro t ie_none (cons i_delay nil) ; exact (fun H => H).

Tactic Notation "integral" constr(t) "lower" :=
  do_integral_intro t ie_upper (cons i_delay nil) ; exact (fun H => H).

Tactic Notation "integral" constr(t) "upper"  :=
  do_integral_intro t ie_lower (cons i_delay nil) ; exact (fun H => H).

Tactic Notation "integral" constr(t) "with" constr(params) :=
  do_integral_intro t ie_none ltac:(tuple_to_list params (cons i_delay nil)) ; exact (fun H => H).

Tactic Notation "integral" constr(t) "lower" "with" constr(params) :=
  do_integral_intro t ie_upper ltac:(tuple_to_list params (cons i_delay nil)) ; exact (fun H => H).

Tactic Notation "integral" constr(t) "upper" "with" constr(params) :=
  do_integral_intro t ie_lower ltac:(tuple_to_list params (cons i_delay nil)) ; exact (fun H => H).

Tactic Notation "integral_intro" constr(t) :=
  do_integral_intro t ie_none (@nil interval_tac_parameters) ; intro.

Tactic Notation "integral_intro" constr(t) "lower" :=
  do_integral_intro t ie_upper (@nil interval_tac_parameters) ; intro.

Tactic Notation "integral_intro" constr(t) "upper"  :=
  do_integral_intro t ie_lower (@nil interval_tac_parameters) ; intro.

Tactic Notation "integral_intro" constr(t) "with" constr(params) :=
  do_integral_intro t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "integral_intro" constr(t) "lower" "with" constr(params) :=
  do_integral_intro t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "integral_intro" constr(t) "upper" "with" constr(params) :=
  do_integral_intro t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "integral_intro" constr(t) "as" simple_intropattern(H) :=
  do_integral_intro t ie_none (@nil interval_tac_parameters) ; intros H.

Tactic Notation "integral_intro" constr(t) "lower" "as" simple_intropattern(H) :=
  do_integral_intro t ie_upper (@nil interval_tac_parameters) ; intros H.

Tactic Notation "integral_intro" constr(t) "upper" "as" simple_intropattern(H)  :=
  do_integral_intro t ie_lower (@nil interval_tac_parameters) ; intros H.

Tactic Notation "integral_intro" constr(t) "with" constr(params) "as" simple_intropattern(H) :=
  do_integral_intro t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral_intro" constr(t) "lower" "with" constr(params) "as" simple_intropattern(H) :=
  do_integral_intro t ie_upper ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "integral_intro" constr(t) "upper" "with" constr(params) "as" simple_intropattern(H) :=
  do_integral_intro t ie_lower ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

Tactic Notation "plot" constr(t) constr(x1) constr(x2) :=
  do_plot t x1 x2 (@nil interval_tac_parameters).

Tactic Notation "plot" constr(t) constr(x1) constr(x2) "with" constr(params) :=
  do_plot t x1 x2 ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "plot" constr(t) constr(x1) constr(x2) constr(y1) constr(y2) :=
  do_plot_y t x1 x2 y1 y2 (@nil interval_tac_parameters).

Tactic Notation "plot" constr(t) constr(x1) constr(x2) constr(y1) constr(y2) "with" constr(params) :=
  do_plot_y t x1 x2 y1 y2 ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "root" constr(Zy) :=
  do_root Zy (@nil interval_tac_parameters).

Tactic Notation "root" constr(Zy) "with" constr(params) :=
  do_root Zy ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "root_intro" constr(Zy) constr(x) :=
  do_root_intro x Zy (@nil interval_tac_parameters) ; intro.

Tactic Notation "root_intro" constr(Zy) :=
  do_root_intro Zy (@nil interval_tac_parameters) ; intro.

Tactic Notation "root_intro" constr(Zy) "with" constr(params) :=
  do_root_intro Zy ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intro.

Tactic Notation "root_intro" constr(Zy) "as" simple_intropattern(H) :=
  do_root_intro Zy (@nil interval_tac_parameters) ; intros H.

Tactic Notation "root_intro" constr(Zy) "with" constr(params) "as" simple_intropattern(H) :=
  do_root_intro Zy ltac:(tuple_to_list params (@nil interval_tac_parameters)) ; intros H.

End IntervalTactic.

Require Import Specific_bigint.
Require Import Specific_ops.
Module SFBI2 := SpecificFloat BigIntRadix2.
Module IT := IntervalTactic SFBI2.
Export IT.
