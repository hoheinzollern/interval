(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: https://coqinterval.gitlabpages.inria.fr/

Copyright (C) 2007-2021, Inria

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

Require Import Stdlib.
Require Import Xreal.
Require Import Basic.
Require Import Sig.
Require Import Interval.
Require Import Eval.
Require Import Tree.
Require Import Prog.
Require Import Reify.

Inductive interval_tac_method : Set :=
  | itm_naive
  | itm_autodiff
  | itm_taylor.

Inductive interval_extent : Set :=
  | ie_none
  | ie_lower
  | ie_upper.

Ltac tuple_to_list params l :=
  match params with
  | pair ?a ?b => tuple_to_list a (b :: l)
  | pair _ ?b => fail 100 "Unknown tactic parameter" b
  | ?b => constr:(b :: l)
  | ?b => fail 100 "Unknown tactic parameter" b
  end.

Ltac do_interval_generalize output :=
  let H := fresh "H" in
  intro H ;
  apply output in H ;
  revert H ;
  match goal with
  | |- contains_output ?b ?t -> ?G =>
    let b' := eval vm_compute in b in
    replace b with b' by (vm_cast_no_check (eq_refl b')) ;
    let o := eval cbv -[IZR Rdiv Rle Q2R] in (contains_output b') in
    let o := eval cbv beta in (o t) in
    lazymatch o with
    | True => fail "Nothing known about" t
    | _ => change (o -> G)
    end
  end.

Ltac do_reduction nocheck native :=
  clear ;
  lazymatch nocheck with
  | true =>
    match native with
    | true => native_cast_no_check (eq_refl true)
    | false => vm_cast_no_check (eq_refl true)
    end
  | false =>
    (abstract
    match native with
    | true => native_cast_no_check (eq_refl true)
    | false => vm_cast_no_check (eq_refl true)
    end) ||
    fail "Numerical evaluation failed to conclude. You may want to adjust some parameters"
  end.

Ltac merge_vars fvar bvars :=
  let rec aux acc l :=
    match l with
    | ?v :: ?l' =>
      let acc := list_add v acc in
      aux acc l'
    | nil => acc
    end in
  lazymatch fvar with
  | Some ?x => aux (cons x nil) bvars
  | None => aux (@nil R) bvars
  end.

Ltac get_var_indices vars bvars :=
  let rec aux1 v i l :=
    lazymatch l with
    | v :: _ => i
    | _ :: ?l' => aux1 v (S i) l'
    end in
  let rec aux2 acc l :=
    lazymatch l with
    | ?v :: ?l' =>
      let i := aux1 v 0%nat vars in
      aux2 (cons i acc) l'
    | nil => acc
    end in
  aux2 (@nil nat) bvars.

Ltac hide_lhs :=
  lazymatch goal with
  | |- ?l = _ =>
    let l' := fresh "l" in
    set (l' := l)
  end.

Module IntervalTacticAux (I : IntervalOps).

Module J := IntervalExt I.
Module A := IntervalAlgos I.
Module T := Tree.Bnd I.
Module R := Reify.Bnd I.

Definition compute_inputs prec hyps consts :=
  R.merge_hyps prec hyps ++ map (T.eval_bnd prec) consts.

Theorem app_merge_hyps_eval_bnd :
  forall prec vars hyps consts,
  R.eval_hyps_bnd (R.merge_hyps prec hyps) vars ->
  A.contains_all (compute_inputs prec hyps consts) (vars ++ map (fun c => eval c nil) consts).
Proof.
intros prec vars hyps consts He.
unfold compute_inputs.
revert vars He.
induction (R.merge_hyps prec hyps) as [|h t IH].
  intros [|vars]. 2: easy.
  intros _.
  simpl.
  split.
    now rewrite 2!map_length.
  intros n.
  rewrite (nth_map (Evar 0)).
  destruct le_lt_dec as [H|H].
    now rewrite I.nai_correct.
  rewrite (nth_map_lt (Evar 0)) by easy.
  apply T.eval_bnd_correct.
intros [|v vars].
  easy.
simpl.
intros [H1 H2].
apply A.contains_all_cons with (2 := H1).
now apply IH.
Qed.

Theorem eval_bisect_aux :
  forall prec depth idx vars hyps prog consts g fi,
  ( forall xi x, A.contains_all xi x ->
    contains (I.convert (fi xi)) (Xreal (nth 0 (eval_real prog x) 0%R)) ) ->
  A.bisect (compute_inputs prec hyps consts) idx (fun xi => R.eval_goal_bnd prec g (fi xi)) depth = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec depth idx vars hyps prog consts g fi Hfi H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_correct with (P := fun x => eval_goal g (nth 0 (eval_real prog x) 0%R)) (2 := H).
- intros x xi Ix.
  apply (R.eval_goal_bnd_correct prec).
  now apply Hfi.
- now apply app_merge_hyps_eval_bnd.
Qed.

Theorem eval_bisect_contains_aux :
  forall prec depth idx vars hyps prog consts b fi,
  ( forall xi x, A.contains_all xi x ->
    contains (I.convert (fi xi)) (Xreal (nth 0 (eval_real prog x) 0%R)) ) ->
  A.bisect (compute_inputs prec hyps consts) idx (fun xi => I.subset (fi xi) b) depth = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth idx vars hyps prog consts b fi Hfi H.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.bisect_correct with (P := fun x => contains (I.convert b) (Xreal (nth 0 (eval_real prog x) 0%R))) (2 := H).
- intros x xi Ix H''.
  apply I.subset_correct with (2 := H'').
  now apply Hfi.
- now apply app_merge_hyps_eval_bnd.
Qed.

Theorem eval_lookup_contains_aux :
  forall prec depth extend idx vars hyps prog consts fi,
  ( forall xi x, A.contains_all xi x ->
    contains (I.convert (fi xi)) (Xreal (nth 0 (eval_real prog x) 0%R)) ) ->
  let b := A.lookup fi (compute_inputs prec hyps consts) idx extend depth in
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth extend idx vars hyps prog consts fi Hfi.
apply (R.eval_hyps_bnd_correct prec).
intros H'.
apply A.lookup_correct with (1 := Hfi).
now apply app_merge_hyps_eval_bnd.
Qed.

Definition eval_bisect_fun prec prog xi :=
  nth 0 (A.BndValuator.eval prec prog xi) I.nai.

Definition eval_bisect prec depth idx hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  let check := R.eval_goal_bnd prec g in
  A.bisect bounds idx (fun xi => check (eval_bisect_fun prec prog xi)) depth.

Theorem eval_bisect_correct :
  forall prec depth idx vars hyps prog consts g,
  eval_bisect prec depth idx hyps prog consts g = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec depth idx vars hyps prog consts g H.
apply eval_bisect_aux with (2 := H).
intros xi x Ix.
now apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bisect_contains prec depth idx hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => I.subset (eval_bisect_fun prec prog xi) b) depth.

Theorem eval_bisect_contains_correct :
  forall prec depth idx vars hyps prog consts b,
  eval_bisect_contains prec depth idx hyps prog consts b = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth idx vars hyps prog consts b H.
apply eval_bisect_contains_aux with (2 := H).
intros xi x Ix.
now apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bisect_plain prec depth extend idx hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  A.lookup (eval_bisect_fun prec prog) bounds idx extend depth.

Theorem eval_bisect_plain_correct :
  forall prec depth extend idx vars hyps prog consts,
  let b := eval_bisect_plain prec depth extend idx hyps prog consts in
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth extend idx vars hyps prog consts.
apply eval_lookup_contains_aux.
intros xi x Ix.
now apply A.BndValuator.eval_correct'.
Qed.

Definition eval_bisect_diff_fun prec prog xi :=
  match xi with
  | nil => I.nai
  | xi :: li => A.DiffValuator.eval prec prog li 0 xi
  end.

Definition eval_bisect_diff prec depth idx hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  let check := R.eval_goal_bnd prec g in
  A.bisect bounds idx (fun xi => check (eval_bisect_diff_fun prec prog xi)) depth.

Theorem eval_bisect_diff_correct :
  forall prec depth idx vars hyps prog consts g,
  eval_bisect_diff prec depth idx hyps prog consts g = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec depth idx vars hyps prog consts g H.
apply eval_bisect_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  apply J.nai_correct.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.DiffValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_contains_diff prec depth idx hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => I.subset (eval_bisect_diff_fun prec prog xi) b) depth.

Theorem eval_bisect_contains_diff_correct :
  forall prec depth idx vars hyps prog consts b,
  eval_bisect_contains_diff prec depth idx hyps prog consts b = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth idx vars hyps prog consts b H.
apply eval_bisect_contains_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  apply J.nai_correct.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.DiffValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_diff_plain prec depth extend idx hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  A.lookup (eval_bisect_diff_fun prec prog) bounds idx extend depth.

Theorem eval_bisect_diff_plain_correct :
  forall prec depth extend idx vars hyps prog consts,
  let b := eval_bisect_diff_plain prec depth extend idx hyps prog consts in
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec depth extend idx vars hyps prog consts.
apply eval_lookup_contains_aux.
intros xi x Ix.
destruct xi as [|xi li].
  apply J.nai_correct.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.DiffValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_taylor_fun prec deg prog xi :=
  match xi with
  | nil => I.nai
  | xi :: li =>
    let li := A.TaylorValuator.TM.var :: map A.TaylorValuator.TM.const li in
    A.TaylorValuator.TM.eval (prec, deg)
      (nth 0 (A.TaylorValuator.eval prec deg xi prog li) A.TaylorValuator.TM.dummy) xi xi
  end.

Definition eval_bisect_taylor prec deg depth idx hyps prog consts g :=
  let bounds := compute_inputs prec hyps consts in
  let check := R.eval_goal_bnd prec g in
  A.bisect bounds idx (fun xi => check (eval_bisect_taylor_fun prec deg prog xi)) depth.

Theorem eval_bisect_taylor_correct :
  forall prec deg depth idx vars hyps prog consts g,
  eval_bisect_taylor prec deg depth idx hyps prog consts g = true ->
  eval_hyps hyps vars (eval_goal g (eval_real' prog vars consts)).
Proof.
intros prec deg depth idx vars hyps prog consts g H.
apply eval_bisect_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  apply J.nai_correct.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.TaylorValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_contains_taylor prec deg depth idx hyps prog consts b :=
  let bounds := compute_inputs prec hyps consts in
  A.bisect bounds idx (fun xi => I.subset (eval_bisect_taylor_fun prec deg prog xi) b) depth.

Theorem eval_bisect_contains_taylor_correct :
  forall prec deg depth idx vars hyps prog consts b,
  eval_bisect_contains_taylor prec deg depth idx hyps prog consts b = true ->
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec deg depth idx vars hyps prog consts b H.
apply eval_bisect_contains_aux with (2 := H).
intros xi x Ix.
destruct xi as [|xi li].
  apply J.nai_correct.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.TaylorValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition eval_bisect_taylor_plain prec deg depth extend idx hyps prog consts :=
  let bounds := compute_inputs prec hyps consts in
  A.lookup (eval_bisect_taylor_fun prec deg prog) bounds idx extend depth.

Theorem eval_bisect_taylor_plain_correct :
  forall prec deg depth extend idx vars hyps prog consts,
  let b := eval_bisect_taylor_plain prec deg depth extend idx hyps prog consts in
  eval_hyps hyps vars (contains (I.convert b) (Xreal (eval_real' prog vars consts))).
Proof.
intros prec deg depth extend idx vars hyps prog consts.
apply eval_lookup_contains_aux.
intros xi x Ix.
destruct xi as [|xi li].
  apply J.nai_correct.
destruct Ix as [H1 H2].
destruct x as [|x l].
  easy.
apply A.TaylorValuator.eval_correct.
split.
  now injection H1.
intros n.
apply (H2 (S n)).
apply (H2 O).
Qed.

Definition extent e :=
  match e with
  | ie_none => fun v => v
  | ie_lower => I.lower_extent
  | ie_upper => I.upper_extent
  end.

Ltac do_interval fvar bvars prec degree depth native nocheck eval_tac :=
  let vars := merge_vars fvar bvars in
  let idx := get_var_indices vars bvars in
  massage_goal ;
  reify_full vars ;
  lazymatch eval_tac with
  | itm_naive => apply (eval_bisect_correct prec depth idx)
  | itm_autodiff => apply (eval_bisect_diff_correct prec depth idx)
  | itm_taylor => apply (eval_bisect_taylor_correct prec degree depth idx)
  end ;
  do_reduction nocheck native.

Ltac do_instantiate i extend native yi :=
  let yi :=
    lazymatch native with
    | true => eval native_compute in (extend yi)
    | false => eval vm_compute in (extend yi)
    end in
  instantiate (i := yi).

Ltac do_interval_intro y extend fvar bvars prec degree depth native nocheck eval_tac output :=
  let extend := constr:(extent extend) in
  let vars := merge_vars fvar bvars in
  let idx := get_var_indices vars bvars in
  let i := fresh "__i" in
  evar (i : I.type) ;
  cut (contains (I.convert i) (Xreal y)) ; cycle 1 ; [
    let vars := get_vars y vars in
    reify_partial y vars ;
    apply (eq_ind _ (fun z => contains (I.convert i) (Xreal z))) ;
    find_hyps vars ;
    lazymatch goal with
    | |- eval_hyps ?hyps ?vars (contains _ (Xreal (eval_real' ?prog _ ?consts))) =>
      lazymatch eval_tac with
      | itm_naive =>
        apply (eval_bisect_contains_correct prec depth idx vars hyps prog consts) ;
        do_instantiate i extend native (eval_bisect_plain prec depth extend idx hyps prog consts)
      | itm_autodiff =>
        apply (eval_bisect_contains_diff_correct prec depth idx vars hyps prog consts) ;
        do_instantiate i extend native (eval_bisect_diff_plain prec depth extend idx hyps prog consts)
      | itm_taylor =>
        apply (eval_bisect_contains_taylor_correct prec degree depth idx vars hyps prog consts) ;
        do_instantiate i extend native (eval_bisect_taylor_plain prec degree depth extend idx hyps prog consts)
      end
    end ;
    do_reduction nocheck native
  | unfold i ; clear i ;
    do_interval_generalize (I.output_correct output) ].

Module SimpleTactic.

Inductive interval_tac_parameters : Set :=
  | i_prec (p : positive)
  | i_bisect (v : R)
  | i_autodiff (v : R)
  | i_taylor (v : R)
  | i_degree (d : nat)
  | i_depth (d : nat).

Ltac do_interval_parse params depth :=
  let rec aux fvar bvars prec degree depth itm params :=
    lazymatch params with
    | nil => constr:((fvar, bvars, prec, degree, depth, itm))
    | cons (i_prec ?p) ?t => aux fvar bvars p degree depth itm t
    | cons (i_degree ?d) ?t => aux fvar bvars prec d depth itm t
    | cons (i_bisect ?x) ?t => aux fvar (cons x bvars) prec degree depth itm t
    | cons (i_autodiff ?x) ?t => aux (Some x) bvars prec degree depth itm_autodiff t
    | cons (i_taylor ?x) ?t => aux (Some x) bvars prec degree depth itm_taylor t
    | cons (i_depth ?d) ?t => aux fvar bvars prec degree d itm t
    | cons ?h _ => fail 100 "Unknown tactic parameter" h
    end in
  aux (@None R) (@nil R) 53%positive 10%nat depth itm_naive params.

Ltac do_interval_ params :=
  match do_interval_parse params 15%nat with
  | (?fvar, ?bvars, ?prec, ?degree, ?depth, ?itm) =>
    let prec := eval vm_compute in (I.F.PtoP prec) in
    do_interval fvar bvars prec degree depth false false itm
  end.

Ltac do_interval_intro_ t extend params :=
  match do_interval_parse params 5%nat with
  | (?fvar, ?bvars, ?prec, ?degree, ?depth, ?itm) =>
    let prec := eval vm_compute in (I.F.PtoP prec) in
    do_interval_intro t extend fvar bvars prec degree depth false false itm false
  end.

Tactic Notation "interval" :=
  do_interval_ (@nil interval_tac_parameters).

Tactic Notation "interval" "with" constr(params) :=
  do_interval_ ltac:(tuple_to_list params (@nil interval_tac_parameters)).

Tactic Notation "interval_intro" constr(t) "with" constr(params) :=
  do_interval_intro_ t ie_none ltac:(tuple_to_list params (@nil interval_tac_parameters)).

End SimpleTactic.

End IntervalTacticAux.
