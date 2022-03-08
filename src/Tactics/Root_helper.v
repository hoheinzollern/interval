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
Require Import Interval_helper.

Module RootTacticAux (F : FloatOps with Definition radix := Zaux.radix2 with Definition sensible_format := true) (I : IntervalOps with Module F := F).

Module F' := FloatExt F.
Module IH := IntervalTacticAux I.
Import IH.

Definition check_goal prec hyps pg cg g :=
  let bounds := hyps ++ map (T.eval_bnd prec) cg in
  fun b =>
    let yi := nth 0 (A.BndValuator.eval prec pg (b :: bounds)) I.nai in
    R.eval_goal_bnd prec g yi.

Fixpoint refine_root_aux depth prec prog bounds xi (check : I.type -> bool) :=
  match depth with
  | S depth =>
    let xi' := A.DiffValuator.root prec prog bounds xi in
    if check xi' then true
    else
      let (xi1,xi2) := I.bisect xi in
      if I.wider prec xi1 xi' then
        refine_root_aux depth prec prog bounds xi' check
      else if refine_root_aux depth prec prog bounds xi1 check then
        refine_root_aux depth prec prog bounds xi2 check
      else false
  | O => false
  end.

Definition refine_root prec depth hyps px cx pf cf pg cg g :=
  let hyps := R.merge_hyps prec hyps in
  let xi := nth 0 (A.BndValuator.eval prec px (hyps ++ map (T.eval_bnd prec) cx)) I.nai in
  let check := check_goal prec hyps pg cg g in
  refine_root_aux depth prec pf (hyps ++ map (T.eval_bnd prec) cf) xi check.

Theorem refine_root_correct :
  forall prec depth vars hyps px cx pf cf pg cg g,
  refine_root prec depth hyps px cx pf cf pg cg g = true ->
  eval_hyps hyps vars (eval_real' pf (eval_real' px vars cx :: vars) cf = 0%R ->
    eval_goal g (eval_real' pg (eval_real' px vars cx :: vars) cg)).
Proof.
intros prec depth vars hyps px cx pf cf pg cg g H.
apply (R.eval_hyps_bnd_correct prec).
set (x := eval_real' px vars cx).
intros H1 H2.
unfold refine_root in H.
revert H.
set (xi := nth 0 _ _).
assert (Hx: contains (I.convert xi) (Xreal x)).
{ apply A.BndValuator.eval_correct'.
  now apply app_merge_hyps_eval_bnd. }
clearbody xi.
revert xi Hx.
induction depth as [|depth IH].
easy.
intros xi Hx.
simpl.
fold (compute_inputs prec hyps cf).
refine (_ (A.DiffValuator.root_correct prec pf (compute_inputs prec hyps cf) _ _ xi x Hx H2)).
2: now apply app_merge_hyps_eval_bnd.
set (xi' := A.DiffValuator.root _ _ _ _).
intros Hx' H.
destruct check_goal eqn:Hg.
- clear H IH.
  apply (R.eval_goal_bnd_correct prec) with (2 := Hg).
  unfold eval_real'.
  fold (compute_inputs prec hyps cg).
  simpl.
  apply A.BndValuator.eval_correct_ext' with (2 := Hx').
  now apply app_merge_hyps_eval_bnd.
- generalize (I.bisect_correct _ _ Hx).
  destruct (I.bisect xi) as [xi1 xi2].
  destruct I.wider.
  + intros _.
    now apply (IH _ Hx').
  + destruct refine_root_aux eqn:Hb.
    now intros [K|K] ; apply (IH _ K).
    easy.
Qed.

Ltac do_root x Zy prec depth native nocheck :=
  massage_goal ;
  let y :=
    match type of Zy with
    | (?y = 0)%R => y
    | _ => fail "Not an equality to zero"
    end in
  match goal with
  | |- eval_goal ?g' ?z =>
    let g := fresh "__goal" in
    set (g := g') ;
    let vars := get_vars x (@nil R) in
    let vars := get_vars y vars in
    let vars := get_vars z vars in
    let vars' := constr:(x :: vars) in
    reify_partial z vars' ;
    intros <- ;
    revert Zy ;
    reify_partial y vars' ;
    intros <- ;
    let v := fresh "__vars" in
    set (v := vars) ;
    reify_partial x vars ;
    intros <- ;
    find_hyps vars ;
    apply (refine_root_correct prec depth)
  end ;
  do_reduction nocheck native.

End RootTacticAux.
