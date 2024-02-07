(**
This file is part of the Coq.Interval library for proving bounds of
real-valued expressions in Coq: https://coqinterval.gitlabpages.inria.fr/

Copyright (C) 2007-2019, Inria

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

From Coq Require Import ZArith Reals List Psatz.

Require Import Xreal.
Require Import Tree.

Inductive term : Set :=
  | Forward : nat -> term
  | Unary : unary_op -> nat -> term
  | Binary : binary_op -> nat -> nat -> term.

Set Implicit Arguments.

Record operations (A : Type) : Type :=
  { constant : Z -> A
  ; unknown : A
  ; unary : unary_op -> A -> A
  ; binary : binary_op -> A -> A -> A
  ; sign : A -> Xcomparison }.

Unset Implicit Arguments.

Definition eval_generic_body {A} (ops : operations A) values op :=
  let nth n := nth n values (unknown ops) in
  match op with
  | Forward u => nth u
  | Unary o u => unary ops o (nth u)
  | Binary o u v => binary ops o (nth u) (nth v)
  end :: values.

Definition eval_generic {A} (ops : operations A) :=
  fold_left (eval_generic_body ops).

Lemma rev_formula :
  forall A formula terms (ops : operations A),
  eval_generic ops formula terms =
  fold_right (fun y x => eval_generic_body ops x y) terms (rev formula).
Proof.
intros.
pattern formula at 1 ; rewrite <- rev_involutive.
unfold eval_generic, eval_generic_body.
rewrite <- fold_left_rev_right.
rewrite rev_involutive.
apply refl_equal.
Qed.

Theorem eval_inductive_prop :
  forall A B (P : A -> B -> Prop) (opsA : operations A) (opsB : operations B),
 (forall o a b, P a b -> P (unary opsA o a) (unary opsB o b)) ->
 (forall o a1 a2 b1 b2, P a1 b1 -> P a2 b2 -> P (binary opsA o a1 a2) (binary opsB o b1 b2)) ->
  forall inpA inpB,
 (forall n, P (nth n inpA (unknown opsA)) (nth n inpB (unknown opsB))) ->
  forall prog,
  forall n, P (nth n (eval_generic opsA prog inpA) (unknown opsA)) (nth n (eval_generic opsB prog inpB) (unknown opsB)).
Proof.
intros A B P opsA opsB Hun Hbin inpA inpB Hinp prog.
do 2 rewrite rev_formula.
induction (rev prog).
exact Hinp.
intros [|n].
2: apply IHl.
destruct a as [n|o n|o n1 n2] ;
  [ idtac | apply Hun | apply Hbin ] ; apply IHl.
Qed.

Definition real_operations :=
  Build_operations IZR 0%R
   unary_real binary_real
   (fun x => Xcmp (Xreal x) (Xreal 0)).

Definition eval_real :=
  eval_generic real_operations.

Scheme Equality for expr.

Inductive splitted_expr : Set :=
  | Sconst
  | Scomposed (lp lc : list expr).

Fixpoint rcons_unique (e : expr) (l : list expr) :=
  match l with
  | cons h t =>
    if expr_beq e h then l else cons h (rcons_unique e t)
  | nil => cons e nil
  end.

Lemma rcons_unique_correct : forall e l, exists l',
  rcons_unique e l = l ++ l'.
Proof.
induction l as [ | e' l [l' IHl]].
- now exists (e :: nil).
- simpl. destruct expr_beq.
  + exists nil. apply app_nil_end.
  + exists l'. now rewrite IHl.
Qed.

Definition cons_unique (e : expr) (l : list expr) :=
  let fix aux (l' : list expr) :=
    match l' with
    | cons h t =>
      if expr_beq e h then l else aux t
    | nil => cons e l
    end in
  aux l.

Fixpoint split_expr (e : expr) (lp lc : list expr) :=
  match e with
  | Evar n => Scomposed lp lc
  | Econst o => Sconst
  | Eunary o e1 =>
    match split_expr e1 lp lc with
    | Sconst => Sconst
    | Scomposed lp lc => Scomposed (cons_unique e lp) lc
    end
  | Ebinary o e1 e2 =>
    match split_expr e2 lp lc with
    | Sconst =>
      match split_expr e1 lp lc with
      | Sconst => Sconst
      | Scomposed lp lc => Scomposed (cons_unique e lp) (rcons_unique e2 lc)
      end
    | Scomposed lp lc =>
      match split_expr e1 lp lc with
      | Sconst => Scomposed (cons_unique e lp) (rcons_unique e1 lc)
      | Scomposed lp lc => Scomposed (cons_unique e lp) lc
      end
    end
  end.

Lemma eval_nth_rcons_unique :
  forall d vars vars' e l,
  eval e vars = eval e vars' ->
  (forall n, eval (nth n l d) vars = eval (nth n l d) vars') ->
  forall n,
  eval (nth n (rcons_unique e l) d) vars = eval (nth n (rcons_unique e l) d) vars'.
Proof.
intros d vars vars' e l He Hl.
induction l as [|h t IH] ; simpl.
{ simpl in Hl. now intros [|n]. }
generalize (internal_expr_dec_bl e h).
destruct expr_beq.
{ now intros _. }
intros _ [|n].
{ apply (Hl 0). }
apply IH.
intros n'.
apply (Hl (S n')).
Qed.

Theorem split_expr_correct :
  forall d vars vars' e lp lc,
  (forall n, eval (nth n lc d) vars = eval (nth n lc d) vars') ->
  match split_expr e lp lc with
  | Sconst => eval e vars = eval e vars'
  | Scomposed lp' lc' =>
    forall n, eval (nth n lc' d) vars = eval (nth n lc' d) vars'
  end.
Proof.
intros d vars vars'.
induction e as [n|o|o e1 IHe1|o e1 IHe1 e2 IHe2] ; intros lp lc Hc ; simpl ; try easy.
  specialize (IHe1 lp lc Hc).
  destruct split_expr as [|lp' lc'].
  now apply f_equal.
  apply IHe1.
specialize (IHe2 lp lc Hc).
destruct split_expr as [|lp2 lc2].
  specialize (IHe1 lp lc Hc).
  destruct split_expr as [|lp1 lc1].
  now apply f_equal2.
  now apply eval_nth_rcons_unique.
specialize (IHe1 lp2 lc2 IHe2).
destruct split_expr as [|lp1 lc1].
  now apply eval_nth_rcons_unique.
apply IHe1.
Qed.

Fixpoint find_expr_aux (e : expr) (n : nat) (l : list expr) :=
  match l with
  | cons h t => if expr_beq e h then Some n else find_expr_aux e (S n) t
  | nil => None
  end.

Definition find_expr (e : expr) (vars : nat) (lp lc : list expr) :=
  match e with
  | Evar n =>
    if Nat.ltb n vars then Some (List.length lp + n)%nat else None
  | _ =>
    match find_expr_aux e 0%nat lp with
    | Some n => Some n
    | None => find_expr_aux e (length lp + vars)%nat lc
    end
  end.

Theorem find_expr_correct :
  forall e vars lp lc,
  match find_expr e vars lp lc with
  | Some n => nth n (lp ++ map Evar (seq 0 vars) ++ lc) (Econst (Int 0)) = e
  | None => True
  end.
Proof.
intros e vars lp lc.
assert (H1: forall l n,
    match find_expr_aux e n l with
    | Some k => (n <= k < n + length l)%nat /\ nth (k - n) l (Econst (Int 0)) = e
    | None => True
    end).
  induction l as [|h t IH].
  easy.
  intros n.
  simpl find_expr_aux.
  generalize (internal_expr_dec_bl e h).
  destruct expr_beq.
  intros H.
  split.
  simpl.
  lia.
  rewrite Nat.sub_diag.
  now rewrite H.
  intros _.
  specialize (IH (S n)).
  revert IH.
  destruct find_expr_aux as [k|] ; try easy.
  intros [H1 H2].
  split.
  simpl.
  lia.
  replace (k - n)%nat with (S (k - S n))%nat by lia.
  easy.
unfold find_expr.
set (foo :=
  match find_expr_aux e 0%nat lp with
  | Some n => Some n
  | None => find_expr_aux e (length lp + vars)%nat lc
  end).
assert (H2:
    match foo with
    | Some n => nth n (lp ++ map Evar (seq 0 vars) ++ lc) (Econst (Int 0)) = e
    | None => True
    end).
  unfold foo.
  clear foo.
  generalize (H1 lp 0%nat).
  destruct find_expr_aux as [n1|].
  rewrite Nat.add_0_l, Nat.sub_0_r.
  intros [H2 H3].
  now rewrite app_nth1.
  intros _.
  specialize (H1 lc (length lp + vars)%nat).
  revert H1.
  destruct find_expr_aux as [n2|] ; try easy.
  intros [H1 H2].
  rewrite -> app_nth2 by lia.
  rewrite app_nth2 ; rewrite map_length, seq_length.
  now rewrite <- Nat.sub_add_distr.
  lia.
destruct e as [n|o|o n1|o n1 n2] ; simpl ; try easy.
destruct (Nat.ltb_spec n vars) as [H|H] ; try easy.
rewrite app_nth2 by apply Nat.le_add_r.
rewrite Nat.add_comm, Nat.add_sub.
rewrite app_nth1.
rewrite nth_indep with (d' := Evar 0).
now rewrite map_nth, seq_nth.
now rewrite map_length, seq_length.
now rewrite map_length, seq_length.
Qed.

Fixpoint decompose (vars : nat) (p : list term) (lp lc : list expr) :=
  match lp with
  | nil => Some p
  | cons h t =>
    match find_expr h vars t lc with
    | Some n => decompose vars (cons (Forward n) p) t lc
    | None =>
      match h with
      | Evar n => decompose vars (cons (Forward (length t + n)) p) t lc
      | Econst _ => None
      | Eunary o e1 =>
        match find_expr e1 vars t lc with
        | Some n => decompose vars (cons (Unary o n) p) t lc
        | None => None
        end
      | Ebinary o e1 e2 =>
        match find_expr e1 vars t lc with
        | Some n1 =>
          match find_expr e2 vars t lc with
          | Some n2 => decompose vars (cons (Binary o n1 n2) p) t lc
          | None => None
          end
        | None => None
        end
      end
    end
  end.

Theorem decompose_correct :
  forall vars p lp lc,
  (forall vars n, eval (nth n lc (Econst (Int 0))) vars = eval (nth n lc (Econst (Int 0))) nil) ->
  let lc' := map (fun c => eval c nil) lc in
  match decompose (length vars) p lp lc with
  | None => True
  | Some lp' =>
    eval_real lp' (vars ++ lc') =
    eval_real p ((map (fun c => eval c (vars ++ lc')) lp) ++ (vars ++ lc'))
  end.
Proof.
intros vars p lp lc Hc lc'.
revert p.
induction lp as [|h t IH].
easy.
intros p.
simpl.
assert (H: forall n e,
    nth n (t ++ map Evar (seq 0 (length vars)) ++ lc) (Econst (Int 0)) = e ->
    nth n (map (fun c : expr => eval c (vars ++ lc')) t ++ vars ++ lc') 0%R = eval e (vars ++ lc')).
  intros n e.
  destruct (Nat.lt_ge_cases n (length t)) as [H1|H1].
  rewrite app_nth1 by apply H1.
  intros H.
  rewrite app_nth1 by now rewrite map_length.
  change 0%R with ((fun c => eval c (vars ++ lc')) (Econst (Int 0))).
  rewrite map_nth.
  now rewrite H.
  rewrite app_nth2 by apply H1.
  rewrite (@app_nth2 _ _ _ _ n) ; rewrite map_length.
  2: exact H1.
  destruct (Nat.lt_ge_cases (n - length t) (length vars)) as [H2|H2].
  rewrite app_nth1 by now rewrite map_length, seq_length.
  rewrite app_nth1 by apply H2.
  rewrite nth_indep with (d' := Evar 0) by now rewrite map_length, seq_length.
  rewrite map_nth, seq_nth, Nat.add_0_l by apply H2.
  intros <-.
  simpl.
  now rewrite app_nth1 by apply H2.
  rewrite app_nth2 ; rewrite map_length, seq_length.
  2: exact H2.
  rewrite app_nth2 by apply H2.
  intros H.
  unfold lc'.
  change 0%R with ((fun c => eval c nil) (Econst (Int 0))).
  rewrite map_nth, H.
  rewrite <- H at 2.
  now rewrite Hc, H.
destruct find_expr eqn:H0.
{ generalize (find_expr_correct h (length vars) t lc).
  rewrite H0. specialize (IH (Forward n :: p)).
  destruct decompose; [| easy].
  rewrite IH. intros H1. apply H in H1. rewrite <-H1.
  unfold eval_real. simpl. now unfold eval_generic_body. }
clear H0.
destruct h as [n|o|o e1|o e1 e2] ; try easy.
- specialize (IH (Forward (length t + n) :: p)).
  destruct decompose ; try easy.
  rewrite IH.
  simpl.
  unfold eval_generic_body.
  rewrite app_nth2 ; rewrite map_length.
  apply (f_equal (fun v => eval_real p (nth v _ _ :: _))).
  lia.
  lia.
- generalize (find_expr_correct e1 (length vars) t lc).
  destruct find_expr as [n1|] ; try easy.
  intros H1.
  specialize (IH (Unary o n1 :: p)).
  destruct decompose ; try easy.
  rewrite IH.
  simpl.
  unfold eval_generic_body.
  apply (f_equal (fun v => eval_real p (unary_real o v :: _))).
  now apply H.
- generalize (find_expr_correct e1 (length vars) t lc).
  destruct find_expr as [n1|] ; try easy.
  intros H1.
  generalize (find_expr_correct e2 (length vars) t lc).
  destruct find_expr as [n2|] ; try easy.
  intros H2.
  specialize (IH (Binary o n1 n2 :: p)).
  destruct decompose ; try easy.
  rewrite IH.
  simpl.
  unfold eval_generic_body.
  apply (f_equal2 (fun v1 v2 => eval_real p (binary_real o v1 v2 :: _))).
  now apply H.
  now apply H.
Qed.

Fixpoint max_arity (e : expr) (n : nat) :=
  match e with
  | Evar k => Nat.ltb k n
  | Econst _ => true
  | Eunary o e1 => max_arity e1 n
  | Ebinary o e1 e2 => if max_arity e1 n then max_arity e2 n else false
  end.

Lemma max_arity_correct :
  forall e vars v,
  max_arity e (length vars) = true ->
  eval e (vars ++ v) = eval e vars.
Proof.
induction e as [n|o|o e IH|o e1 IH1 e2 IH2] ; simpl ; intros vars v H.
- apply app_nth1.
  now apply Nat.ltb_lt.
- easy.
- now rewrite IH.
- rewrite <- Bool.andb_lazy_alt in H.
  apply andb_prop in H.
  rewrite IH1 by easy.
  now rewrite IH2.
Qed.

Inductive extracted_expr : Set :=
  | Eabort
  | Eprog (lp : list term) (lc : list expr).

Fixpoint fold_split (le lp lc : list expr) :=
  match le with
  | nil => (lp, lc)
  | e :: le =>
    let (lp, lc) := fold_split le lp lc in
    match split_expr e lp lc with
    | Sconst => (lp, (rcons_unique e lc))
    | Scomposed lp lc => (lp, lc)
    end
  end.

Fixpoint max_arity_list (le : list expr) (vars : nat) :=
  match le with
  | nil => true
  | e :: le => andb (max_arity e vars) (max_arity_list le vars)
  end.

Lemma max_arity_nth :
  forall le vars k d,
  max_arity_list le vars = true ->
  k < length le ->
  max_arity (nth k le d) vars = true.
Proof.
induction le ; try easy.
intros vars k d H Hk.
simpl in H.
apply andb_prop in H.
destruct H as [Ha Hle].
destruct k as [|k] ; try easy.
apply IHle with (1 := Hle).
now simpl in Hk; rewrite <-Nat.succ_lt_mono in Hk.
Qed.

Definition extract_list (le : list expr) (vars : nat) :=
  if max_arity_list le vars then
    let (lp, lc) := fold_split le nil nil in
    let lp' := le ++ lp in
    match decompose vars nil lp' lc with
    | Some p =>  Eprog p lc
    | None => Eabort
    end
  else Eabort.

Definition eval_real_nth k prog vars consts :=
  nth k (eval_real prog (vars ++ map (fun c => eval c nil) consts)) 0%R.

Theorem extract_list_correct :
  forall le vars,
  match extract_list le (length vars) with
  | Eabort => True
  | Eprog lp lc => forall k, k < length le -> eval_real_nth k lp vars lc = eval (nth k le (Econst (Int 0))) vars
  end.
Proof.
intros le vars.
unfold extract_list.
destruct max_arity_list eqn:Ha ; [ |exact I].
destruct fold_split as (lp, lc) eqn:Hf.
generalize (decompose_correct vars nil (le ++ lp) lc).
destruct decompose as [lp'|] ; [ |easy].
assert ((forall (vars0 : list R) (n : nat),
 eval (nth n lc (Econst (Int 0))) vars0 = eval (nth n lc (Econst (Int 0))) nil) /\
 forall k : nat, k < length le ->
 nth k (eval_real nil
   (map (fun c : expr => eval c (vars ++ map (fun c0 : expr => eval c0 nil) lc))
        (le ++ lp) ++ vars ++ map (fun c : expr => eval c nil) lc)) 0%R =
 eval (nth k le (Econst (Int 0))) vars) as [H1 H2].
2: { intros H. apply H in H1. unfold eval_real_nth. now rewrite H1. }
revert lp lc Hf lp'.
induction le ; intros lp lc.
{ intros [= <- <-].
  split ; [ |easy].
  now intros vars0 [|n]. }
simpl fold_split.
simpl in Ha.
apply andb_prop in Ha.
destruct Ha as [Ha1 Ha2].
destruct fold_split as (lp0, lc0) eqn:Hf'.
intros Hf lp'.
destruct (IHle Ha2 lp0 lc0 eq_refl lp') as [IH1 _]. clear IHle.
generalize (fun v => split_expr_correct (Econst (Int 0)) v nil a lp0 lc0).
intros Hs.
destruct split_expr as [|lp1 lc1] ; injection Hf as <- <- ; split.
- intros vars0 n.
  apply eval_nth_rcons_unique.
  now apply Hs.
  easy.
- intros [|k] Hk ; simpl.
  { now apply max_arity_correct. }
  destruct (rcons_unique_correct a lc0) as [l' ->].
  simpl in Hk.
  rewrite <-Nat.succ_lt_mono in Hk.
  rewrite app_nth1.
  2: { rewrite map_length, app_length. lia. }
  rewrite map_nth with (d := Econst (Int 0)).
  rewrite app_nth1 by easy.
  apply max_arity_correct.
  now apply max_arity_nth.
- intros vars0.
  now apply Hs.
- intros [|k] Hk ; simpl.
  { now apply max_arity_correct. }
  simpl in Hk.
  rewrite <-Nat.succ_lt_mono in Hk.
  rewrite app_nth1.
  2: { rewrite map_length, app_length. lia. }
  rewrite map_nth with (d := Econst (Int 0)).
  rewrite app_nth1 by easy.
  apply max_arity_correct.
  now apply max_arity_nth.
Qed.

Definition extract e vars := extract_list (e :: nil) vars.

Definition eval_real' prog vars consts :=
  nth O (eval_real prog (vars ++ map (fun c => eval c nil) consts)) 0%R.

Theorem extract_correct :
  forall e vars,
  match extract e (length vars) with
  | Eabort => True
  | Eprog lp lc => eval_real' lp vars lc = eval e vars
  end.
Proof.
intros e vars.
change (eval e vars) with (eval (nth O (e :: nil) (Econst (Int 0))) vars).
unfold eval_real', extract.
generalize (extract_list_correct (e :: nil) vars).
destruct extract_list; [easy | ]. intros H.
now specialize (H O (Nat.lt_0_succ _)).
Qed.
