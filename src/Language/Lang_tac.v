From Coq Require Import Reals List.
From Flocq Require Import Core BinarySingleNaN Operations.

Require Import Lang_expr Lang_simpl.

Open Scope R_scope.

Lemma destructLet : forall Tl T1 T2
    (P  : evalExprTypeMath T1 -> evalExprTypeMath T2 -> Prop)
    (Q  : evalExprTypeMath T1 -> Prop)
    (x  : ArithExprTree Tl T1) (t  : ArithExprTree (T1 :: Tl) T2)
    (lM : evalExprTypeMath_list Tl) md,
  let xM := evalRounded x lM md in
  wellBehaved x lM md -> (wellBehaved x lM md -> Q (evalRounded x lM md)) ->
 (forall xM', Q xM' -> wellBehaved t (xM', lM) md
                    /\ P xM' (evalRounded t (xM', lM) md)) ->
  wellBehaved (Let x t) lM md /\ P xM (evalRounded (Let x t) lM md).
Proof. intros Tl T1 T2 P Q x t lM md xM IWB IQ H. specialize (IQ IWB). simpl.
now split; [split; [assumption |] | fold xM]; apply H.
Qed.

Ltac do_assert_let Q :=
lazymatch goal with
| |- context [@Let ?Tl ?T1 ?T2 ?x ?t] =>
  let lM := lazymatch goal with
  | |- context [evalRounded (Let x t) ?lM ?md] => lM
  | |- context [evalRounded t ?lM ?md] => lM end in
  let md := lazymatch goal with
  | |- context [evalRounded (Let x t) lM ?md] => md
  | |- context [evalRounded t lM ?md] => md end in
  pattern (evalRounded (Let x t) lM md); pattern (evalRounded x lM md);
  lazymatch goal with
  | |- (fun vM => (fun wM => wellBehaved (Let x t) ?lM ?md /\ ?P) ?yM) ?xM =>
    change ((fun vM => (fun wM => wellBehaved (Let x t) lM md /\ P) yM) xM)
    with   (wellBehaved (Let x t) lM md /\ (fun vM wM => P) xM yM);
    apply (destructLet Tl T1 T2 (fun vM wM => P) Q x t lM)
  end
end.


Tactic Notation "assert_on_let" open_constr(Q) := do_assert_let Q.

Tactic Notation "assert_on_let" open_constr(Q) "as"
    ident(xM) simple_intropattern(H) :=
  do_assert_let Q; [| | intros xM H].

Ltac compute_vars v := match v with
  | tt        => constr:(@nil R)
  | (?a, ?v') => let l := compute_vars v' in
    match True with
    | True => constr:(a :: l)
    | True => constr:(IZR a :: l) end
  end.

Ltac compute_vars_Real v := match v with
  | tt        => constr:(@nil R)
  | (?a, ?v') => let l := compute_vars v' in constr:(a :: l)
  end.

Ltac simplify_wb :=
let P := fresh "__P" in evar (P : Prop);
lazymatch goal with
  | |- @wellBehaved ?Tl ?T ?t ?v ?md => let l := compute_vars v in
    cut P;
   [Reify.find_hyps l; change l with (@toList Tl (@M2R_list Tl v));
    eapply (@generatePProp_correct Tl T t v md);
    [try easy | vm_compute; reflexivity]
   |unfold P; clear P; cbn -[bpow (* evalPTree2 *)]]
end.

Ltac simplify_wb_taylor :=
let P := fresh "__P" in evar (P : Prop);
lazymatch goal with
  | |- @wellBehaved ?Tl ?T ?t ?v ?md => let l := compute_vars v in
    cut P;
   [Reify.find_hyps l; change l with (@toList Tl (@M2R_list Tl v));
    eapply (@generatePProp_taylor_correct Tl T t v md);
    [try easy | vm_compute; reflexivity]
   |unfold P; clear P; cbn -[bpow (* evalPTree2 *)]]
end.


Ltac decompose_wb := apply @evalFloat_evalRounded;
  [| simpl C2M_list; simpl M2R_list; simplify_wb |]; try easy.

Lemma and_idem : forall A, A /\ A <-> A.
Proof. easy. Qed.

Ltac dig_out P := lazymatch goal with
| |- context [P /\ P] => rewrite !(and_idem P); dig_out P
| |- context [?P' /\ P] => rewrite !(and_comm P' P); dig_out P
| |- context [P /\ P /\ ?P0] => rewrite <-(and_assoc P P P0);
     rewrite (and_idem P); dig_out P
| |- context [?P1 /\ P /\ ?P0] => rewrite <-(and_assoc P1 P P0);
     rewrite (and_comm P1 P); rewrite (and_assoc P P1 P0); dig_out P
| |- context [(P /\ ?P0) /\ ?P1] => rewrite (and_assoc P P0 P1); dig_out P
| |- P /\ _ => idtac
| |- P => idtac
| _ => fail "not found"
end.

Goal forall (A B C : Prop), A -> B -> C -> ((A /\ B) /\ (C /\ A) /\ C) /\ ((B /\ C /\ B) /\ A) /\ A.
Proof. intros A B C HA HB HC. dig_out B. dig_out A. Abort.

Ltac remove P G := match G with
| context G' [P /\ ?P'] => let G'' := context G' [P'] in remove P G''
| context G' [?P' /\ P] => let G'' := context G' [P'] in remove P G''
| context G' [?P' \/ P] => let G'' := context G' [True] in remove P G''
| context G' [P \/ ?P'] => let G'' := context G' [True] in remove P G''
| _ => G
end.

Ltac replace_term t t' G :=
lazymatch G with
| context G' [t] => let G'' := (context G' [t']) in replace_term t t' G''
| _ => G
end.

Ltac switch :=
lazymatch goal with
| |- ?G0 => match G0 with
  | context [@evalFloat ?Tl ?T ?t ?lC ?md] =>
    let G1 := match G0 with
    | context G' [?g] => context G' [(eqExprType (@evalFloat Tl T t lC md) (@evalRounded Tl T t (@C2M_list Tl lC) md)) /\ g]
    end in
    let G  := replace_term (B2R (@evalFloat Tl T t lC md))
             (@evalRounded Tl T t (@C2M_list Tl lC) md) G1 in
    cut G; simpl C2M_list
  end
end.

Ltac clean xC G :=
match G with
| context [is_finite xC = ?b] =>
  let G' := remove (is_finite xC = b) G in clean xC G'
| context [C2M xC = ?xM0] =>
  let G' := remove (C2M xC = xM0) G in clean xC G'
| context [B2R xC = ?xM1] =>
  let G' := remove (B2R xC = xM1) G in clean xC G'
| context [xC = ?xM2] =>
  let G' := remove (xC = xM2) G in clean xC G'
| _ => G
end.

Ltac clean_goal xC G :=
match G with
| context [is_finite xC = ?b] =>
  let G' := remove (is_finite xC = b) G in
  try dig_out (is_finite xC = b); try clean_goal xC G'
| context [C2M xC = ?xM0] =>
  let G' := remove (C2M xC = xM0) G in
  try dig_out (C2M xC = xM0); try clean_goal xC G'
| context [B2R xC = ?xM1] =>
  let G' := remove (B2R xC = xM1) G in
  try dig_out (B2R xC = xM1); try clean_goal xC G'
| context [xC = ?xM2] =>
  let G' := remove (xC = xM2) G in
  try dig_out (xC = xM2); try clean_goal xC G'
| _ => try (dig_out True; split; [easy |])
end.

Ltac do_extract_real x :=
revert dependent x; intros x; cut (generic_format radix2 (FLT_exp (-1074) 53) (B2R x));
  [| apply generic_format_B2R]; generalize (B2R x); let r := fresh "__r" in intros r;
  intros; clear dependent x; revert dependent r.

Tactic Notation "extract_real" ident(x) "as" ident(xM) ident(Hformat_xM) :=
  do_extract_real x; intros xM Hformat_xM.

Ltac remove_float :=
lazymatch goal with
| |- ?G0 => lazymatch G0 with
  | context [@evalFloat ?Tl ?T ?t ?lC ?md] =>
    clean_goal (evalFloat t lC md) G0;
    let G1 := clean (evalFloat t lC md) G0 in
    let G2 := replace_term (B2R (evalFloat t lC md)) (evalRounded t (@C2M_list Tl lC) md) G1 in
    let G3 := match G2 with
    | context G' [?g] =>
      context G' [(eqExprType (evalFloat t lC md) (evalRounded t (@C2M_list Tl lC) md)) /\ g]
    end in let G3' := match G2 with
    | context G' [?g] =>
      context G' [wellBehaved t (@C2M_list Tl lC) md /\ g]
    end in
    let Hfin := fresh "Hfin" in let Heq := fresh "Heq" in let Hgoal := fresh "Hgoal" in
    let IWB  := fresh "IWB"  in let IWF := fresh "IWF" in cut G3; simpl C2M_list;
   [(intros [[Hfin Heq] Hgoal] || intros Heq Hgoal); repeat (split; [easy |]); now rewrite Heq
   | cut G3';
     [ intros [IWB Hgoal]; split; [apply @evalFloat_evalRounded; [try easy | easy | try easy] | easy]
     | simpl C2M_list ]]
  end
end.
