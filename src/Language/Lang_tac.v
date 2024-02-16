From Coq Require Import Reals List.
From Flocq Require Import Core BinarySingleNaN Operations.

Require Import Lang_expr Lang_simpl.

Local Open Scope R_scope.

Lemma destructLet : forall Tl T1 T2
    (P  : evalExprTypeRounded T1 -> evalExprTypeRounded T2 -> Prop)
    (Q  : evalExprTypeRounded T1 -> Prop)
    (x  : ArithExpr Tl T1) (t  : ArithExpr (T1 :: Tl) T2)
    (lM : evalExprTypeRounded_list Tl) md,
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
  | |- context [evalRounded t ?lM ?md] => lM end in (* Why t and not x? *)
  let md := lazymatch goal with
  | |- context [evalRounded (Let x t) lM ?md] => md
  | |- context [evalRounded t lM ?md] => md end in (* Why t and not x? *)
  pattern (evalRounded (Let x t) lM md); pattern (evalRounded x lM md);
  lazymatch goal with
  | |- (fun vM => (fun wM => wellBehaved (Let x t) ?lM ?md /\ ?P) ?yM) ?xM =>
    change ((fun vM => (fun wM => wellBehaved (Let x t) lM md /\ P) yM) xM)
    with   (wellBehaved (Let x t) lM md /\ (fun vM wM => P) xM yM);
    apply (destructLet Tl T1 T2 (fun vM wM => P) Q x t lM)
  end
end.

Ltac remove_Let_x x xR G := match G with
| context G' [wellBehaved (Let x ?t) ?lR ?md]
  => let G'' := context G' [wellBehaved t (xR, lR) md] in remove_Let_x x xR G''
| context G' [wellBehaved x ?lR ?md]
  => let G'' := context G' [True] in remove_Let_x x xR G''
| context G' [evalRounded (Let x ?t) ?lR ?md]
  => let G'' := context G' [evalRounded t (xR, lR) md] in remove_Let_x x xR G''
| _ => G
end.

Ltac do_assert_multilet Q :=
lazymatch goal with
| |- ?G => lazymatch G with
  | context [@Let ?Tl ?T1 ?T2 ?x _] =>
    let lR := lazymatch goal with
    | |- context [evalRounded (Let x _) ?lR ?md] => lR
    | |- context [evalRounded x ?lR ?md] => lR end in
    let md := lazymatch goal with
    | |- context [evalRounded (Let x _) lR ?md] => md
    | |- context [evalRounded x lR ?md] => md end in
    let xR := constr:(evalRounded x lR md) in
    let WBx := constr:(wellBehaved x lR md) in
    let G' := constr:(WBx -> Q xR) in
    let G'' := remove_Let_x x xR constr:(G' -> G) in
    let H := fresh "__H" in let xR' := fresh "__xR" in
    cut G'; [cut (WBx /\ G''); [intuition; try easy | split; [|
      generalize xR; intros xR' H; specialize (H I)]] |]
  end
end.


Tactic Notation "assert_let" open_constr(Q) := do_assert_let Q.

Tactic Notation "assert_let" open_constr(Q) "as"
    ident(xM) simple_intropattern(H) :=
  do_assert_let Q; [| | intros xM H].

Tactic Notation "assert_multilet" open_constr(Q) := do_assert_multilet Q.

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
    simple refine (@generateCProp_correct Tl T t _ v md _ _ _ _);
    [try easy.. | let n := eval lazy in (length l) in
      change (length _) with n; (repeat match reverse goal with
        | H: _ |- _ => clear H end); vm_compute; reflexivity |]
   |unfold P; clear P; cbn -[bpow (* evalCArithExpr2 *)]]
end.

Ltac simplify_wb_taylor :=
let P := fresh "__P" in evar (P : Prop);
lazymatch goal with
  | |- @wellBehaved ?Tl ?T ?t ?v ?md => let l := compute_vars v in
    cut P;
   [Reify.find_hyps l; change l with (@toList Tl (@M2R_list Tl v));
    eapply (@generateCProp_taylor_correct Tl T t _ v md);
    [try easy.. | vm_compute; reflexivity |]
   |unfold P; clear P; cbn -[bpow (* evalCArithExpr2 *)]]
end.

Ltac remove P G := match G with
| context G' [P /\ ?P'] => let G'' := context G' [P'] in remove P G''
| context G' [?P' /\ P] => let G'' := context G' [P'] in remove P G''
| context G' [?P' \/ P] => let G'' := context G' [True] in remove P G''
| context G' [P \/ ?P'] => let G'' := context G' [True] in remove P G''
| _ => G
end. (* is_finite, is_finite_strict, B2R, fp_classsify *)

Ltac replace_term t t' G :=
lazymatch G with
| context G' [t] => let G'' := (context G' [t']) in replace_term t t' G''
| _ => G
end.

Ltac clean t G :=
match G with
| context [is_finite t = ?b] =>
  let G' := remove (is_finite t = b) G in clean t G'
| context [is_finite_SF t = ?b] =>
  let G' := remove (is_finite_SF t = b) G in clean t G'
| _ => G
end.

Ltac do_reify_var x :=
revert dependent x; intros x; cut (generic_format radix2 (FLT_exp (-1074) 53) (B2R x));
  [| apply generic_format_B2R]; generalize (B2R x); let r := fresh "__r" in intros r;
  intros; clear dependent x; revert dependent r. (* TODO: Add hypothesis -maxval <= B2R x <= maxval *)

Tactic Notation "reify_var" ident(x) "as" ident(xM) ident(Hformat_xM) :=
  do_reify_var x; intros xM Hformat_xM.

Ltac do_reify_var' x :=
revert dependent x; intros x; rewrite <-(Prim2SF2R_Prim2B2R x);
  cut (generic_format radix2 (FLT_exp (-1074) 53) (B2R (PrimFloat.Prim2B x)));
  [| apply generic_format_B2R]; generalize (B2R (PrimFloat.Prim2B x)); let r := fresh "__r" in intros r;
  intros; clear dependent x; revert dependent r. (* TODO: merge with previous tactic *)

Tactic Notation "reify_var'" ident(x) "as" ident(xM) ident(Hformat_xM) :=
  do_reify_var' x; intros xM Hformat_xM.

Ltac remove_floats :=
lazymatch goal with
| |- ?G0 => match G0 with
  | context [@evalFloat ?Tl ?T ?t ?lC ?md] =>
 (* clean_goal (evalFloat t lC md) G0; *)
    let G1 := clean (evalFloat t lC md) G0 in
    let G2 := replace_term (B2R (@evalFloat Tl T t lC md)) (@evalRounded Tl T t (@C2M_list Tl lC) md) G1 in
    let G3 := match G2 with
    | context G' [?g] =>
      context G' [@wellBehaved Tl T t (@C2M_list Tl lC) md /\ g]
    end in
    let IWB   := fresh "IWB"   in let Hgoal   := fresh "Hgoal"   in
    let Iconv := fresh "Iconv" in let IisConv := fresh "IisConv" in cut G3;
     [intros [IWB Hgoal]; refine (_ (@equivFloat Tl T t lC md _ IWB _));
       [intros [Iconv ->]; intuition |
        repeat lazymatch goal with |- convertibleFloat_list _ => split ; try easy end |
        try easy]
     | simpl C2M_list]
  | context [@evalPrim ?Tl ?T ?t ?lP] =>
 (* clean_goal (evalPrim t lC md) G0; *)
    let G1 := clean (FloatOps.Prim2SF (@evalPrim Tl T t lP)) G0 in
    let G2 := replace_term (SF2R radix2 (FloatOps.Prim2SF (@evalPrim Tl T t lP))) (evalRounded t (@P2M_list Tl lP) mode_NE) G1 in
    let G3 := match G2 with
    | context [@evalPrim Tl T t lP] =>
      constr:(eqExprTypePrim (@evalPrim Tl T t lP) (@evalRounded Tl T t (@P2M_list Tl lP) mode_NE) -> G2)
    | _ => G2
    end in
    let G4 := constr:(wellBehaved t (@P2M_list Tl lP) mode_NE /\ G3) in
    let IWB   := fresh "IWB"   in let Hgoal   := fresh "Hgoal"   in
    let Iconv := fresh "Iconv" in let IisConv := fresh "IisConv" in cut G4;
     [intros [IWB Hgoal]; refine (_ (@equivPrim Tl T t lP _ IWB _));
       [let H := fresh "__H" in
        intros [Iconv H]; unfold isConversionPrim in H;
        rewrite ?H; intuition; apply Hgoal; easy |
        clear IWB Hgoal; repeat lazymatch goal with |- convertiblePrim_list _ => split ; try easy end |
        try easy]
     | simpl P2M_list]
  end
end.
