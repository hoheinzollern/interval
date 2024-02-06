From Coq Require Import Bool Floats Reals List Lia Lra.
From Flocq Require Import Core PrimFloat BinarySingleNaN Operations.

Require Import Specific_bigint Specific_ops.
Require Import Interval_helper.
Require Import Float_full.
Require Import Prog.
Require Import Lang_expr.

Open Scope R_scope.

Ltac destruct_tuple := try match goal with
  | |- match ?t with _ => _ end => match type of t with
    | prod _ _ => rewrite (surjective_pairing t); destruct_tuple end end.

Ltac destruct_tuple_hyp H := try match type of H with
  | match ?t with _ => _ end => match type of t with
    | prod _ _ => rewrite (surjective_pairing t) in H; destruct_tuple_hyp H end end.

Ltac destruct_tuple_obj t := try match type of t with
  | prod _ _ => rewrite (surjective_pairing t) in *; destruct_tuple_obj (fst t) end.


Fixpoint toList {Tl} := match Tl return evalExprTypeReal_list Tl -> _ with
  | nil => fun _ => nil
  | _ :: Tl' => fun l => let x := fst l in let l' := snd l in x :: toList l' end.

Fixpoint exprsucc t := match t with
  | Tree.Evar n => Tree.Evar (S n)
  | Tree.Econst _ => t
  | Tree.Eunary op t' => Tree.Eunary op (exprsucc t')
  | Tree.Ebinary op t1 t2 => Tree.Ebinary op (exprsucc t1) (exprsucc t2) end.

Lemma eval_exprsucc : forall t l x, Tree.eval (exprsucc t) (x :: l) = Tree.eval t l.
Proof. now induction t; simpl; intros; [| | rewrite IHt | rewrite IHt1, IHt2]. Qed.



(* Computable/Compatible arithmetic expressions *)

Inductive CArithOp := CADD | CSUB | CMUL | CFLTDIV | CINTDIV.

Definition ArithOpToCArithOp T OP := match OP with
  | ADD => CADD
  | SUB => CSUB
  | MUL => CMUL
  | DIV => match T with
    | Integer  => CINTDIV
    | BinFloat => CFLTDIV
    end
  end.

Definition rounding_mode_of_mode md := match md with
  | mode_NE | mode_NA => Basic.rnd_NE
  | mode_ZR           => Basic.rnd_ZR
  | mode_DN           => Basic.rnd_DN
  | mode_UP           => Basic.rnd_UP
end.

Inductive CArithExpr :=
  | CInt: Z -> CArithExpr
  | CBinFl: Z -> Z -> CArithExpr
  | CVar: nat -> CArithExpr
  | COp: CArithOp -> CArithExpr -> CArithExpr -> CArithExpr
  | CRnd: mode -> CArithExpr -> CArithExpr
  | CNearbyint: CArithExpr -> CArithExpr
  | CTrunc: CArithExpr -> CArithExpr
  | CLdexp: CArithExpr -> CArithExpr -> CArithExpr
  | CSqrt: CArithExpr -> CArithExpr.

Fixpoint CArithExprToTree t := match t with
  | CInt n => Tree.Econst (Tree.Int n)
  | CBinFl n1 n2 => Tree.Ebinary Tree.Mul (Tree.Econst (Tree.Int n1)) (Tree.Econst (Tree.Bpow 2 n2))
  | CVar n => Tree.Evar n
  | COp OP t1 t2 => let u1 := CArithExprToTree t1 in let u2 := CArithExprToTree t2 in match OP with
    | CADD    => Tree.Ebinary Tree.Add u1 u2
    | CSUB    => Tree.Ebinary Tree.Sub u1 u2
    | CMUL    => Tree.Ebinary Tree.Mul u1 u2
    | CFLTDIV => Tree.Ebinary Tree.Div u1 u2
    | CINTDIV => Tree.Eunary (Tree.Nearbyint Basic.rnd_ZR) (Tree.Ebinary Tree.Div u1 u2)
    end
  | CRnd md t' => Tree.Eunary (Tree.RoundFlt (rounding_mode_of_mode md) Rrnd.emin Format64.prec) (CArithExprToTree t')
  | CNearbyint t' => Tree.Eunary (Tree.Nearbyint Basic.rnd_NE) (CArithExprToTree t')
  | CTrunc t' => Tree.Eunary (Tree.Nearbyint Basic.rnd_ZR) (CArithExprToTree t')
  | CLdexp t' p => Tree.Econst (Tree.Int 0) (* not compatible *)
  | CSqrt t' => Tree.Eunary Tree.Sqrt (CArithExprToTree t') end.

Fixpoint Psucc t := match t with
  | CInt _ | CBinFl _ _ => t
  | CVar n => CVar (S n)
  | COp OP t1 t2 => COp OP (Psucc t1) (Psucc t2)
  | CRnd md t' => CRnd md (Psucc t')
  | CNearbyint t' => CNearbyint (Psucc t')
  | CTrunc t' => CTrunc (Psucc t')
  | CLdexp t' p => CLdexp (Psucc t') (Psucc p)
  | CSqrt t' => CSqrt (Psucc t') end.

Lemma CArithExprToTree_Psucc : forall t, CArithExprToTree (Psucc t) = exprsucc (CArithExprToTree t).
Proof.
induction t as [| | | OP | | | | |]; simpl; intros.
5, 6, 7, 9: now rewrite IHt. 1, 2, 3, 5: easy.
now destruct OP; rewrite IHt1; rewrite IHt2.
Qed.

Definition evalCArithExpr1 t l := Tree.eval (CArithExprToTree t) l.

Fixpoint evalCArithExpr2 t l := match t with
  | CInt n => IZR n
  | CBinFl n1 n2 => IZR n1 * Rpow2 n2
  | CVar n => nth n l R0
  | COp OP t1 t2 => let x1 := evalCArithExpr2 t1 l in let x2 := evalCArithExpr2 t2 l in
    match OP with
    | CADD    => (evalCArithExpr2 t1 l) + (evalCArithExpr2 t2 l)
    | CSUB    => (evalCArithExpr2 t1 l) - (evalCArithExpr2 t2 l)
    | CMUL    => (evalCArithExpr2 t1 l) * (evalCArithExpr2 t2 l)
    | CFLTDIV => (evalCArithExpr2 t1 l) / (evalCArithExpr2 t2 l)
    | CINTDIV => @Rrnd.nearbyint mode_ZR ((evalCArithExpr2 t1 l) / (evalCArithExpr2 t2 l))
    end
  | CRnd md t' => round radix2 (FLT_exp emin prec) (round_mode md) (evalCArithExpr2 t' l)
  | CNearbyint t' => @Rrnd.nearbyint mode_NE (evalCArithExpr2 t' l)
  | CTrunc t' => @Rrnd.nearbyint mode_ZR (evalCArithExpr2 t' l)
  | CLdexp t' p => ((evalCArithExpr2 t' l) * Rpower 2 (evalCArithExpr2 p l))
  | CSqrt t' => sqrt (evalCArithExpr2 t' l) end.

Lemma evalCArithExpr2_succ : forall t l x, evalCArithExpr2 (Psucc t) (x :: l) = evalCArithExpr2 t l.
Proof. induction t as [| | | OP | | | | |]; simpl; intros.
5, 6, 7, 9: now rewrite IHt. 1, 2, 3: easy.
- now destruct OP; rewrite IHt1, IHt2.
- now rewrite IHt1; rewrite IHt2.
Qed.



(* Computable Prop *)

Inductive Atom :=
(*| Ne: CArithExpr -> CArithExpr -> Atom
  | Lt: CArithExpr -> CArithExpr -> Atom
  | Le: CArithExpr -> CArithExpr -> Atom
  | Ge: CArithExpr -> CArithExpr -> Atom
  | Gt: CArithExpr -> CArithExpr -> Atom
  | Eq: CArithExpr -> CArithExpr -> Atom
  | LeLe: CArithExpr -> CArithExpr -> CArithExpr -> Atom
  | AbsLe: CArithExpr -> CArithExpr -> Atom *)
  | InInt32: CArithExpr -> Atom (* - IZR (Int32.N / 2) <= t <= IZR (Int32.N / 2 - 1) *)
  | InInt51: CArithExpr -> Atom
  | InInt64: CArithExpr -> Atom (* - IZR (Int64.N / 2) <= t <= IZR (Int64.N / 2 - 1) *)
  | InFloat64: CArithExpr -> Atom (* Rabs t <= Rrnd.maxval *)
  | InFloat64Int: CArithExpr -> Atom (* Rabs t <= Rpow2 53 *)
  | NonZero: CArithExpr -> Atom (* t <> 0 *)
  | NonNeg: CArithExpr -> Atom (* 0 <= t *)
  | RndExact: mode -> CArithExpr -> Atom (* Rrnd.rnd t = t *)
  | LdexpControl: Z -> CArithExpr -> CArithExpr -> Atom
    (* (Rabs (evalReal _ _ t1 vars)) <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec)
    /\ IZR n + evalReal _ _ t2 vars <= IZR Rrnd.emax *).

Definition AtomToProp g l := match g with
  | InInt32 t => - IZR (Int32.N / 2) <= evalCArithExpr2 t l <= IZR (Int32.N / 2 - 1)
  | InInt51 t => -2251799813685248 <= evalCArithExpr2 t l <= 2251799813685247
  | InInt64 t => - IZR (Int64.N / 2) <= evalCArithExpr2 t l <= IZR (Int64.N / 2 - 1)
  | InFloat64 t => Rabs (evalCArithExpr2 t l) <= Rrnd.maxval
  | InFloat64Int t => Rabs (evalCArithExpr2 t l) <= Rpow2 53
  | NonZero t => evalCArithExpr2 t l <> 0
  | NonNeg t => 0 <= evalCArithExpr2 t l
  | RndExact md t => let u := evalCArithExpr2 t l in round radix2 (FLT_exp emin prec) (round_mode md) u = u
  | LdexpControl n t p =>
    Rabs (evalCArithExpr2 t l) <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec) /\
    IZR n + evalCArithExpr2 p l <= IZR Rrnd.emax end.

Inductive CProp :=
  | CTrue | CFalse
  | CAtom: Atom -> CProp
(*| CNot: CProp -> CProp
  | COr: CProp -> CProp -> CProp *)
  | CAnd: CProp -> CProp -> CProp.

Fixpoint CPropToProp p l := match p with
  | CFalse => False
  | CTrue => True
  | CAtom i => AtomToProp i l
  | CAnd p1 p2 => CPropToProp p1 l /\ CPropToProp p2 l end.

Fixpoint simplifyCProp p := match p with
  | CFalse => CFalse
  | CTrue => CTrue
  | CAtom i => CAtom i
  | CAnd p1 p2 => match simplifyCProp p1, simplifyCProp p2 with
    | CTrue, p' | p', CTrue => p'
    | p1', p2' => CAnd p1' p2' end
  end.

Lemma simplifyCProp_correct :
  forall p l, CPropToProp (simplifyCProp p) l <-> CPropToProp p l.
Proof. split.
- induction p; simpl; [easy.. |].
  now destruct (simplifyCProp p1), (simplifyCProp p2);
  simpl; intros; (split; [apply IHp1 | apply IHp2]).
- induction p; simpl; [easy.. |]. intros [H1 H2].
  now destruct (simplifyCProp p1), (simplifyCProp p2); simpl in *;
  apply IHp1 in H1; apply IHp2 in H2; [easy | ..]; repeat split.
Qed.



(* Auxiliary functions on computables *)

Fixpoint list_var_aux n init := match n with
  | O => nil
  | S n' => CVar init :: list_var_aux n' (S init) end.

Lemma length_list_var_aux : forall n i, length (list_var_aux n i) = n.
Proof. now induction n; [| intros i; simpl; rewrite (IHn (S i))]. Qed.

Lemma nth_list_var_aux_S: forall n k i t, nth (S n) (list_var_aux (S k) i) (Psucc t) =
  Psucc (nth n (list_var_aux k i) t).
Proof. induction n; destruct k; [easy.. |].
intros i t. simpl in *. now rewrite (IHn k (S i) t).
Qed.

Definition list_var n := list_var_aux n O.

Lemma list_var_correct1 : forall Tl (l : evalExprTypeReal_list Tl) n,
evalCArithExpr1 (nth n (list_var (length Tl)) (CInt 0)) (toList l) = nthExprTypeReal n l 0.
Proof. unfold evalCArithExpr1.
induction Tl as [| T' Tl]; destruct n; [easy | easy | easy |]. simpl length.
simpl toList. change (CInt 0) with (Psucc (CInt 0)). unfold list_var in *.
rewrite nth_list_var_aux_S. rewrite CArithExprToTree_Psucc, eval_exprsucc.
now rewrite IHTl.
Qed.

Lemma list_var_correct2 : forall Tl (l : evalExprTypeReal_list Tl) n,
evalCArithExpr2 (nth n (list_var (length Tl)) (CInt 0)) (toList l) = nthExprTypeReal n l 0.
Proof.
induction Tl as [| T' Tl]; destruct n; [easy | easy | easy |]. simpl length.
simpl toList. change (CInt 0) with (Psucc (CInt 0)). unfold list_var in *.
rewrite nth_list_var_aux_S. rewrite evalCArithExpr2_succ. now rewrite IHTl.
Qed.

Fixpoint compatible t := match t with
  | CInt _ | CBinFl _ _ | CVar _ => true
  | COp _ t1 t2 => andb (compatible t1) (compatible t2)
  | CNearbyint t | CTrunc t | CSqrt t => compatible t
  | CRnd md t => match md with mode_NA => false | _ => compatible t end
  | CLdexp _ _ => false end.

Lemma compatible_correct :
  forall t l, compatible t = true -> evalCArithExpr1 t l = evalCArithExpr2 t l.
Proof. unfold evalCArithExpr1. induction t as [| | | OP | | | | |]; simpl; intros.
6, 7: now rewrite IHt, Rrnd.nearbyint_IZR. 1, 2, 3, 6: easy.
- apply andb_prop in H. destruct H as [H1 H2].
  destruct OP; simpl; (rewrite IHt1, IHt2; [| easy | easy]);
  [easy | easy | easy | easy |]. now rewrite Rrnd.nearbyint_IZR.
- destruct m; [.. | easy]; now rewrite IHt.
- now rewrite IHt.
Qed.

Definition compatible_atom a := match a with
  | InInt32 t | InInt51 t | InInt64 t | InFloat64 t
  | InFloat64Int t | NonZero t | NonNeg t => compatible t
  | _                                     => false
  end.

Definition add_compatibility t := (t, compatible t).



(* Separate proof obligations *)

Inductive BTree :=
  | Void: BTree
  | Leaf: Atom  -> BTree
  | Node: BTree -> BTree -> BTree.

Fixpoint BTreeToList_aux bt acc := match bt with
  | Void => acc
  | Leaf i => i :: acc
  | Node bt1 bt2 =>
    let acc' := BTreeToList_aux bt2 acc in BTreeToList_aux bt1 acc'
  end.

Definition BTreeToList bt := BTreeToList_aux bt nil.

Lemma BTreeToList_aux_concat : forall bt acc,
  BTreeToList_aux bt acc = BTreeToList bt ++ acc.
Proof. induction bt as [| i | bt1 IHbt1 bt2 IHbt2]; [easy | easy |].
intros acc. unfold BTreeToList. simpl. rewrite IHbt2. rewrite 2IHbt1.
now rewrite app_assoc.
Qed.

Fixpoint merge l p := match l with
  | nil => p
  | i :: l' => merge l' (CAnd p (CAtom i))
  end.

Lemma merge_decomp : forall l1 p l,
  CPropToProp (merge l1 p) l <-> CPropToProp (merge l1 CTrue) l /\ CPropToProp p l.
Proof. induction l1 as [| t l1]; [easy |]. simpl. intros p l.
destruct_tuple_obj t. split; intros H.
- apply IHl1 in H. destruct H as [H1 H]. simpl in H. destruct H as [h H].
  split; apply IHl1.
  + now split; [| simpl].
  + now apply IHl1.
- destruct H as [H1 h]. apply IHl1 in H1. destruct H1 as [H1 H]. simpl in H.
  apply IHl1. now split; [| simpl].
Qed.

Lemma merge_app : forall l1 l2 p l,
  CPropToProp (merge (l1 ++ l2) p) l <->
 (CPropToProp (merge l1 p) l /\ CPropToProp (merge l2 p) l).
Proof. intros l1 l2 p l. rewrite (merge_decomp (l1 ++ l2)).
  rewrite (merge_decomp l1). rewrite (merge_decomp l2).
  induction l1 as [| t l1]; simpl; [easy |].
  destruct_tuple_obj t. rewrite (merge_decomp (l1 ++ l2)).
  rewrite (merge_decomp l1). split.
  - intros [[H12 H] h]. simpl in H. now repeat split; try easy; apply IHl1; split.
  - intros [[[H1 H] h] [H2 _]]. simpl in H. repeat split; try easy.
    now apply IHl1.
Qed.

Fixpoint well_formed {Tl} : evalExprTypeReal_list Tl -> _ :=
  match Tl with
  | nil      => fun _  vars _ => vars = nil (* Possibly improvable *)
  | _ :: Tl' => fun lR vars l => let x := fst lR in let lR' := snd lR in
    match vars with
    | nil             => False
    | (t, b) :: vars' => (b = true -> compatible t = true) /\
                         (evalCArithExpr2 t l) = x /\ well_formed lR' vars' l
    end
  end.

Lemma well_formed_list_var_aux {Tl} : forall (lR : evalExprTypeReal_list Tl) l,
  well_formed lR (map add_compatibility (list_var_aux (length Tl) (length l))) (l ++ toList lR).
Proof. induction Tl; [easy |]. intros [xR lR] l. simpl. repeat split.
- apply nth_middle.
- rewrite <-(app_nil_l (toList lR)), app_comm_cons, app_assoc.
  rewrite <-(last_length l xR). apply IHTl.
Qed.

Corollary well_formed_list_var {Tl} : forall (lR : evalExprTypeReal_list Tl),
  well_formed lR (map add_compatibility (list_var (length Tl))) (toList lR).
Proof. intros lR. rewrite <-(app_nil_l (toList lR)). unfold list_var.
fold (@length R nil). apply well_formed_list_var_aux.
Qed.

Fixpoint ArrayFree {Tl T} (t : ArithExpr Tl T) := match t with

  | Int                _             _
  | BinFl              _             _
  | Var                _     _                => True

  | Op                 _ _     _     t1 t2
  | OpExact            _       _     t1 t2
(*| Ldexp              _         _   t1 t2  *)=> ArrayFree t1 /\ ArrayFree t2

  | Fma                _             t1 t2 t3
  | FmaExact           _             t1 t2 t3 => ArrayFree t1 /\ ArrayFree t2 /\ ArrayFree t3

  | Let                _ _ _         t1 t2    => ArrayFree t1 /\ ArrayFree t2

  | ArrayAcc           _           _ _        => False

  | Nearbyint          _             t
  | FastNearbyint      _             t
  | FastNearbyintToInt _             t
  | TruncToInt         _             t
  | FloatInj           _             t
  | Sqrt               _ _           t
  | Assert             _ _         _ t
  | Postcond           _ _         _ t        => ArrayFree t
  end.

Fixpoint decomposeToCProp {Tl T} (t : ArithExpr Tl T) vars md := match t with

  | Int                _                n        => (CInt n, true, Void, CTrue)

  | BinFl              _                x        =>
    let f := Prim2B x in
    match f with
    | B754_zero   _       => (CBinFl 0 0, true, Void, CTrue)
    | B754_finite s m e _ => (CBinFl (if s then Z.neg m else Z.pos m) e, true, Void, CTrue)
    | _                   => (CInt 0%Z, false, Void, CTrue)
    end

  | Var                _                n        =>
    let (u, b) := nth n vars (CInt 0%Z, false) in (u, b, Void, CTrue)

  | Op                 _ T''   OP       t1 t2    =>
    let '(u1, b1, bt1, p1) := decomposeToCProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToCProp t2 vars md in
    let b  := andb b1 b2 in
    let bt := Node (if b2 then match OP with
                    | DIV => Leaf (NonZero u2)
                    | _     => Void end else Void) (Node bt1 bt2) in
    let p  := CAnd (if b2 then CTrue else match OP with
                    | DIV => CAtom (NonZero u2)
                    | _     => CTrue end) (CAnd p1 p2) in
    match T'' with
    | Integer  =>
      let t   := COp (ArithOpToCArithOp T'' OP) u1 u2 in
      let bt' := Node (if b then Leaf (InInt32 t) else Void) bt in
      let p'  := CAnd (if b then CTrue else CAtom (InInt32 t)) p in
      (t, b, bt', p')
    | BinFloat =>
      let t   := CRnd md (COp (ArithOpToCArithOp T'' OP) u1 u2) in
      let bt' := Node (if b then Leaf (InFloat64 t) else Void) bt in
      let p'  := CAnd (if b then CTrue else CAtom (InFloat64 t)) p in
      (t, b, bt', p')
    end

  | OpExact            _       OP       t1 t2    =>
    let '(u1, b1, bt1, p1) := decomposeToCProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToCProp t2 vars md in
    let t  := COp (ArithOpToCArithOp BinFloat OP) u1 u2 in
    let b  := andb b1 b2 in
    let bt := Node (if b then match OP with
                    | DIV => Node (Leaf (NonZero u2)) (Leaf (InFloat64 t))
                    | _     => Leaf (InFloat64 t)
                    end else Void) (Node bt1 bt2) in
    let p  := CAnd
             (CAnd (if b then CTrue else match OP with
                    | DIV => CAnd (CAtom (NonZero u2)) (CAtom (InFloat64 t))
                    | _     => CAtom (InFloat64 t)
                    end) (CAtom (RndExact md t))) (CAnd p1 p2) in
    (t, b, bt, p)

  | Fma                _                t1 t2 t3 =>
    let '(u1, b1, bt1, p1) := decomposeToCProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToCProp t2 vars md in
    let '(u3, b3, bt3, p3) := decomposeToCProp t3 vars md in
    let t  := CRnd md (COp CADD (COp CMUL u1 u2) u3) in
    let b  := andb (andb b1 b2) b3 in
    let bt := Node (if b then Leaf (InFloat64 t) else Void) (Node (Node bt1 bt2) bt3) in
    let p  := CAnd (if b then CTrue else CAtom (InFloat64 t)) (CAnd (CAnd p1 p2) p3) in
    (t, b, bt, p)

  | FmaExact           _                t1 t2 t3 =>
    let '(u1, b1, bt1, p1) := decomposeToCProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToCProp t2 vars md in
    let '(u3, b3, bt3, p3) := decomposeToCProp t3 vars md in
    let t  := COp CADD (COp CMUL u1 u2) u3 in
    let b  := andb (andb b1 b2) b3 in
    let bt := Node (if b then Leaf (InFloat64 t) else Void) (Node (Node bt1 bt2) bt3) in
    let p  := CAnd (if b then CTrue else CAtom (InFloat64 t)) (CAnd (CAnd p1 p2) p3) in
    (t, b, bt, CAnd p (CAtom (RndExact md t)))

  | Nearbyint          _                t        =>
    let '(u, b, bt, p) := decomposeToCProp t vars md in
    (CNearbyint u, b, bt, p)

  | FastNearbyint      _                t        =>
    let '(u, b, bt, p) := decomposeToCProp t vars md in
    let t   := CNearbyint u in
    let bt' := Node (if b then Leaf (InInt51 u) else Void) bt in
    let p'  := CAnd (if b then CTrue else CAtom (InInt51 u)) p in
    (t, b, bt', p')

  | FastNearbyintToInt _                t        =>
    let '(u, b, bt, p) := decomposeToCProp t vars md in
    let t   := CNearbyint u in
    let bt' := Node (if b then Leaf (InInt32 u) else Void) bt in
    let p'  := CAnd (if b then CTrue else CAtom (InInt32 u)) p in
    (t, b, bt', p')

  | TruncToInt         _                t        =>
    let '(u, b, bt, p) := decomposeToCProp t vars md in
    let t   := CTrunc u in
    let bt' := Node (if b then Leaf (InInt32 t) else Void) bt in
    let p'  := CAnd (if b then CTrue else CAtom (InInt32 t)) p in
    (t, b, bt', p')

  | FloatInj           _                t        =>
    let '(u, b, bt, p) := decomposeToCProp t vars md in
    let bt' := Node (if b then Leaf (InFloat64Int u) else Void) bt in
    let p'  := CAnd (if b then CTrue else CAtom (InFloat64Int u)) p in
    (u, b, bt', p')

(*| Ldexp              _            n   t1 t2    =>
    let '(u1, _, bt1, p1) := decomposeToCProp t1 vars md in
    let '(u2, _, bt2, p2) := decomposeToCProp t2 vars md in
    let t  := CRnd md (CLdexp u1 u2) in
    let bt := Node bt1 bt2 in
    let p  := CAnd (CAtom (LdexpControl n u1 u2)) (CAnd p1 p2) in
    (t, false, bt, p) *)

  | Sqrt               _ T''            t        =>
    let '(u, b, bt, p) := decomposeToCProp t vars md in
    let t   := CSqrt u in
    let bt' := Node (if b then Leaf (NonNeg u) else Void) bt in
    let p'  := CAnd (if b then CTrue else CAtom (NonNeg u)) p in
    match T'' with
    | Integer  => (CTrunc t, b, bt', p')
    | BinFloat => (CRnd md t, b, bt', p')
    end

  | ArrayAcc           _              _ _        => (CInt 0%Z, false, Void, CTrue)

  | Let                _ _ _            t1 t2    =>
    let '(u, b1, bt1, p1) := decomposeToCProp t1 vars              md in
    let '(t, b2, bt2, p2) := decomposeToCProp t2 ((u, b1) :: vars) md in
    let b := b2 in
    let bt := Node bt2 bt1 (* Preserving some sort of order *) in
    let p := CAnd p1 p2 in
    (t, b, bt, p)

  | Assert             _ _          _   t
  | Postcond           _ _          _   t        => decomposeToCProp t vars md
  end.

Lemma decomposeToCProp_correct {Tl T} :
  forall (t : ArithExpr Tl T), ArrayFree t ->
  forall (lM : evalExprTypeRounded_list Tl) vars l md,
  md <> mode_NA -> let lR := M2R_list lM in well_formed lR vars l ->
  let '(t', b, bt, p) := decomposeToCProp t vars md in
  let l' := BTreeToList bt in (
((b = true -> compatible t' = true) /\
 (evalCArithExpr2 t' l = evalReal t lR md)) /\
  forall k, compatible_atom (nth k l' (InInt32 (CInt 0))) = true) /\
 (CPropToProp (merge l' p) l -> wellBehaved t lM md).
Proof.
assert (Haux : forall l',
 (forall k, compatible_atom (nth k l' (InInt32 (CInt 0))) = true) <->
  map (fun p => compatible_atom p) l' = repeat true (length l')).
{ induction l'; [now split; [| intros _ [|]] |].
  destruct IHl' as [IHl'_0 IHl'_1]. simpl. split; intros H.
  - rewrite (H O). now rewrite IHl'_0; [| intros k; specialize (H (S k))].
  - inversion H as [[H0 H1]]. clear H. intros [| k]; [easy |].
    rewrite H0 in H1. rewrite H0. now apply IHl'_1. }
induction t as [| | Tl n | Tl T OP | Tl OP | | | | | | | | Tl T | | | |];
intros IAF lM vars l md Hmd lR Iwf.
16, 17: now apply IHt.
15: easy.
{ repeat split. now intros [|]. }
(* { repeat split. now intros [|]. } (* BinFl *) *)

all: simpl.

- now destruct Prim2B; (split; [| easy]);
   [simpl; rewrite Rmult_1_r | | | unfold B2R, F2R; destruct s; simpl];
   (split; [| destruct k]).


- set (d := nth n vars (CInt 0, false)). destruct_tuple_obj d.
  unfold d. clear d. split; [| easy]. split; [| now intros [|]].
  clear IAF. revert n vars l Iwf. induction Tl as [| T Tl];
  [now intros [|] [|] | intros [|] [| tb vars] l Hl; destruct_tuple_obj tb; simpl];
  [easy | now destruct Hl | easy |]. destruct lM as (xM, lM). apply (IHTl lM _ _ l).
  now simpl in Hl.


- destruct IAF as [IAF1 IAF2].
  specialize (IHt1 IAF1 lM vars l md Hmd Iwf).
  specialize (IHt2 IAF2 lM vars l md Hmd Iwf).
  revert IHt1 IHt2. fold lR.

  set (q1 := decomposeToCProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToCProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  unfold evalCArithExpr1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4]
         [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4].
  rewrite merge_decomp in IHt1_4, IHt2_4. rewrite Haux in IHt1_3, IHt2_3.

  destruct T; rewrite Haux.
  + split.
    { destruct bq1, bq2; (split; [split | unfold BTreeToList; simpl BTreeToList_aux]);
     [intros _ | | | easy | | | easy | | | easy | |].
      { apply andb_true_intro.
        now split; [apply IHt1_1 | apply IHt2_1]. }
      1, 3, 5, 7: now destruct OP; rewrite <-IHt1_2, <-IHt2_2.
      all:  rewrite (BTreeToList_aux_concat lq1);
            rewrite (BTreeToList_aux_concat lq2).
      2, 4: rewrite 2app_length, 2repeat_app, 2map_app;
            rewrite IHt1_3, IHt2_3; easy.
      2:    destruct OP; simpl; [| | | rewrite IHt2_1 by easy];
            rewrite 2app_length, 2repeat_app, 2map_app;
            rewrite IHt1_3, IHt2_3; easy.
      destruct OP; simpl; rewrite IHt1_1, IHt2_1 by easy; simpl;
      rewrite 2app_length, 2repeat_app, 2map_app;
      rewrite IHt1_3, IHt2_3; easy. }
    rewrite merge_decomp. unfold BTreeToList. simpl.
    rewrite 3BTreeToList_aux_concat.
    rewrite 3merge_app. intros [[HOP [Hm1 [Hm2 Hm3]]] [HP [HP1 [HP2 HP3]]]].
    fold (BTreeToList lq2) in Hm2.
    split; [now apply IHt1_4; split | split; [now apply IHt2_4; split |]].
    destruct OP; [.. | split]; (destruct bq1, bq2; simpl in HOP;
     [destruct HOP as [H HOP] | | |]). all: simpl in *.
    17-20: now apply neq_IZR; fold (M2R (evalRounded t2 lM md));
      rewrite <-evalReal_evalRounded; fold lR; rewrite <-IHt2_2; destruct Hm1.
    1-4: rewrite plus_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: rewrite minus_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: rewrite mult_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: rewrite <-Ztrunc_div_; change Ztrunc with (round_mode mode_ZR);
      rewrite <-Rrnd.nearbyint_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded; fold lR;
      now rewrite <-IHt1_2, <-IHt2_2.
  + split.
    { destruct bq1, bq2; (split; [split | unfold BTreeToList; simpl BTreeToList_aux]);
     [intros _ | | | easy | | | easy | | | easy | |].
      { destruct md; [.. | easy]; apply andb_true_intro;
        now split; [apply IHt1_1 | apply IHt2_1]. }
      1, 3, 5, 7: now destruct OP; rewrite <-IHt1_2, <-IHt2_2.
      all:  rewrite (BTreeToList_aux_concat lq1);
            rewrite (BTreeToList_aux_concat lq2).
      2, 4: rewrite 2app_length, 2repeat_app, 2map_app;
            rewrite IHt1_3, IHt2_3; easy.
      2:    destruct OP; simpl; [| | | rewrite IHt2_1 by easy];
            rewrite 2app_length, 2repeat_app, 2map_app;
            rewrite IHt1_3, IHt2_3; easy.
      destruct OP; simpl; rewrite IHt1_1, IHt2_1 by easy; simpl;
      rewrite 2app_length, 2repeat_app, 2map_app;
      rewrite IHt1_3, IHt2_3; destruct md; easy. }
    rewrite merge_decomp. unfold BTreeToList. simpl.
    rewrite 3BTreeToList_aux_concat.
    rewrite 3merge_app. intros [[HOP [Hm1 [Hm2 Hm3]]] [HP [HP1 [HP2 HP3]]]].
    fold (BTreeToList lq2) in Hm2.
    split; [now apply IHt1_4; split | split; [now apply IHt2_4; split |]].
    destruct OP; [.. | split]; (destruct bq1, bq2; simpl in HOP;
     [destruct HOP as [H HOP] | | |]). all: simpl in *.
    17-20: now fold (M2R (evalRounded t2 lM md));
      rewrite <-evalReal_evalRounded; fold lR; rewrite <-IHt2_2; destruct Hm1.
    1-4: fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalReal_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: fold (M2R (evalRounded t1 lM md)); fold (M2R (evalRounded t2 lM md));
      rewrite <-2evalReal_evalRounded; fold lR;
      now rewrite <-IHt1_2, <-IHt2_2.


- destruct IAF as [IAF1 IAF2].
  specialize (IHt1 IAF1 lM vars l md Hmd Iwf).
  specialize (IHt2 IAF2 lM vars l md Hmd Iwf).
  revert IHt1 IHt2. fold lR.

  set (q1 := decomposeToCProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToCProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  unfold evalCArithExpr1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4]
         [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4].
  rewrite merge_decomp in IHt1_4, IHt2_4. rewrite Haux in IHt1_3, IHt2_3.

  rewrite Haux. split.
  { destruct bq1, bq2; (split; [split | unfold BTreeToList; simpl BTreeToList_aux]);
   [intros _ | | | easy | | | easy | | | easy | |].
    { destruct md; [.. | easy]; apply andb_true_intro;
      now split; [apply IHt1_1 | apply IHt2_1]. }
    1, 3, 5, 7: now destruct OP; rewrite <-IHt1_2, <-IHt2_2.
    all:  rewrite (BTreeToList_aux_concat lq1);
          rewrite (BTreeToList_aux_concat lq2).
    2, 4: rewrite 2app_length, 2repeat_app, 2map_app;
          rewrite IHt1_3, IHt2_3; easy.
    2:    destruct OP; simpl; rewrite 2app_length, 2repeat_app, 2map_app;
          rewrite IHt1_3, IHt2_3; easy.
    destruct OP; simpl; rewrite IHt1_1, IHt2_1 by easy; simpl;
    rewrite 2app_length, 2repeat_app, 2map_app;
    rewrite IHt1_3, IHt2_3; destruct md; easy. }
  rewrite merge_decomp. unfold BTreeToList. simpl.
  rewrite 3BTreeToList_aux_concat.
  rewrite 3merge_app. intros [[HOP [Hm1 Hm2]] [[HP HP3] [HP1 HP2]]].
  fold (BTreeToList lq2) in Hm2. destruct OP; [| | | split].
  5: { fold (M2R (evalRounded t2 lM md)). rewrite <-evalReal_evalRounded. fold lR.
       rewrite <-IHt2_2. destruct bq1, bq2; simpl in HOP;
        [destruct HOP as [[_ H] HOP] | | |]; now simpl in HP. }
  1-4: split; [now apply IHt1_4; split | split; [now apply IHt2_4; split | split]].
  1-8: fold (M2R (evalRounded t1 lM md)). 1-8: fold (M2R (evalRounded t2 lM md)).
  1-8: rewrite <-2evalReal_evalRounded. 1-8: fold lR.
  1-8: rewrite <-IHt1_2, <-IHt2_2.
  1, 3, 5, 7: destruct bq1, bq2; simpl in *; now destruct HOP.
  1-4: now simpl in HP3.


- destruct IAF as [IAF1 [IAF2 IAF3]].
  specialize (IHt1 IAF1 lM vars l md Hmd Iwf).
  specialize (IHt2 IAF2 lM vars l md Hmd Iwf).
  specialize (IHt3 IAF3 lM vars l md Hmd Iwf).
  revert IHt1 IHt2 IHt3.

  set (q1 := decomposeToCProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToCProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).
  set (q3 := decomposeToCProp t3 vars md).
  destruct_tuple_obj q3.
  set (pq3 := snd q3). set (lq3 := snd (fst q3)). set (bq3 := snd (fst (fst q3))).
  set (tq3 := fst (fst (fst q3))).

  unfold evalCArithExpr1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4]
         [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4]
         [[[IHt3_1 IHt3_2] IHt3_3] IHt3_4].
  rewrite merge_decomp in IHt1_4, IHt2_4, IHt3_4.
  rewrite Haux in IHt1_3, IHt2_3, IHt3_3.

  rewrite Haux. split.
  { destruct bq1, bq2, bq3; (split; [split | unfold BTreeToList; simpl BTreeToList_aux]);
   [intros _ | | | easy | | | easy | | | easy | | | easy | | | easy | | | easy | | | easy | |].
    { destruct md; [.. | easy]; apply andb_true_intro; (split; [| now apply IHt3_1]);
      apply andb_true_intro; now split; [apply IHt1_1 | apply IHt2_1]. }
    2: simpl; rewrite IHt1_1, IHt2_1, IHt3_1 by easy; simpl.
    2, 4, 6, 8, 10, 12, 14, 16: rewrite (BTreeToList_aux_concat lq1);
                                rewrite (BTreeToList_aux_concat lq2);
                                rewrite (BTreeToList_aux_concat lq3);
                                rewrite 3app_length, 3repeat_app, 3map_app;
                                rewrite IHt1_3, IHt2_3, IHt3_3; destruct md; easy.
    all: now unfold lR; rewrite <-IHt1_2, <-IHt2_2, <-IHt3_2. }
  rewrite merge_decomp. unfold BTreeToList. simpl.
  rewrite 3BTreeToList_aux_concat.
  rewrite 3merge_app. intros [[HOP [Hm1 [Hm2 Hm3]]] [HP [[HP1 HP2] HP3]]].
  fold (BTreeToList lq3) in Hm3.
  split; [now apply IHt1_4; split | split;
         [now apply IHt2_4; split | split;
         [now apply IHt3_4; split |]]].
  destruct bq1, bq2, bq3; simpl in HOP; [destruct HOP as [_ HOP] | | | | | | |].
  1-8: simpl in HP. 1-8: fold (M2R (evalRounded t1 lM md)).
  1-8: fold (M2R (evalRounded t2 lM md)). 1-8: fold (M2R (evalRounded t3 lM md)).
  1-8: rewrite <-3evalReal_evalRounded.
  1-8: now rewrite <-IHt1_2, <-IHt2_2, <-IHt3_2.


- destruct IAF as [IAF1 [IAF2 IAF3]].
  specialize (IHt1 IAF1 lM vars l md Hmd Iwf).
  specialize (IHt2 IAF2 lM vars l md Hmd Iwf).
  specialize (IHt3 IAF3 lM vars l md Hmd Iwf).
  revert IHt1 IHt2 IHt3.

  set (q1 := decomposeToCProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToCProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).
  set (q3 := decomposeToCProp t3 vars md).
  destruct_tuple_obj q3.
  set (pq3 := snd q3). set (lq3 := snd (fst q3)). set (bq3 := snd (fst (fst q3))).
  set (tq3 := fst (fst (fst q3))).

  unfold evalCArithExpr1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4]
         [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4]
         [[[IHt3_1 IHt3_2] IHt3_3] IHt3_4].
  rewrite merge_decomp in IHt1_4, IHt2_4, IHt3_4.
  rewrite Haux in IHt1_3, IHt2_3, IHt3_3.

  rewrite Haux. split.
  { destruct bq1, bq2, bq3; (split; [split | unfold BTreeToList; simpl BTreeToList_aux]);
   [intros _ | | | easy | | | easy | | | easy | | | easy | | | easy | | | easy | | | easy | |].
    { destruct md; [.. | easy]; apply andb_true_intro; (split; [| now apply IHt3_1]);
      apply andb_true_intro; now split; [apply IHt1_1 | apply IHt2_1]. }
    2: simpl; rewrite IHt1_1, IHt2_1, IHt3_1 by easy; simpl.
    2, 4, 6, 8, 10, 12, 14, 16: rewrite (BTreeToList_aux_concat lq1);
                                rewrite (BTreeToList_aux_concat lq2);
                                rewrite (BTreeToList_aux_concat lq3);
                                rewrite 3app_length, 3repeat_app, 3map_app;
                                rewrite IHt1_3, IHt2_3, IHt3_3; destruct md; easy.
    all: now unfold lR; rewrite <-IHt1_2, <-IHt2_2, <-IHt3_2. }
  rewrite merge_decomp. unfold BTreeToList. simpl.
  rewrite 3BTreeToList_aux_concat.
  rewrite 3merge_app. intros [[HOP [Hm1 [Hm2 Hm3]]] [[HP [[HP1 HP2] HP3]] HP4]].
  fold (BTreeToList lq3) in Hm3.
  split; [now apply IHt1_4; split | split;
         [now apply IHt2_4; split | split;
         [now apply IHt3_4; split |]]].
  fold (M2R (evalRounded t1 lM md)). fold (M2R (evalRounded t2 lM md)).
  fold (M2R (evalRounded t3 lM md)). rewrite <-3evalReal_evalRounded.
  unfold Rrnd.fma. rewrite <-IHt1_2, <-IHt2_2, <-IHt3_2.
  split; [| easy].
  now destruct bq1, bq2, bq3; simpl in HOP; [destruct HOP as [_ HOP] | | | | | | |].


- specialize (IHt IAF lM vars l md Hmd Iwf). revert IHt.

  set (q := decomposeToCProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux. split; [| assumption].
  now destruct bq; simpl; (split; [split | assumption]); [assumption | | easy |];
  rewrite IHt_2.


- specialize (IHt IAF lM vars l md Hmd Iwf). simpl in IHt. revert IHt.

  set (q := decomposeToCProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux.
  destruct bq; simpl; (split; [split; [split; [assumption | now rewrite IHt_2] |] |]);
   [rewrite IHt_1 by easy; now apply f_equal | | assumption | unfold BTreeToList];
    rewrite merge_decomp; cbn; rewrite IHt_2, evalReal_evalRounded; simpl;
   [intros [H0 [[_ H1] [H2 H3]]] | intros [H0 [[H2 H3] H1]]];
    (split; [| easy]); apply IHt_4; rewrite merge_decomp; split; assumption.


- specialize (IHt IAF lM vars l md Hmd Iwf). simpl in IHt. revert IHt.

  set (q := decomposeToCProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux.
  destruct bq; simpl; (split; [split; [split; [assumption | now rewrite IHt_2] |] |]);
   [rewrite IHt_1 by easy; now apply f_equal | | assumption | unfold BTreeToList];
    rewrite merge_decomp; cbn; rewrite IHt_2, evalReal_evalRounded; simpl;
   [intros [H0 [[_ H1] [H2 H3]]] | intros [H0 [[H2 H3] H1]]];
    (split; [| easy]); apply IHt_4; rewrite merge_decomp; split; assumption.



- specialize (IHt IAF lM vars l md Hmd Iwf). simpl in IHt. revert IHt.

  set (q := decomposeToCProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux.
  destruct bq; simpl; (split; [split; [split; [assumption | now rewrite IHt_2] |] |]);
   [rewrite IHt_1 by easy; now apply f_equal | | assumption | unfold BTreeToList];
    rewrite merge_decomp; cbn; unfold Rrnd.trunc;
    rewrite IHt_2, round_FIX_IZR, evalReal_evalRounded; simpl;
   [intros [H0 [[_ H1] [H2 H3]]] | intros [H0 [[H2 H3] H1]]]; rewrite <-opp_IZR in H2;
    apply le_IZR in H2, H3; (split; [| easy]); apply IHt_4; rewrite merge_decomp; split; assumption.


- specialize (IHt IAF lM vars l md Hmd Iwf). simpl in IHt. revert IHt.

  set (q := decomposeToCProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux. split; [split; [easy |] |].
  + destruct bq; simpl; unfold BTreeToList in IHt_3; [now rewrite IHt_1, IHt_3 |].
    now unfold BTreeToList.
  + intros H. destruct bq; rewrite merge_decomp in H; simpl in H;
    destruct H as [H1 [H3 H4]]; rewrite merge_decomp in H1;
    destruct H1 as [H1 H2]; simpl in H1, H2; destruct H2;
    (split; [now apply IHt_4; unfold BTreeToList; rewrite merge_decomp |]);
    fold (M2R (evalRounded t lM md)); rewrite <-evalReal_evalRounded; now rewrite <-IHt_2.

- specialize (IHt IAF lM vars l md Hmd Iwf). simpl in IHt. revert IHt.

  set (q := decomposeToCProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4]. rewrite Haux in IHt_3.

  destruct T; rewrite Haux.
  + split; [split; [split; [easy | now simpl; unfold lR; rewrite IHt_2] |] |].
    * destruct bq; simpl; unfold BTreeToList in IHt_3; [now rewrite IHt_1, IHt_3 |].
      now unfold BTreeToList.
    * intros H. destruct bq; rewrite merge_decomp in H; simpl in H;
      destruct H as [H1 [H3 H4]]; rewrite merge_decomp in H1;
      destruct H1 as [H1 H2]; simpl in H1, H2; destruct H2;
      (split; [now apply IHt_4; unfold BTreeToList; rewrite merge_decomp |]);
      fold (M2R (evalRounded t lM md)); rewrite <-evalReal_evalRounded; rewrite <-IHt_2; lra.
  + split; [split; [split; [now destruct md | now simpl; unfold lR; rewrite IHt_2] |] |].
    * destruct bq; simpl; unfold BTreeToList in IHt_3; [now rewrite IHt_1, IHt_3 |].
      now unfold BTreeToList.
    * intros H. destruct bq; rewrite merge_decomp in H; simpl in H;
      destruct H as [H1 [H3 H4]]; rewrite merge_decomp in H1;
      destruct H1 as [H1 H2]; simpl in H1, H2; destruct H2;
      (split; [now apply IHt_4; unfold BTreeToList; rewrite merge_decomp |]);
      fold (M2R (evalRounded t lM md)); rewrite <-evalReal_evalRounded; rewrite <-IHt_2; lra.


- set (xM := evalRounded t1 lM md). set (xR := evalReal t1 lR md).
  destruct IAF as [IAF1 IAF2].
  specialize (IHt1 IAF1 lM vars l md Hmd Iwf). revert IHt1.

  set (q1 := decomposeToCProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).

  unfold evalCArithExpr1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4].

  specialize (IHt2 IAF2 (xM, lM) ((tq1, bq1) :: vars) l md Hmd). simpl in IHt2.
  assert (H : (bq1 = true -> compatible tq1 = true)
           /\ evalCArithExpr2 tq1 l = xR
           /\ well_formed lR vars l).
  { now repeat split. }
  unfold xR, lR in H. rewrite evalReal_evalRounded in H.
  fold xM in H. specialize (IHt2 H). revert IHt2.

  set (q2 := decomposeToCProp t2 ((tq1, bq1) :: vars) md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  intros [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4].
  rewrite merge_decomp in IHt1_4, IHt2_4. rewrite Haux in IHt1_3, IHt2_3.

  rewrite Haux. split.
  { split; [split; [easy |]; rewrite IHt2_2; unfold xM, xR, lR; now rewrite evalReal_evalRounded |].
    unfold BTreeToList. simpl.
    rewrite (BTreeToList_aux_concat lq1).
    rewrite (BTreeToList_aux_concat lq2).
    rewrite 2app_length, 2repeat_app, 2map_app.
    now rewrite IHt1_3, IHt2_3. }
  rewrite merge_decomp. unfold BTreeToList. simpl. rewrite 2BTreeToList_aux_concat.
  rewrite 2merge_app. intros [[Hm1 [Hm2 _]] [HP1 HP2]].
  split; [now apply IHt1_4 | now apply IHt2_4].
Qed.


Definition extractCProp {Tl T} (t : ArithExpr Tl T) md :=
  let '(_, _, l, p) :=
    decomposeToCProp t (map add_compatibility (list_var (length Tl))) md
  in (l, simplifyCProp p).

Corollary extractCProp_correct {Tl T} :
  forall (t : ArithExpr Tl T), ArrayFree t ->
  forall (lM : evalExprTypeRounded_list Tl) md,
  md <> mode_NA -> let lR := M2R_list lM in
  let '(bt, p) := extractCProp t md in let l' := BTreeToList bt in
 (forall k, compatible_atom (nth k l' (InInt32 (CInt 0))) = true) /\
 (CPropToProp (merge l' p) (toList lR) -> wellBehaved t lM md).
Proof. intros t IAF lM md Hmd lR. unfold extractCProp. set (l := toList lR).
set (vars := (map add_compatibility (list_var (length Tl)))).
generalize (decomposeToCProp_correct t IAF lM vars l md Hmd).
set (q := decomposeToCProp _ _ _). destruct_tuple_obj q.
unfold vars. unfold l at 1. intros H. specialize (H (well_formed_list_var lR)).
rewrite merge_decomp in H. rewrite merge_decomp. rewrite simplifyCProp_correct.
split; apply H.
Qed.



(* Try to solve compatible goals using Interval *)

Module Faux := SpecificFloat BigIntRadix2.
Module Iaux := FloatIntervalFull Faux.
Module IH := IntervalTacticAux Iaux.

Definition prec := Faux.PtoP 80.
Definition degree := 10%nat.

Definition AtomToGoal g := match g with
  | InInt32      _ => Reify.Glele (Tree.Econst (Tree.Int (- Int32.N / 2))) (Tree.Econst (Tree.Int (Int32.N / 2 - 1)))
  | InInt51      _ => Reify.Glele (Tree.Econst (Tree.Int (-2251799813685248))) (Tree.Econst (Tree.Int 2251799813685247))
  | InInt64      _ => Reify.Glele (Tree.Econst (Tree.Int (- Int64.N / 2))) (Tree.Econst (Tree.Int (Int64.N / 2 - 1)))
  | InFloat64    _ => Reify.Gabsle true (* (Tree.Econst (Tree.Int ((2 ^ 53 - 1) * 2 ^ 971))) *) (Tree.Ebinary Tree.Mul
   (Tree.Ebinary Tree.Sub (Tree.Econst (Tree.Bpow 2 53)) (Tree.Econst (Tree.Int 1)))
   (Tree.Econst (Tree.Bpow 2 971)))
  | InFloat64Int _ => Reify.Gabsle true (Tree.Econst (Tree.Bpow 2 53))
  | NonZero      _ => Reify.Gne true (Tree.Econst (Tree.Int 0))
  | NonNeg       _ => Reify.Gge true (Tree.Econst (Tree.Int 0))
  | _ => Reify.Glt (Tree.Evar O) (*
    goals that we will not solve using interval.
    TODO: think harder about the case LdExpControl as we may be able to use interval to solve this one
    *)
  end.

Definition getCArithExpr g := match g with
  | InInt32 t | InInt64 t | InInt51 t | InFloat64 t
  | InFloat64Int t | NonZero t | NonNeg t => t
  | _                                     => CInt 0 (*
    goals that we will not solve using interval.
    TODO: think harder about the case LdExpControl as we may be able to use interval to solve this one
    *)
  end.

Lemma AtomToGoal_correct : forall i a l,
   compatible_atom a = true ->
   Interval.contains (Iaux.convert i)
    (Xreal.Xreal (Tree.eval (CArithExprToTree (getCArithExpr a)) l)) ->
   IH.R.eval_goal_bnd prec (AtomToGoal a) i = true ->
   AtomToProp a l.
Proof. intros i a l Ha Hcont Heg. generalize IH.R.eval_goal_bnd_correct. intros H.
specialize (H prec (AtomToGoal a) i (Tree.eval (CArithExprToTree (getCArithExpr a)) l) Hcont Heg).
clear Hcont Heg. destruct a; simpl in *; [| | | unfold Rrnd.maxval;rewrite minus_IZR | | | | easy..];
  apply (compatible_correct _ l) in Ha; now rewrite <-Ha.
Qed.

Fixpoint compareResults goals results := match goals with
  | nil => nil
  | g :: goals' => match results with
    | nil => nil (* should not happen in normal use *)
    | res :: results' => IH.R.eval_goal_bnd prec g res :: compareResults goals' results'
    end
  end.

Fixpoint par_construct Al (bl : list bool) := match Al with
  | nil      => CTrue
  | p :: Al' => match bl with
    | nil      => CTrue
    | b :: bl' => let P := par_construct Al' bl' in
      if b then (CAnd P (CAtom p)) else P
    end
  end.

Fixpoint par_mergerest Al (bl : list bool) P := match Al with
  | nil      => P
  | p :: Al' => match bl with
    | nil      => merge Al' (CAnd P (CAtom p))
    | b :: bl' => let P' := if b then P else (CAnd P (CAtom p)) in
      par_mergerest Al' bl' P'
    end
  end.

Lemma par_mergerest_decomp : forall Al bl P l,
  CPropToProp (par_mergerest Al bl P) l <->
  CPropToProp (par_mergerest Al bl CTrue) l /\ CPropToProp P l.
Proof. induction Al; [easy |].
intros [| [|] bl] P l; simpl; [| apply IHAl |].
- rewrite merge_decomp. rewrite (merge_decomp _ (CAnd _ _) _). now simpl.
- rewrite IHAl. rewrite (IHAl _ (CAnd _ _) _). now simpl.
Qed.

Lemma par_construct_mergerest : forall Al bl P l,
  CPropToProp (par_construct Al bl) l /\ CPropToProp (par_mergerest Al bl P) l <->
  CPropToProp (merge Al P) l.
Proof. induction Al; intros bl P l; simpl; destruct bl; [easy.. |].
rewrite par_mergerest_decomp, merge_decomp.
now case b; simpl; rewrite <-(IHAl bl).
Qed.

Definition generateCProp {Tl T}  (t : ArithExpr Tl T) md vars hyps :=
  let (tointerval, unsolvable) := extractCProp t md in
  let tointerval := BTreeToList tointerval in
  let lexpr := map (fun p => CArithExprToTree (getCArithExpr p)) tointerval in
  match extract_list lexpr vars with
  | Eabort => merge tointerval unsolvable
  | Eprog prog consts =>
    let goals := map (fun p => AtomToGoal p) tointerval in
    let ieval := fun xi => IH.A.BndValuator.eval prec prog xi in
    let bounds := IH.compute_inputs prec hyps consts in
    let results := ieval bounds in
    let compared := compareResults goals results in
    par_mergerest tointerval compared unsolvable end.

Theorem generateCProp_correct {Tl T} :
  forall (t : ArithExpr Tl T), ArrayFree t ->
  forall (lM : evalExprTypeRounded_list Tl) md hyps P,
  md <> mode_NA -> let lR := M2R_list lM in let l := toList lR in
    generateCProp t md (length l) hyps = P ->
    Reify.eval_hyps hyps l (CPropToProp P l -> wellBehaved t lM md).
Proof. intros t IAF lM md hyps P Hmd lR l <-.
apply (IH.R.eval_hyps_bnd_correct prec).
generalize (extractCProp_correct t IAF lM md). unfold generateCProp.
set (p0 := extractCProp _ _). destruct_tuple_obj p0.
set (unsolved := snd p0).
intros [Hm Hm'] Hh Hg; [easy |]. apply Hm'. revert Hm Hg.
set (tointerval := BTreeToList (fst p0)).
set (goals := map (fun p => AtomToGoal p) tointerval).
set (lexpr := map (fun p => CArithExprToTree (getCArithExpr p)) tointerval).
generalize (extract_list_correct lexpr l).
destruct extract_list as [|prog consts]; [easy |].
intros H Hm Hg. eapply par_construct_mergerest. revert Hm Hg.
set (ieval := fun xi => IH.A.BndValuator.eval prec prog xi).
set (bounds := IH.compute_inputs prec hyps consts).
set (results := ieval bounds). set (compared := compareResults goals results).
intros Hm Hg. split; [| exact Hg]. fold ieval. fold bounds.
apply (IH.app_merge_hyps_eval_bnd _ _ _ consts) in Hh. fold bounds in Hh.
set (l' := l ++ map (fun c : Tree.expr => Tree.eval c nil) consts).
fold l' in Hh. clear Hm' Hg.
generalize (IH.A.BndValuator.eval_correct' prec prog bounds l' Hh).
destruct Hh as [Hl Hh]. intros H'.
clearbody tointerval. clear p0 unsolved results compared.
unfold goals. clear goals. unfold ieval. clear ieval. clear T t IAF.
fold lR l. clearbody l. clear Tl lM lR. clearbody bounds.
unfold eval_real_nth in H. fold l' in H. revert H'.
generalize (IH.A.BndValuator.eval prec prog bounds).
intros l0 H'.
cut (forall k,
  nth k (compareResults (map (fun p : Atom => AtomToGoal p) tointerval) l0) false = true ->
  AtomToProp (nth k tointerval (InInt32 (CInt 0))) l).
{ clear. revert l0. induction tointerval; [easy |].
intros l0 H''. simpl. destruct l0 as [| i l0]; [easy |].
simpl in H''. generalize (H'' O). destruct IH.R.eval_goal_bnd; intros Ha.
- split; [| now apply Ha]. apply IHtointerval. intros k.
  apply (H'' (S k)).
- apply IHtointerval. intros k.
  apply (H'' (S k)). }
intros k Hk. destruct (Nat.lt_ge_cases k (length tointerval)) as [Hkl | Hkl].
2: { rewrite nth_overflow in Hk; [easy |]. clear -Hkl. revert l0 k Hkl.
  induction tointerval; [easy |]. simpl. intros l0 k. destruct l0 as [| i l0];
  [intros _; apply Nat.le_0_l |]. intros Hkl. simpl. destruct k as [| k];
  [easy |]. apply le_n_S, (IHtointerval l0 k). now apply le_S_n in Hkl. }
apply AtomToGoal_correct with (i := (nth k l0 Iaux.nai)) (1 := (Hm k)).
- specialize (H' k). rewrite H in H' by (unfold lexpr; now rewrite map_length).
  unfold lexpr in H'. rewrite (Eval.nth_map_lt (InInt32 (CInt 0))) in H' by easy.
  apply H'.
- clear -Hk Hkl. revert l0 k Hk Hkl. induction tointerval; [easy |]. simpl.
  intros [| i l0]; [now intros [|] |]. simpl.
  intros [| k]; [easy |]. simpl. intros Hk Hkl. apply IHtointerval; [easy |].
  now apply Nat.succ_lt_mono.
Qed.

Definition generateCProp_taylor {Tl T}  (t : ArithExpr Tl T) md vars hyps :=
  let (tointerval, unsolvable) := extractCProp t md in
  let tointerval := BTreeToList tointerval in
  let lexpr := map (fun p => CArithExprToTree (getCArithExpr p)) tointerval in
  match extract_list lexpr vars with
  | Eabort => merge tointerval unsolvable
  | Eprog prog consts =>
    let goals := map (fun p => AtomToGoal p) tointerval in
    let bounds := IH.compute_inputs prec hyps consts in
    match bounds with
    | nil     => merge tointerval unsolvable
    | xi :: li =>
      let li := IH.A.TaylorValuator.TM.var :: map IH.A.TaylorValuator.TM.const li in
      let polys := (IH.A.TaylorValuator.eval prec degree xi prog li) in
      let results := map (fun p => IH.A.TaylorValuator.TM.eval (prec, degree) p xi xi) polys in
    let compared := compareResults goals results in
    par_mergerest tointerval compared unsolvable
    end end.

Theorem generateCProp_taylor_correct {Tl T} :
  forall (t : ArithExpr Tl T), ArrayFree t ->
  forall (lM : evalExprTypeRounded_list Tl) md hyps P,
  md <> mode_NA -> let lR := M2R_list lM in let l := toList lR in
    generateCProp_taylor t md (length l) hyps = P ->
    Reify.eval_hyps hyps l (CPropToProp P l -> wellBehaved t lM md).
Proof. intros t IAF lM md hyps P Hmd lR l <-.
apply (IH.R.eval_hyps_bnd_correct prec).
generalize (extractCProp_correct t IAF lM md). unfold generateCProp_taylor.
set (p0 := extractCProp _ _). destruct_tuple_obj p0.
set (unsolved := snd p0).
intros [Hm Hm'] Hh Hg; [easy |]. apply Hm'. revert Hm Hg.
set (tointerval := BTreeToList (fst p0)).
set (goals := map (fun p => AtomToGoal p) tointerval).
set (lexpr := map (fun p => CArithExprToTree (getCArithExpr p)) tointerval).
generalize (extract_list_correct lexpr l).
destruct extract_list as [|prog consts]; [easy |]. intros H.
unfold eval_real_nth in H.
set (bounds := IH.compute_inputs prec hyps consts).
destruct bounds as [| xi li] eqn:Hbounds; [easy |].
intros Hm Hg. eapply par_construct_mergerest.
split; [| exact Hg].
apply (IH.app_merge_hyps_eval_bnd _ _ _ consts) in Hh. fold bounds in Hh.
set (l' := l ++ map (fun c : Tree.expr => Tree.eval c nil) consts).
fold l' in H, Hh. clear Hm' Hg. rewrite Hbounds in Hh. destruct Hh as [Hl Hh].
destruct l' as [| x l']; [easy |].
assert (Hh' : IH.A.contains_all li l').
{ split.
  - now injection Hl.
  - intros n. apply (Hh (S n)). }
generalize (fun n => IH.A.TaylorValuator.eval_correct prec degree prog li l' Hh' n xi xi x (Hh 0%nat)).
intros H'. clearbody tointerval. clear p0 unsolved.
unfold goals. clear goals. clear T t IAF.
fold lR l. clearbody l. clear Tl lM lR. clearbody bounds.
revert H'.
generalize ((IH.A.TaylorValuator.eval prec degree xi prog
               (IH.A.TaylorValuator.TM.var
                :: map IH.A.TaylorValuator.TM.const li))).
intros l0 H'.
set (l0' := (map
           (fun p : IH.A.TaylorValuator.TM.T =>
            IH.A.TaylorValuator.TM.eval (prec, degree) p xi xi) l0)).
cut (forall k,
  nth k (compareResults (map (fun p : Atom => AtomToGoal p) tointerval) l0') false = true ->
  AtomToProp (nth k tointerval (InInt32 (CInt 0))) l).
{ generalize l0'. clear. induction tointerval; [easy |].
intros l0' H''. simpl. destruct l0' as [| i l0']; [easy |].
simpl in H''. generalize (H'' O). destruct IH.R.eval_goal_bnd; intros Ha.
- split; [| now apply Ha]. apply IHtointerval. intros k.
  apply (H'' (S k)).
- apply IHtointerval. intros k.
  apply (H'' (S k)). }
intros k Hk. destruct (Nat.lt_ge_cases k (length tointerval)) as [Hkl | Hkl].
2: { rewrite nth_overflow in Hk; [easy |]. clearbody l0'. clear -Hkl. revert l0' k Hkl.
  induction tointerval; [easy |]. simpl. intros l0' k Hkl. destruct l0' as [| i l0'];
  [apply Nat.le_0_l |]. simpl. destruct k as [| k];
  [easy |]. apply le_n_S, (IHtointerval l0' k). now apply le_S_n in Hkl. }
apply AtomToGoal_correct with (i := (nth k l0' Iaux.nai)) (1 := (Hm k)).
- specialize (H' k). rewrite H in H' by (unfold lexpr; now rewrite map_length).
  unfold lexpr in H'. rewrite (Eval.nth_map_lt (InInt32 (CInt 0))) in H' by easy.
  revert Hk Hkl. unfold l0'. clear -H'. revert tointerval l0 H'. induction k.
  + intros [| a tointerval] [| x0 l0]; easy.
  + intros [| a tointerval] [| x0 l0]; try easy. simpl. intros H' Hk Hkl.
    apply IHk. 3: now apply Nat.succ_lt_mono. easy. easy.
- clearbody l0'. clear -Hk Hkl. revert l0' k Hk Hkl. induction tointerval; [easy |]. simpl.
  intros [| i l0']; [now intros [|] |]. simpl.
  intros [| k]; [easy |]. simpl. intros Hk Hkl. apply IHtointerval; [easy |].
  now apply Nat.succ_lt_mono.
Qed.
