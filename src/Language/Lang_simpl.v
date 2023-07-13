From Coq Require Import Bool Reals List Lia Lra.
From Flocq Require Import Core BinarySingleNaN Operations.

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



(* Computable real number expressions *)

Inductive ProcessedOp := PADD | PSUB | PMUL | PFLTDIV | PINTDIV.

Definition ArithOpToPOp T OP := match OP with
  | ADD => PADD
  | SUB => PSUB
  | MUL => PMUL
  | DIV => match T with
    | Integer  => PINTDIV
    | BinFloat => PFLTDIV
    end
  end.

Definition rounding_mode_of_mode md := match md with
  | mode_NE | mode_NA => Basic.rnd_NE
  | mode_ZR           => Basic.rnd_ZR
  | mode_DN           => Basic.rnd_DN
  | mode_UP           => Basic.rnd_UP
end.

Inductive ProcessedTree :=
  | PInt: Z -> ProcessedTree
  | PBinFl: Z -> Z -> ProcessedTree
  | PVar: nat -> ProcessedTree
  | POp: ProcessedOp -> ProcessedTree -> ProcessedTree -> ProcessedTree
  | PRnd: mode -> ProcessedTree -> ProcessedTree
  | PNearbyint: ProcessedTree -> ProcessedTree
  | PTrunc: ProcessedTree -> ProcessedTree
  | PLdexp: ProcessedTree -> ProcessedTree -> ProcessedTree
  | PSqrt: ProcessedTree -> ProcessedTree.

Fixpoint PTreeToTree t := match t with
  | PInt n => Tree.Econst (Tree.Int n)
  | PBinFl n1 n2 => Tree.Ebinary Tree.Mul (Tree.Econst (Tree.Int n1)) (Tree.Econst (Tree.Bpow 2 n2))
  | PVar n => Tree.Evar n
  | POp OP t1 t2 => let u1 := PTreeToTree t1 in let u2 := PTreeToTree t2 in match OP with
    | PADD    => Tree.Ebinary Tree.Add u1 u2
    | PSUB    => Tree.Ebinary Tree.Sub u1 u2
    | PMUL    => Tree.Ebinary Tree.Mul u1 u2
    | PFLTDIV => Tree.Ebinary Tree.Div u1 u2
    | PINTDIV => Tree.Eunary (Tree.Nearbyint Basic.rnd_ZR) (Tree.Ebinary Tree.Div u1 u2)
    end
  | PRnd md t' => Tree.Eunary (Tree.Round (rounding_mode_of_mode md) Rrnd.emin Format64.prec) (PTreeToTree t')
  | PNearbyint t' => Tree.Eunary (Tree.Nearbyint Basic.rnd_NE) (PTreeToTree t')
  | PTrunc t' => Tree.Eunary (Tree.Nearbyint Basic.rnd_ZR) (PTreeToTree t')
  | PLdexp t' p => Tree.Econst (Tree.Int 0) (* not compatible *)
  | PSqrt t' => Tree.Eunary Tree.Sqrt (PTreeToTree t') end.

Fixpoint Psucc t := match t with
  | PInt _ | PBinFl _ _ => t
  | PVar n => PVar (S n)
  | POp OP t1 t2 => POp OP (Psucc t1) (Psucc t2)
  | PRnd md t' => PRnd md (Psucc t')
  | PNearbyint t' => PNearbyint (Psucc t')
  | PTrunc t' => PTrunc (Psucc t')
  | PLdexp t' p => PLdexp (Psucc t') (Psucc p)
  | PSqrt t' => PSqrt (Psucc t') end.

Lemma PTreeToTree_Psucc : forall t, PTreeToTree (Psucc t) = exprsucc (PTreeToTree t).
Proof.
induction t as [| | | OP | | | | |]; simpl; intros.
5, 6, 7, 9: now rewrite IHt. 1, 2, 3, 5: easy.
now destruct OP; rewrite IHt1; rewrite IHt2.
Qed.

Definition evalPTree1 t l := Tree.eval (PTreeToTree t) l.

Fixpoint evalPTree2 t l := match t with
  | PInt n => IZR n
  | PBinFl n1 n2 => IZR n1 * Rpow2 n2
  | PVar n => nth n l R0
  | POp OP t1 t2 => let x1 := evalPTree2 t1 l in let x2 := evalPTree2 t2 l in
    match OP with
    | PADD    => (evalPTree2 t1 l) + (evalPTree2 t2 l)
    | PSUB    => (evalPTree2 t1 l) - (evalPTree2 t2 l)
    | PMUL    => (evalPTree2 t1 l) * (evalPTree2 t2 l)
    | PFLTDIV => (evalPTree2 t1 l) / (evalPTree2 t2 l)
    | PINTDIV => @Rrnd.nearbyint mode_ZR ((evalPTree2 t1 l) / (evalPTree2 t2 l))
    end
  | PRnd md t' => Rrnd.Rnd md (evalPTree2 t' l)
  | PNearbyint t' => @Rrnd.nearbyint mode_NE (evalPTree2 t' l)
  | PTrunc t' => @Rrnd.nearbyint mode_ZR (evalPTree2 t' l)
  | PLdexp t' p => ((evalPTree2 t' l) * Rpower 2 (evalPTree2 p l))
  | PSqrt t' => sqrt (evalPTree2 t' l) end.

Lemma evalPTree2_succ : forall t l x, evalPTree2 (Psucc t) (x :: l) = evalPTree2 t l.
Proof. induction t as [| | | OP | | | | |]; simpl; intros.
5, 6, 7, 9: now rewrite IHt. 1, 2, 3: easy.
- now destruct OP; rewrite IHt1, IHt2.
- now rewrite IHt1; rewrite IHt2.
Qed.



(* Computable Prop *)

Inductive Atom :=
(*| Ne: ProcessedTree -> ProcessedTree -> Atom
  | Lt: ProcessedTree -> ProcessedTree -> Atom
  | Le: ProcessedTree -> ProcessedTree -> Atom
  | Ge: ProcessedTree -> ProcessedTree -> Atom
  | Gt: ProcessedTree -> ProcessedTree -> Atom
  | Eq: ProcessedTree -> ProcessedTree -> Atom
  | LeLe: ProcessedTree -> ProcessedTree -> ProcessedTree -> Atom
  | AbsLe: ProcessedTree -> ProcessedTree -> Atom *)
  | InInt64: ProcessedTree -> Atom (* - IZR (Int64.N / 2) <= t <= IZR (Int64.N / 2 - 1) *)
  | InFloat64: ProcessedTree -> Atom (* Rabs t <= Rrnd.maxval *)
  | InFloat64Int: ProcessedTree -> Atom (* Rabs t <= Rpow2 53 *)
  | NonZero: ProcessedTree -> Atom (* t <> 0 *)
  | NonNeg: ProcessedTree -> Atom (* t >= 0 *)
  | RndExact: mode -> ProcessedTree -> Atom (* Rrnd.rnd t = t *)
  | LdexpControl: Z -> ProcessedTree -> ProcessedTree -> Atom
    (* (Rabs (evalRoundedR _ _ t1 vars)) <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec)
    /\ IZR n + evalRoundedR _ _ t2 vars <= IZR Rrnd.emax *).

Definition AtomToProp g l := match g with
  | InInt64 t => - IZR (Int64.N / 2) <= evalPTree2 t l <= IZR (Int64.N / 2 - 1)
  | InFloat64 t => Rabs (evalPTree2 t l) <= Rrnd.maxval
  | InFloat64Int t => Rabs (evalPTree2 t l) <= Rpow2 53
  | NonZero t => evalPTree2 t l <> 0
  | NonNeg t => evalPTree2 t l >= 0
  | RndExact md t => let u := evalPTree2 t l in Rrnd.Rnd md u = u
  | LdexpControl n t p =>
    Rabs (evalPTree2 t l) <= IZR (radix2 ^ Rrnd.prec - 1) * Rpow2 (n - Rrnd.prec) /\
    IZR n + evalPTree2 p l <= IZR Rrnd.emax end.

Inductive ProcessedProp :=
  | PTrue | PFalse
  | PAtom: Atom -> ProcessedProp
(*| PNot: ProcessedProp -> ProcessedProp
  | POr: ProcessedProp -> ProcessedProp -> ProcessedProp *)
  | PAnd: ProcessedProp -> ProcessedProp -> ProcessedProp.

Fixpoint PPropToProp p l := match p with
  | PFalse => False
  | PTrue => True
  | PAtom i => AtomToProp i l
  | PAnd p1 p2 => PPropToProp p1 l /\ PPropToProp p2 l end.

Fixpoint simplifyPProp p := match p with
  | PFalse => PFalse
  | PTrue => PTrue
  | PAtom i => PAtom i
  | PAnd p1 p2 => match simplifyPProp p1, simplifyPProp p2 with
    | PTrue, p' | p', PTrue => p'
    | p1', p2' => PAnd p1' p2' end
  end.

Lemma simplifyPProp_correct :
  forall p l, PPropToProp (simplifyPProp p) l <-> PPropToProp p l.
Proof. split.
- induction p; simpl; [easy.. |].
  now destruct (simplifyPProp p1), (simplifyPProp p2);
  simpl; intros; (split; [apply IHp1 | apply IHp2]).
- induction p; simpl; [easy.. |]. intros [H1 H2].
  now destruct (simplifyPProp p1), (simplifyPProp p2); simpl in *;
  apply IHp1 in H1; apply IHp2 in H2; [easy | ..]; repeat split.
Qed.



(* Auxiliary functions on computables *)

Fixpoint list_var_aux n init := match n with
  | O => nil
  | S n' => PVar init :: list_var_aux n' (S init) end.

Lemma length_list_var_aux : forall n i, length (list_var_aux n i) = n.
Proof. now induction n; [| intros i; simpl; rewrite (IHn (S i))]. Qed.

Lemma nth_list_var_aux_S: forall n k i t, nth (S n) (list_var_aux (S k) i) (Psucc t) =
  Psucc (nth n (list_var_aux k i) t).
Proof. induction n; destruct k; [easy.. |].
intros i t. simpl in *. now rewrite (IHn k (S i) t).
Qed.

Definition list_var n := list_var_aux n O.

Lemma list_var_correct1 : forall Tl (l : evalExprTypeReal_list Tl) n,
evalPTree1 (nth n (list_var (length Tl)) (PInt 0)) (toList l) = nthExprTypeReal n l 0.
Proof. unfold evalPTree1.
induction Tl as [| T' Tl]; destruct n; [easy | easy | easy |]. simpl length.
simpl toList. change (PInt 0) with (Psucc (PInt 0)). unfold list_var in *.
rewrite nth_list_var_aux_S. rewrite PTreeToTree_Psucc, eval_exprsucc.
now rewrite IHTl.
Qed.

Lemma list_var_correct2 : forall Tl (l : evalExprTypeReal_list Tl) n,
evalPTree2 (nth n (list_var (length Tl)) (PInt 0)) (toList l) = nthExprTypeReal n l 0.
Proof.
induction Tl as [| T' Tl]; destruct n; [easy | easy | easy |]. simpl length.
simpl toList. change (PInt 0) with (Psucc (PInt 0)). unfold list_var in *.
rewrite nth_list_var_aux_S. rewrite evalPTree2_succ. now rewrite IHTl.
Qed.

Fixpoint compatible t := match t with
  | PInt _ | PBinFl _ _ | PVar _ => true
  | POp _ t1 t2 => compatible t1 && compatible t2
  | PNearbyint t | PTrunc t | PSqrt t => compatible t
  | PRnd md t => match md with mode_NA => false | _ => compatible t end
  | PLdexp _ _ => false end.

Lemma compatible_correct :
  forall t l, compatible t = true -> evalPTree1 t l = evalPTree2 t l.
Proof. unfold evalPTree1. induction t as [| | | OP | | | | |]; simpl; intros.
6, 7: now rewrite IHt, Rrnd.nearbyint_IZR. 1, 2, 3, 6: easy.
- apply andb_prop in H. destruct H as [H1 H2].
  destruct OP; simpl; (rewrite IHt1, IHt2; [| easy | easy]);
  [easy | easy | easy | easy |]. now rewrite Rrnd.nearbyint_IZR.
- destruct m; [.. | easy]; now rewrite IHt.
- now rewrite IHt.
Qed.

Definition compatible_atom a := match a with
  | InInt64 t | InFloat64 t | InFloat64Int t
  | NonZero t | NonNeg t                     => compatible t
  | _                                        => false
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
  | i :: l' => merge l' (PAnd p (PAtom i))
  end.

Lemma merge_decomp : forall l1 p l,
  PPropToProp (merge l1 p) l <-> PPropToProp (merge l1 PTrue) l /\ PPropToProp p l.
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
  PPropToProp (merge (l1 ++ l2) p) l <->
 (PPropToProp (merge l1 p) l /\ PPropToProp (merge l2 p) l).
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
                         (evalPTree2 t l) = x /\ well_formed lR' vars' l
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

Fixpoint decomposeToPProp {Tl T} (t : ArithExprTree Tl T) vars md := match t with

  | Int       _                    n     => (PInt n, true, Void, PTrue)

  | BinFl     _                 n1 n2    => (PBinFl n1 n2, true, Void, PTrue)

  | Var       _                    n     =>
    let (u, b) := nth n vars (PInt 0%Z, false) in (u, b, Void, PTrue)

  | Op        _    T''   OP     t1 t2    =>
    let '(u1, b1, bt1, p1) := decomposeToPProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToPProp t2 vars md in
    let b  := b1 && b2 in
    let bt := Node (if b2 then match OP with
                    | DIV => Leaf (NonZero u2)
                    | _     => Void end else Void) (Node bt1 bt2) in
    let p  := PAnd (if b2 then PTrue else match OP with
                    | DIV => PAtom (NonZero u2)
                    | _     => PTrue end) (PAnd p1 p2) in
    match T'' with
    | Integer  =>
      let t  := POp (ArithOpToPOp T'' OP) u1 u2 in
      let bt' := Node (if b then Leaf (InInt64 t) else Void) bt in
      let p'  := PAnd (if b then PTrue else PAtom (InInt64 t)) p in
      (t, b, bt', p')
    | BinFloat =>
      let t  := PRnd md (POp (ArithOpToPOp T'' OP) u1 u2) in
      let bt' := Node (if b then Leaf (InFloat64 t) else Void) bt in
      let p'  := PAnd (if b then PTrue else PAtom (InFloat64 t)) p in
      (t, b, bt', p')
    end

  | OpExact   _          OP     t1 t2    =>
    let '(u1, b1, bt1, p1) := decomposeToPProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToPProp t2 vars md in
    let t  := POp (ArithOpToPOp BinFloat OP) u1 u2 in
    let b  := b1 && b2 in
    let bt := Node (if b then match OP with
                    | DIV => Node (Leaf (NonZero u2)) (Leaf (InFloat64 t))
                    | _     => Leaf (InFloat64 t)
                    end else Void) (Node bt1 bt2) in
    let p  := PAnd 
             (PAnd (if b then PTrue else match OP with
                    | DIV => PAnd (PAtom (NonZero u2)) (PAtom (InFloat64 t))
                    | _     => PAtom (InFloat64 t)
                    end) (PAtom (RndExact md t))) (PAnd p1 p2) in
    (t, b, bt, p)

  | Fma       _                 t1 t2 t3 =>
    let '(u1, b1, bt1, p1) := decomposeToPProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToPProp t2 vars md in
    let '(u3, b3, bt3, p3) := decomposeToPProp t3 vars md in
    let t  := PRnd md (POp PADD (POp PMUL u1 u2) u3) in
    let b  := b1 && b2 && b3 in
    let bt := Node (if b then Leaf (InFloat64 t) else Void) (Node (Node bt1 bt2) bt3) in
    let p  := PAnd (if b then PTrue else PAtom (InFloat64 t)) (PAnd (PAnd p1 p2) p3) in
    (t, b, bt, p)

  | FmaExact  _                 t1 t2 t3 =>
    let '(u1, b1, bt1, p1) := decomposeToPProp t1 vars md in
    let '(u2, b2, bt2, p2) := decomposeToPProp t2 vars md in
    let '(u3, b3, bt3, p3) := decomposeToPProp t3 vars md in
    let t  := POp PADD (POp PMUL u1 u2) u3 in
    let b  := b1 && b2 && b3 in
    let bt := Node (if b then Leaf (InFloat64 t) else Void) (Node (Node bt1 bt2) bt3) in
    let p  := PAnd (if b then PTrue else PAtom (InFloat64 t)) (PAnd (PAnd p1 p2) p3) in
    (t, b, bt, PAnd p (PAtom (RndExact md t)))

  | NearbyInt _                 t        =>
    let '(u, b, bt, p) := decomposeToPProp t vars md in
    (PNearbyint u, b, bt, p)

  | Trunc     _                 t        =>
    let '(u, b, bt, p) := decomposeToPProp t vars md in
    (PTrunc u, b, bt, p)

  | FloatInj  _                 t        =>
    let '(u, b, bt, p) := decomposeToPProp t vars md in
    let bt' := Node (if b then Leaf (InFloat64Int u) else Void) bt in
    let p'  := PAnd (if b then PTrue else PAtom (InFloat64Int u)) p in
    (u, b, bt', p')

  | Ldexp     _             n   t1 t2    =>
    let '(u1, _, bt1, p1) := decomposeToPProp t1 vars md in
    let '(u2, _, bt2, p2) := decomposeToPProp t2 vars md in
    let t  := PRnd md (PLdexp u1 u2) in
    let bt := Node bt1 bt2 in
    let p  := PAnd (PAtom (LdexpControl n u1 u2)) (PAnd p1 p2) in
    (t, false, bt, p)

  | Sqrt      _    T''          t        =>
    let '(u, b, bt, p) := decomposeToPProp t vars md in
    let t   := PSqrt u in
    let bt' := Node (if b then Leaf (NonNeg u) else Void) bt in
    let p'  := PAnd (if b then PTrue else PAtom (NonNeg u)) p in
    match T'' with
    | Integer  => (PTrunc t, b, bt', p')
    | BinFloat => (PRnd md t, b, bt', p')
    end

  | Let       _    _ _          t1 t2    =>
    let '(u, b1, bt1, p1) := decomposeToPProp t1 vars              md in
    let '(t, b2, bt2, p2) := decomposeToPProp t2 ((u, b1) :: vars) md in
    let b := b2 in
    let bt := Node bt2 bt1 (* Preserving some sort of order *) in
    let p := PAnd p1 p2 in
    (t, b, bt, p)

  | Assert    _    _          _ t
  | Postcond  _    _          _ t        => decomposeToPProp t vars md
  end.

Lemma decomposeToPProp_correct {Tl T} :
  forall (t : ArithExprTree Tl T) (lM : evalExprTypeMath_list Tl) vars l md,
  md <> mode_NA -> let lR := M2R_list lM in well_formed lR vars l ->
  let '(t', b, bt, p) := decomposeToPProp t vars md in
  let l' := BTreeToList bt in (
((b = true -> compatible t' = true) /\
 (evalPTree2 t' l = evalRoundedR t lR md)) /\
  forall k, compatible_atom (nth k l' (InInt64 (PInt 0))) = true) /\
 (PPropToProp (merge l' p) l -> wellBehaved t lM md).
Proof.
assert (Haux : forall l',
 (forall k, compatible_atom (nth k l' (InInt64 (PInt 0))) = true) <->
  map (fun p => compatible_atom p) l' = repeat true (length l')).
{ induction l'; [now split; [| intros _ [|]] |].
  destruct IHl' as [IHl'_0 IHl'_1]. simpl. split; intros H.
  - rewrite (H O). now rewrite IHl'_0; [| intros k; specialize (H (S k))].
  - inversion H as [[H0 H1]]. clear H. intros [| k]; [easy |].
    rewrite H0 in H1. rewrite H0. now apply IHl'_1. }
induction t as [| | Tl n | Tl T OP | Tl OP | | | | | | | Tl T | | |];
intros lM vars l md Hmd lR Truewf.
14, 15: now apply IHt.
1,  2:  repeat split; now intros [|].

all: simpl.

- set (d := nth n vars (PInt 0, false)). destruct_tuple_obj d.
  unfold d. clear d. split; [| easy]. split; [| now intros [|]].
  revert n vars l Truewf. induction Tl as [| T Tl];
  [now intros [|] [|] | intros [|] [| tb vars] l Hl; destruct_tuple_obj tb; simpl];
  [easy | now destruct Hl | easy |]. destruct lM as (xM, lM). apply (IHTl lM _ _ l).
  now simpl in Hl.


- specialize (IHt1 lM vars l md Hmd Truewf).
  specialize (IHt2 lM vars l md Hmd Truewf).
  revert IHt1 IHt2. fold lR.

  set (q1 := decomposeToPProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToPProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  unfold evalPTree1.
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
      rewrite <- evalRoundedR_evalRounded; fold lR; rewrite <-IHt2_2; destruct Hm1.
    1-4: rewrite plus_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: rewrite minus_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: rewrite mult_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: rewrite <-Ztrunc_div_; change Ztrunc with (round_mode mode_ZR);
      rewrite <-Rrnd.nearbyint_IZR; fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded; fold lR;
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
      rewrite <-evalRoundedR_evalRounded; fold lR; rewrite <-IHt2_2; destruct Hm1.
    1-4: fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: fold (M2R (evalRounded t1 lM md));
      fold (M2R (evalRounded t2 lM md)); rewrite <-2evalRoundedR_evalRounded;
      fold lR; now rewrite <-IHt1_2, <-IHt2_2.
    1-4: fold (M2R (evalRounded t1 lM md)); fold (M2R (evalRounded t2 lM md));
      rewrite <-2evalRoundedR_evalRounded; fold lR;
      now rewrite <-IHt1_2, <-IHt2_2.


- specialize (IHt1 lM vars l md Hmd Truewf).
  specialize (IHt2 lM vars l md Hmd Truewf).
  revert IHt1 IHt2. fold lR.

  set (q1 := decomposeToPProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToPProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  unfold evalPTree1.
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
  5: { fold (M2R (evalRounded t2 lM md)). rewrite <-evalRoundedR_evalRounded. fold lR.
       rewrite <-IHt2_2. destruct bq1, bq2; simpl in HOP;
        [destruct HOP as [[_ H] HOP] | | |]; now simpl in HP. }
  1-4: split; [now apply IHt1_4; split | split; [now apply IHt2_4; split | split]].
  1-8: fold (M2R (evalRounded t1 lM md)). 1-8: fold (M2R (evalRounded t2 lM md)).
  1-8: rewrite <-2evalRoundedR_evalRounded. 1-8: fold lR.
  1-8: rewrite <-IHt1_2, <-IHt2_2.
  1, 3, 5, 7: destruct bq1, bq2; simpl in *; now destruct HOP.
  1-4: now simpl in HP3.


- specialize (IHt1 lM vars l md Hmd Truewf).
  specialize (IHt2 lM vars l md Hmd Truewf).
  specialize (IHt3 lM vars l md Hmd Truewf).
  revert IHt1 IHt2 IHt3.

  set (q1 := decomposeToPProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToPProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).
  set (q3 := decomposeToPProp t3 vars md).
  destruct_tuple_obj q3.
  set (pq3 := snd q3). set (lq3 := snd (fst q3)). set (bq3 := snd (fst (fst q3))).
  set (tq3 := fst (fst (fst q3))).

  unfold evalPTree1.
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
  1-8: rewrite <-3evalRoundedR_evalRounded.
  1-8: now rewrite <-IHt1_2, <-IHt2_2, <-IHt3_2.


- specialize (IHt1 lM vars l md Hmd Truewf).
  specialize (IHt2 lM vars l md Hmd Truewf).
  specialize (IHt3 lM vars l md Hmd Truewf).
  revert IHt1 IHt2 IHt3.

  set (q1 := decomposeToPProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToPProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).
  set (q3 := decomposeToPProp t3 vars md).
  destruct_tuple_obj q3.
  set (pq3 := snd q3). set (lq3 := snd (fst q3)). set (bq3 := snd (fst (fst q3))).
  set (tq3 := fst (fst (fst q3))).

  unfold evalPTree1.
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
  fold (M2R (evalRounded t3 lM md)). rewrite <-3evalRoundedR_evalRounded.
  unfold Rrnd.fma. rewrite <-IHt1_2, <-IHt2_2, <-IHt3_2.
  split; [| easy].
  now destruct bq1, bq2, bq3; simpl in HOP; [destruct HOP as [_ HOP] | | | | | | |].


- specialize (IHt lM vars l md Hmd Truewf). revert IHt.

  set (q := decomposeToPProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux. split; [| assumption].
  now destruct bq; simpl; (split; [split | assumption]); [assumption | | easy |];
  rewrite IHt_2.


- specialize (IHt lM vars l md Hmd Truewf). simpl in IHt. revert IHt.

  set (q := decomposeToPProp t vars md).
  destruct_tuple_obj q.
  set (pq := snd q). set (lq := snd (fst q)). set (bq := snd (fst (fst q))).
  set (tq := fst (fst (fst q))).

  intros [[[IHt_1 IHt_2] IHt_3] IHt_4].
  rewrite Haux in IHt_3. rewrite Haux. split; [| assumption].
  now destruct bq; simpl; (split; [split | assumption]); [assumption | | easy |];
  rewrite IHt_2.


- specialize (IHt lM vars l md Hmd Truewf). simpl in IHt. revert IHt.

  set (q := decomposeToPProp t vars md).
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
    fold (M2R (evalRounded t lM md)); rewrite <-evalRoundedR_evalRounded; now rewrite <-IHt_2.


- specialize (IHt1 lM vars l md Hmd Truewf).
  specialize (IHt2 lM vars l md Hmd Truewf).
  revert IHt1 IHt2.

  set (q1 := decomposeToPProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).
  set (q2 := decomposeToPProp t2 vars md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  unfold evalPTree1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4]
         [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4].
  rewrite merge_decomp in IHt1_4, IHt2_4. rewrite Haux in IHt1_3, IHt2_3.

  rewrite Haux. split.
  { split; [split; [easy |] |].
    { simpl. now rewrite IHt1_2, IHt2_2. }
    unfold BTreeToList. simpl.
    rewrite (BTreeToList_aux_concat lq1).
    rewrite (BTreeToList_aux_concat lq2).
    rewrite 2app_length, 2repeat_app, 2map_app.
    now rewrite IHt1_3, IHt2_3. }
  rewrite merge_decomp. unfold BTreeToList. simpl. rewrite 2BTreeToList_aux_concat.
  rewrite 2merge_app. intros [[Hm1 [Hm2 _]] [HP [HP1 HP2]]].
  split; [now apply IHt1_4; split | split; [now apply IHt2_4; split |]].
  fold (M2R (evalRounded t1 lM md)). rewrite plus_IZR. fold (M2R (evalRounded t2 lM md)).
  rewrite <-2evalRoundedR_evalRounded. now rewrite <-IHt1_2, <-IHt2_2.


- specialize (IHt lM vars l md Hmd Truewf). simpl in IHt. revert IHt.

  set (q := decomposeToPProp t vars md).
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
      fold (M2R (evalRounded t lM md)); rewrite <-evalRoundedR_evalRounded; now rewrite <-IHt_2.
  + split; [split; [split; [now destruct md | now simpl; unfold lR; rewrite IHt_2] |] |].
    * destruct bq; simpl; unfold BTreeToList in IHt_3; [now rewrite IHt_1, IHt_3 |].
      now unfold BTreeToList.
    * intros H. destruct bq; rewrite merge_decomp in H; simpl in H;
      destruct H as [H1 [H3 H4]]; rewrite merge_decomp in H1;
      destruct H1 as [H1 H2]; simpl in H1, H2; destruct H2;
      (split; [now apply IHt_4; unfold BTreeToList; rewrite merge_decomp |]);
      fold (M2R (evalRounded t lM md)); rewrite <-evalRoundedR_evalRounded; now rewrite <-IHt_2.


- set (xM := evalRounded t1 lM md). set (xR := evalRoundedR t1 lR md).
  specialize (IHt1 lM vars l md Hmd Truewf). revert IHt1.

  set (q1 := decomposeToPProp t1 vars md).
  destruct_tuple_obj q1.
  set (pq1 := snd q1). set (lq1 := snd (fst q1)). set (bq1 := snd (fst (fst q1))).
  set (tq1 := fst (fst (fst q1))).

  unfold evalPTree1.
  intros [[[IHt1_1 IHt1_2] IHt1_3] IHt1_4].

  specialize (IHt2 (xM, lM) ((tq1, bq1) :: vars) l md Hmd). simpl in IHt2.
  assert (H : (bq1 = true -> compatible tq1 = true)
           /\ evalPTree2 tq1 l = xR
           /\ well_formed lR vars l).
  { now repeat split. }
  unfold xR, lR in H. rewrite evalRoundedR_evalRounded in H.
  fold xM in H. specialize (IHt2 H). revert IHt2.

  set (q2 := decomposeToPProp t2 ((tq1, bq1) :: vars) md).
  destruct_tuple_obj q2.
  set (pq2 := snd q2). set (lq2 := snd (fst q2)). set (bq2 := snd (fst (fst q2))).
  set (tq2 := fst (fst (fst q2))).

  intros [[[IHt2_1 IHt2_2] IHt2_3] IHt2_4].
  rewrite merge_decomp in IHt1_4, IHt2_4. rewrite Haux in IHt1_3, IHt2_3.

  rewrite Haux. split.
  { split; [split; [easy |]; rewrite IHt2_2; unfold xM, xR, lR; now rewrite evalRoundedR_evalRounded |].
    unfold BTreeToList. simpl.
    rewrite (BTreeToList_aux_concat lq1).
    rewrite (BTreeToList_aux_concat lq2).
    rewrite 2app_length, 2repeat_app, 2map_app.
    now rewrite IHt1_3, IHt2_3. }
  rewrite merge_decomp. unfold BTreeToList. simpl. rewrite 2BTreeToList_aux_concat.
  rewrite 2merge_app. intros [[Hm1 [Hm2 _]] [HP1 HP2]].
  split; [now apply IHt1_4 | now apply IHt2_4].
Qed.


Definition extractPProp {Tl T} (t : ArithExprTree Tl T) md :=
  let '(_, _, l, p) :=
    decomposeToPProp t (map add_compatibility (list_var (length Tl))) md
  in (l, simplifyPProp p).

Corollary extractPProp_correct {Tl T} :
  forall (t : ArithExprTree Tl T) (lM : evalExprTypeMath_list Tl) md,
  md <> mode_NA -> let lR := M2R_list lM in
  let '(bt, p) := extractPProp t md in let l' := BTreeToList bt in
 (forall k, compatible_atom (nth k l' (InInt64 (PInt 0))) = true) /\
 (PPropToProp (merge l' p) (toList lR) -> wellBehaved t lM md).
Proof. intros t lM md Hmd lR. unfold extractPProp. set (l := toList lR).
set (vars := (map add_compatibility (list_var (length Tl)))).
generalize (decomposeToPProp_correct t lM vars l md Hmd).
set (q := decomposeToPProp _ _ _). destruct_tuple_obj q.
unfold vars. unfold l at 1. intros H. specialize (H (well_formed_list_var lR)).
rewrite merge_decomp in H. rewrite merge_decomp. rewrite simplifyPProp_correct.
split; apply H.
Qed.



(* Try to solve compatible goals using Interval *)

Module Faux := SpecificFloat BigIntRadix2.
Module Iaux := FloatIntervalFull Faux.
Module IH := IntervalTacticAux Iaux.

Definition prec := Faux.PtoP 80.
Definition degree := 10%nat.

Definition AtomToGoal g := match g with
  | InInt64 t => Reify.Glele (Tree.Econst (Tree.Int (- Int64.N / 2))) (Tree.Econst (Tree.Int (Int64.N / 2 - 1)))
  | InFloat64 _ => Reify.Gabsle true (* (Tree.Econst (Tree.Int ((2 ^ 53 - 1) * 2 ^ 971))) *) (Tree.Ebinary Tree.Mul
   (Tree.Ebinary Tree.Sub (Tree.Econst (Tree.Bpow 2 53)) (Tree.Econst (Tree.Int 1)))
   (Tree.Econst (Tree.Bpow 2 971)))
  | NonZero t => Reify.Gne true (Tree.Econst (Tree.Int 0))
  | _ => Reify.Glt (Tree.Evar O) (*
    goals that we will not solve using interval.
    TODO: think harder about the case LdExpControl as we may be able to use interval to solve this one
    *)
  end.

Definition getPTree g := match g with
  | InInt64 t => t
  | InFloat64 t => t
  | NonZero t => t
  | _ => PInt 0 (*
    goals that we will not solve using interval.
    TODO: think harder about the case LdExpControl as we may be able to use interval to solve this one
    *)
  end.

Lemma AtomToGoal_correct : forall i a l,
   compatible_atom a = true ->
   Interval.contains (Iaux.convert i)
    (Xreal.Xreal (Tree.eval (PTreeToTree (getPTree a)) l)) ->
   IH.R.eval_goal_bnd prec (AtomToGoal a) i = true ->
   AtomToProp a l.
Proof. intros i a l Ha Hcont Heg. generalize IH.R.eval_goal_bnd_correct. intros H.
specialize (H prec (AtomToGoal a) i (Tree.eval (PTreeToTree (getPTree a)) l) Hcont Heg).
clear Hcont Heg. destruct a; simpl in *; [| | lra | | lra | easy..].
- apply (compatible_correct _ l) in Ha. now rewrite <- Ha.
- apply (compatible_correct _ l) in Ha. rewrite <- Ha. unfold Rrnd.maxval.
  now rewrite minus_IZR.
- apply (compatible_correct _ l) in Ha. now rewrite <- Ha.
Qed.

Fixpoint compareResults goals results := match goals with
  | nil => nil
  | g :: goals' => match results with
    | nil => nil (* should not happen in normal use *)
    | res :: results' => IH.R.eval_goal_bnd prec g res :: compareResults goals' results'
    end
  end.

Fixpoint par_construct Al (bl : list bool) := match Al with
  | nil      => PTrue
  | p :: Al' => match bl with
    | nil      => PTrue
    | b :: bl' => let P := par_construct Al' bl' in
      if b then (PAnd P (PAtom p)) else P
    end
  end.

Fixpoint par_mergerest Al (bl : list bool) P := match Al with
  | nil      => P
  | p :: Al' => match bl with
    | nil      => merge Al' (PAnd P (PAtom p))
    | b :: bl' => let P' := if b then P else (PAnd P (PAtom p)) in
      par_mergerest Al' bl' P'
    end
  end.

Lemma par_mergerest_decomp : forall Al bl P l,
  PPropToProp (par_mergerest Al bl P) l <->
  PPropToProp (par_mergerest Al bl PTrue) l /\ PPropToProp P l.
Proof. induction Al; [easy |].
intros [| [|] bl] P l; simpl; [| apply IHAl |].
- rewrite merge_decomp. rewrite (merge_decomp _ (PAnd _ _) _). now simpl.
- rewrite IHAl. rewrite (IHAl _ (PAnd _ _) _). now simpl.
Qed.

Lemma par_construct_mergerest : forall Al bl P l,
  PPropToProp (par_construct Al bl) l /\ PPropToProp (par_mergerest Al bl P) l <->
  PPropToProp (merge Al P) l.
Proof. induction Al; intros bl P l; simpl; destruct bl; [easy.. |].
rewrite par_mergerest_decomp, merge_decomp.
now case b; simpl; rewrite <-(IHAl bl).
Qed.

Definition generatePProp {Tl T}  (t : ArithExprTree Tl T) md vars hyps :=
  let (tointerval, unsolvable) := extractPProp t md in
  let tointerval := BTreeToList tointerval in
  let lexpr := map (fun p => PTreeToTree (getPTree p)) tointerval in
  match extract_list lexpr vars with
  | Eabort => merge tointerval unsolvable
  | Eprog prog consts =>
    let goals := map (fun p => AtomToGoal p) tointerval in
    let ieval := fun xi => IH.A.BndValuator.eval prec prog xi in
    let bounds := IH.compute_inputs prec hyps consts in
    let results := ieval bounds in
    let compared := compareResults goals results in
    par_mergerest tointerval compared unsolvable end.

Theorem generatePProp_correct {Tl T} :
  forall (t : ArithExprTree Tl T) (lM : evalExprTypeMath_list Tl) md hyps P,
  md <> mode_NA -> let lR := M2R_list lM in let l := toList lR in
    generatePProp t md (length l) hyps = P ->
    Reify.eval_hyps hyps l (PPropToProp P l -> wellBehaved t lM md).
Proof. intros t lM md hyps P Hmd lR l <-.
apply (IH.R.eval_hyps_bnd_correct prec).
generalize (extractPProp_correct t lM md). unfold generatePProp.
set (p0 := extractPProp _ _). destruct_tuple_obj p0.
set (unsolved := snd p0).
intros [Hm Hm'] Hh Hg; [easy |]. apply Hm'. revert Hm Hg.
set (tointerval := BTreeToList (fst p0)).
set (goals := map (fun p => AtomToGoal p) tointerval).
set (lexpr := map (fun p => PTreeToTree (getPTree p)) tointerval).
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
unfold goals. clear goals. unfold ieval. clear ieval. clear T t.
fold lR l. clearbody l. clear Tl lM lR. clearbody bounds.
unfold eval_real_nth in H. fold l' in H. revert H'.
generalize (IH.A.BndValuator.eval prec prog bounds).
intros l0 H'.
cut (forall k,
  nth k (compareResults (map (fun p : Atom => AtomToGoal p) tointerval) l0) false = true ->
  AtomToProp (nth k tointerval (InInt64 (PInt 0))) l).
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
  unfold lexpr in H'. rewrite (Eval.nth_map_lt (InInt64 (PInt 0))) in H' by easy.
  apply H'.
- clear -Hk Hkl. revert l0 k Hk Hkl. induction tointerval; [easy |]. simpl.
  intros [| i l0]; [now intros [|] |]. simpl.
  intros [| k]; [easy |]. simpl. intros Hk Hkl. apply IHtointerval; [easy |].
  now apply Nat.succ_lt_mono.
Qed.

Definition generatePProp_taylor {Tl T}  (t : ArithExprTree Tl T) md vars hyps :=
  let (tointerval, unsolvable) := extractPProp t md in
  let tointerval := BTreeToList tointerval in
  let lexpr := map (fun p => PTreeToTree (getPTree p)) tointerval in
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

Theorem generatePProp_taylor_correct {Tl T} :
  forall (t : ArithExprTree Tl T) (lM : evalExprTypeMath_list Tl) md hyps P,
  md <> mode_NA -> let lR := M2R_list lM in let l := toList lR in
    generatePProp_taylor t md (length l) hyps = P ->
    Reify.eval_hyps hyps l (PPropToProp P l -> wellBehaved t lM md).
Proof. intros t lM md hyps P Hmd lR l <-.
apply (IH.R.eval_hyps_bnd_correct prec).
generalize (extractPProp_correct t lM md). unfold generatePProp_taylor.
set (p0 := extractPProp _ _). destruct_tuple_obj p0.
set (unsolved := snd p0).
intros [Hm Hm'] Hh Hg; [easy |]. apply Hm'. revert Hm Hg.
set (tointerval := BTreeToList (fst p0)).
set (goals := map (fun p => AtomToGoal p) tointerval).
set (lexpr := map (fun p => PTreeToTree (getPTree p)) tointerval).
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
unfold goals. clear goals. clear T t.
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
  AtomToProp (nth k tointerval (InInt64 (PInt 0))) l).
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
  unfold lexpr in H'. rewrite (Eval.nth_map_lt (InInt64 (PInt 0))) in H' by easy.
  revert Hk Hkl. unfold l0'. clear -H'. revert tointerval l0 H'. induction k.
  + intros [| a tointerval] [| x0 l0]; easy.
  + intros [| a tointerval] [| x0 l0]; try easy. simpl. intros H' Hk Hkl.
    apply IHk. 3: now apply Nat.succ_lt_mono. easy. easy.
- clearbody l0'. clear -Hk Hkl. revert l0' k Hk Hkl. induction tointerval; [easy |]. simpl.
  intros [| i l0']; [now intros [|] |]. simpl.
  intros [| k]; [easy |]. simpl. intros Hk Hkl. apply IHtointerval; [easy |].
  now apply Nat.succ_lt_mono.
Qed.
