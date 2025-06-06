open Big_int_Z

#if COQVERSION >= 81500
let constr_of_global gr = UnivGen.constr_of_monomorphic_global (Global.env ()) gr
#else
let constr_of_global = UnivGen.constr_of_monomorphic_global
#endif

#if COQVERSION >= 81800
let decompose_app = EConstr.decompose_app
#else
let decompose_app = Termops.decompose_app_vect
#endif

let find_reference t x =
  lazy (EConstr.of_constr (constr_of_global (Coqlib.gen_reference_in_modules "Interval" [t] x)))

let is_global evd c t = EConstr.eq_constr evd (Lazy.force c) t

let coq_ref_Datatypes = find_reference ["Coq"; "Init"; "Datatypes"]
let coq_cons = coq_ref_Datatypes "cons"
let coq_nil = coq_ref_Datatypes "nil"
let coq_pair = coq_ref_Datatypes "pair"

let coq_ref_Logic = find_reference ["Coq"; "Init"; "Logic"]
let coq_and = coq_ref_Logic "and"

let coq_ref_BinNums = find_reference ["Coq"; "Numbers"; "BinNums"]
let coq_Z0 = coq_ref_BinNums "Z0"
let coq_Zpos = coq_ref_BinNums "Zpos"
let coq_Zneg = coq_ref_BinNums "Zneg"
let coq_xH = coq_ref_BinNums "xH"
let coq_xI = coq_ref_BinNums "xI"
let coq_xO = coq_ref_BinNums "xO"

let coq_ref_Rdefinitions = find_reference ["Coq"; "Reals"; "Rdefinitions"]
let coq_Rdiv = coq_ref_Rdefinitions "Rdiv"
let coq_Rle = coq_ref_Rdefinitions "Rle"
let coq_IZR = coq_ref_Rdefinitions "IZR"

let interval_plot2 = find_reference ["Interval"; "Tactics"; "Plot_helper"] "plot2"

exception Unrecognized of EConstr.t

let rec tr_positive evd p =
  match EConstr.kind evd p with
  | Constr.Construct _ when is_global evd coq_xH p ->
      unit_big_int
  | Constr.App (f, [|a|]) when is_global evd coq_xI f ->
      add_int_big_int 1 (shift_left_big_int (tr_positive evd a) 1)
  | Constr.App (f, [|a|]) when is_global evd coq_xO f ->
      shift_left_big_int (tr_positive evd a) 1
  | Constr.Cast (p, _, _) ->
      tr_positive evd p
  | _ ->
      raise (Unrecognized p)

let rec tr_Z evd t =
  match EConstr.kind evd t with
  | Constr.Construct _ when is_global evd coq_Z0 t ->
      zero_big_int
  | Constr.App (f, [|a|]) when is_global evd coq_Zpos f ->
      tr_positive evd a
  | Constr.App (f, [|a|]) when is_global evd coq_Zneg f ->
      minus_big_int (tr_positive evd a)
  | Constr.Cast (t, _, _) ->
      tr_Z evd t
  | _ ->
      raise (Unrecognized t)

type rval =
  | Rcst of big_int
  | Rdiv of rval * rval

let rec tr_R evd t =
  match EConstr.kind evd t with
  | Constr.App (f, [|a|]) when is_global evd coq_IZR f ->
      Rcst (tr_Z evd a)
  | Constr.App (f, [|a;b|]) when is_global evd coq_Rdiv f ->
      Rdiv (tr_R evd a, tr_R evd b)
  | Constr.Cast (t, _, _) ->
      tr_R evd t
  | _ ->
      raise (Unrecognized t)

let rec tr_ineq evd t =
  match EConstr.kind evd t with
  | Constr.App (f, [|a;b|]) when is_global evd coq_Rle f ->
      (a, b)
  | _ ->
      raise (Unrecognized t)

let rec tr_bounds evd t =
  match EConstr.kind evd t with
  | Constr.App (f, [|i1;i2|]) when is_global evd coq_and f ->
      let (b1, x1) = tr_ineq evd i1 in
      let (x2, b2) = tr_ineq evd i2 in
      if x1 <> x2 then raise (Unrecognized t);
      (tr_R evd b1, x1, tr_R evd b2)
  | _ ->
      raise (Unrecognized t)

let rec tr_point_list evd t acc =
  match EConstr.kind evd t with
  | Constr.App (f, [|_|]) when is_global evd coq_nil f ->
      List.rev acc
  | Constr.App (f, [|_;a;b|]) when is_global evd coq_cons f ->
      let h =
        match EConstr.kind evd a with
        | Constr.App (f, [|_;_;a;b|]) when is_global evd coq_pair f ->
            (tr_Z evd a, tr_Z evd b)
        | _ ->
            raise (Unrecognized a) in
      tr_point_list evd b (h :: acc)
  | Constr.Cast (t, _, _) ->
      tr_point_list evd t acc
  | _ -> raise (Unrecognized t)

let tr_point_list evd t = tr_point_list evd t []

let tr_plot evd p =
  match decompose_app evd p with
  | c, [|_; ox; dx; oy; dy; h; l|] when is_global evd interval_plot2 c ->
      (tr_R evd ox, tr_R evd dx, tr_R evd oy, tr_R evd dy, tr_Z evd h, tr_point_list evd l)
  | _ ->
      raise (Unrecognized p)

let rec pr_R fmt = function
  | Rcst n -> Format.fprintf fmt "%s." (string_of_big_int n)
  | Rdiv (a,b) -> Format.fprintf fmt "(%a / %a)" pr_R a pr_R b

let of_R = function
  | Rcst n -> float_of_big_int n
  | Rdiv (Rcst a, Rcst b) -> float_of_big_int a /. float_of_big_int b
  | _ -> assert false

let generate fmt h l =
  Format.fprintf fmt "set xrange [] noextend@\n";
  Format.fprintf fmt "plot '-' using (ox+dx*$1):(oy+dy*$2):(oy+dy*$3) notitle with filledcurves@\n";
  let z = ref (h, zero_big_int) in
  let print_row i y1 y2 =
    Format.fprintf fmt "%d %s %s@\n" i (string_of_big_int y1) (string_of_big_int y2) in
  List.iteri (fun i y ->
      let (z1, z2) = y in
      let z1 = min_big_int z1 (fst !z) in
      let z2 = max_big_int z2 (snd !z) in
      print_row i z1 z2;
      z := y) l;
  print_row (List.length l) (fst !z) (snd !z);
  Format.fprintf fmt "e@\npause mouse close@\n@."

let display_plot_aux env evd p f =
  match tr_plot evd p with
  | (ox, dx, oy, dy, h, l) ->
      let file =
        match f with
        | None -> Filename.temp_file "interval_plot" ""
        | Some f -> f in
      let ch = open_out file in
      let fmt = Format.formatter_of_out_channel ch in
      Format.fprintf fmt "ox = %a@\ndx = %a@\noy = %a@\ndy = %a@\n"
        pr_R ox pr_R dx pr_R oy pr_R dy;
      generate fmt h l;
      close_out ch;
      begin match f with
      | None ->
          let e = Sys.command (Printf.sprintf "(gnuplot %s ; rm %s) &" file file) in
          if e <> 0 then
            CErrors.user_err ~hdr:"plot" (Pp.str "Gnuplot not found")
      | Some _ -> ()
      end
  | exception (Unrecognized e) ->
      CErrors.user_err ~hdr:"plot"
        Pp.(str "Cannot parse" ++ spc () ++ Printer.pr_econstr_env env evd e)

let display_plot p f ~pstate =
  let evd, env =
    match pstate with
    | None -> let env = Global.env () in Evd.from_env env, env
    | Some lemma -> Declare.Proof.get_current_context lemma in
  let evd, p = Constrintern.interp_constr_evars env evd p in
  let p = Retyping.get_type_of env evd p in
  display_plot_aux env evd p f

#if COQVERSION >= 81800
let decompose_prod_decls = EConstr.decompose_prod_decls
#else
let decompose_prod_decls = EConstr.decompose_prod_assum
#endif

let pr_type env evd typ =
  let (rel, typ) = decompose_prod_decls evd typ in
  let penv = EConstr.push_rel_context rel env in
  match tr_bounds evd typ with
  | (b1, x, b2) ->
      let b1 = of_R b1 in
      let b2 = of_R b2 in
      let c = (b1 +. b2) *. 0.5 in
      if (b2 -. b1) <= 1e-13 *. c then
        Pp.(Printer.pr_econstr_env penv evd x ++ str " ≈ " ++ real c)
      else
        Pp.(Printer.pr_econstr_env penv evd x ++ str " ∈ [" ++ real b1 ++ str "; " ++ real b2 ++ str "]")
  | exception Unrecognized _ ->
      Printer.pr_econstr_env penv evd typ

#if COQVERSION >= 81800
let cgenarg a = Constrexpr.CGenarg a
#else
let cgenarg a = Constrexpr.CHole (None, Namegen.IntroAnonymous, Some a)
#endif

let perform_tac nam bl tac =
  let arg = Genarg.in_gen (Genarg.rawwit Ltac_plugin.Tacarg.wit_tactic) tac in
  let term = CAst.make (cgenarg arg) in
  let env = Global.env () in
  let name =
    match nam with
    | None -> Namegen.next_global_ident_away (Names.Id.of_string "__") Names.Id.Set.empty
    | Some n -> n in
  let evd = Evd.from_env env in
  let evd, (body, typ), impargs =
    ComDefinition.interp_definition ~program_mode:false env evd Names.Id.Map.empty bl None term None in
  let typ =
    match typ with
    | Some t -> t
    | None -> Retyping.get_type_of ~lax:true env evd body in
  let cinfo = Declare.CInfo.make ~name ~typ:(Some typ) () in
  let info = Declare.Info.make () in
  let _r = Flags.silently (Declare.declare_definition ~info ~cinfo ~opaque:true ~body) evd in
  match decompose_app evd typ with
  | c, [|_; ox; dx; oy; dy; h; l|] when is_global evd interval_plot2 c ->
      if nam = None then display_plot_aux env evd typ None
  | _ ->
       Feedback.msg_notice (pr_type env evd typ)

let __coq_plugin_name = PLOTPLUGIN
let _ = Mltop.add_known_module __coq_plugin_name

#if COQVERSION >= 81900
let vtreadproofopt = Vernactypes.vtreadproofopt
let vtdefault = Vernactypes.vtdefault
#elif COQVERSION >= 81500
let vtreadproofopt = Vernacextend.vtreadproofopt
let vtdefault = Vernacextend.vtdefault
#else
let vtreadproofopt x = Vernacextend.VtReadProofOpt x
let vtdefault x = Vernacextend.VtDefault x
#endif

#if COQVERSION >= 81800
let vernac_extend = Vernacextend.static_vernac_extend ~plugin:(Some "coq-interval.plot")
#else
let vernac_extend = Vernacextend.vernac_extend
#endif

open Vernacextend

let () =
  vernac_extend
    ~command:"VernacPlot"
    ~classifier:(fun _ -> classify_as_query) ?entry:None
    [TyML (false,
        TyTerminal ("Plot",
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Stdarg.wit_constr),
        TyNil)),
#if COQVERSION >= 81400
        (fun r ?loc ~atts () ->
#else
        (fun r ~atts ->
#endif
          Attributes.unsupported_attributes atts;
          vtreadproofopt (display_plot r None)),
        None);
     TyML (false,
        TyTerminal ("Plot",
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Stdarg.wit_constr),
        TyTerminal ("as",
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Stdarg.wit_string),
        TyNil)))),
#if COQVERSION >= 81400
        (fun r s ?loc ~atts () ->
#else
        (fun r s ~atts ->
#endif
          Attributes.unsupported_attributes atts;
          vtreadproofopt (display_plot r (Some s))),
        None)]

let () =
  vernac_extend
    ~command:"VernacDo"
    ?entry:None
    [TyML (false,
        TyTerminal ("Def",
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Stdarg.wit_ident),
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Ltac_plugin.G_rewrite.wit_binders),
        TyTerminal (":=",
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Ltac_plugin.Tacarg.wit_tactic),
        TyNil))))),
#if COQVERSION >= 81400
        (fun name bl tac ?loc ~atts () ->
#else
        (fun name bl tac ~atts ->
#endif
          Attributes.unsupported_attributes atts;
          vtdefault (fun () -> perform_tac (Some name) bl tac)),
        Some (fun name bl tac -> VtSideff ([name], VtLater)));
     TyML (false,
        TyTerminal ("Do",
        TyNonTerminal (Extend.TUentry (Genarg.get_arg_tag Ltac_plugin.Tacarg.wit_tactic),
        TyNil)),
#if COQVERSION >= 81400
        (fun tac ?loc ~atts () ->
#else
        (fun tac ~atts ->
#endif
          Attributes.unsupported_attributes atts;
          vtdefault (fun () -> perform_tac None [] tac)),
        Some (fun tac -> VtSideff ([], VtLater)))]
