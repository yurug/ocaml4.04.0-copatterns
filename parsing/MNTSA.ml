(*******************************************************************************)
(*                                                                             *)
(*   Copattern-matchings and first-class observations in OCaml, with a macro   *)
(*                                                                             *)
(*                      Yann Régis-Gianas, Paul Laforgue                       *)
(*                                                                             *)
(*                      Diderot University, Paris - FRANCE                     *)
(*                    Northeastern University, BOSTON - USA                    *)
(*                                                                             *)
(*******************************************************************************)

open Asttypes
open Parsetree
open Parsetree_alpha

(** {0 Helpers} *)

(* Debugging. *)

let verbose = ref false

let _debug () = (verbose := true)

let _say ?header show x =
  if !verbose then
    let header_str = match header with
      | Some x -> x ^ "\n"
      | None -> ""
    in
    Printf.printf "%s%s\n%!" header_str (show x)

let show_as_list ?(l="") ?(r="") ?(sep=";") f xs =
  l ^ String.concat sep (List.map f xs) ^ r

(* Some combinators for conciseness. *)

let map_option f m = match m with
  | None -> None
  | Some x -> Some (f x)

let ( >>= ) m f = List.fold_right (fun x acc -> f x @ acc) m []

let map_fst f (a, b) = (f a, b)
let map_snd g (a, b) = (a, g b)

let ( <$> ) f m = List.map f m
let ( <$  ) f m = map_fst f <$> m
let (  $> ) f m = map_snd f <$> m

let list_sample xs = match xs with
  | x :: _ -> x
  | _ -> invalid_arg "list_sample"

let list_map_exists pred f xs =
  let rec aux = function
    | [] -> raise Not_found
    | x :: xs -> if pred x then f x :: xs else x :: aux xs
  in aux xs

(* Location and Longident. *)

let mknoloc x =
  Location.mknoloc x

let mknoloc_lid id =
  Location.mknoloc (Longident.parse id)

let lid_from_string_loc s =
  Location.mkloc (Longident.parse s.txt) s.loc

let map_last_lid f = Longident.(function
    | Lident s -> Lident (f s)
    | Ldot (lid, s) -> Ldot (lid, f s)
    | Lapply _ -> assert false
  )

(* Type extractors. *)

let from_typ_constr = function
  | Ptyp_constr (lid, params) -> (lid, params)
  | _ -> invalid_arg "from_typ_constr"

let rec result_typ ty = match ty with
  | Ptyp_constr _ -> ty
  | Ptyp_arrow (Nolabel, _, ty2) -> result_typ ty2.ptyp_desc
  | _ -> invalid_arg "result_typ"

(* Generators *)

module Gen = struct

  let var =
    let i = ref 0 in
    fun () ->
      let r = !i mod 26 in
      let x = char_of_int (r + 97) in
      incr i;
      Printf.sprintf "%c%d" x r

  let pattern_var =
    let i = ref 0 in
    fun () ->
      incr i;
      "pvar__" ^ string_of_int !i

end

(** {1 Linearisation and Transformation} *)

(**************************************************************************)
(*                                                                        *)
(* Linearisation of copattern matching                                    *)
(*                                                                        *)
(**************************************************************************)

module Linear = struct

  (* A copattern token is either of the form:
     - p     where p is a pattern
     - d     where d is a destructor
     with a possible type annotation.
  *)

  type token =
    | LApp of S.pattern * S.core_type option
    | LDes of string loc * S.core_type option

  (* A linear cocase is a cocase whose left hand-side is linear. *)

  type linear_cocase = {
    lhs : token list;
    rhs : S.expression;
  }

  (* [linearize q] returns a list of tokens corresponding to the
     linearized interpretation of [q] such that:

     linearize (f#D p)           == [D;p]
     linearize ((f p1 p2)#D1#D2) == [p1;p2;D1;D2]
  *)

  let linearize q =
    let rec loop acc q = match q.S.pcopat_desc with
      | S.Pcopat_hole ->
          acc
      | S.Pcopat_application (q, p, ty) ->
          loop (LApp (p, ty) :: acc) q
      | S.Pcopat_destructor (q, d, ty) ->
          loop (LDes (d, ty) :: acc) q
    in loop [] q

  let linearize_cocase cocase = {
    lhs = linearize cocase.S.pcc_lhs;
    rhs = cocase.S.pcc_rhs;
  }

end


module Unnest = struct

  (* Unnested deep copattern matching *)

  open Linear
  open Ast_helper_alpha

  (* Compare tokens fixme *)

  let compare_token x y =
    let open S in
    match (x,y) with
    | (LApp ({ppat_desc = Ppat_var x},_), LApp ({ppat_desc = Ppat_var y},_)) ->
        x.txt = y.txt
    | (LDes (d1,_), LDes (d2,_)) ->
        d1.txt = d2.txt
    | _ -> false

  let rec compare_tokens xs ys = match (xs,ys) with
    | ([], []) -> true
    | (tk1 :: xs, tk2 :: ys) -> compare_token tk1 tk2 && compare_tokens xs ys
    | _ -> false

  (* [remplace p z xs] remplaces the first element x of xs that
     satisfies p by z.
     If no element satisfies the predicate, z is pushed at the end of xs.
  *)

  let rec remplace p z xs = match xs with
    | [] -> [z]
    | x :: xs -> if p x then z :: xs else x :: remplace p z xs

  (* -- RESULT SPLITTING *)

  (* [plug_var v tk] plugs a variable pattern in a token [tk]. *)

  let string_of_position pos =
    "p_" ^ string_of_int pos

  let plug_pvar pvar tk = match tk with
    | LApp (_,ty) -> LApp (Pat.var pvar,ty)
    | LDes _ -> tk

  (* [plug_variables zs] plugs a variable for each applicative token. *)

  (* We create a coverage pattern that will drive the algorithm.
     It is not complete but remains safe since :
     - we do not extend the pattern matching with extra cases.
     - the coverage will be checked by the OCaml type checker.
  *)

  let plug_variables0 xs =
    let rec aux acc pos = function
      | [] -> List.rev acc
      | tk :: tks ->
          let s = string_of_position pos in
          let pvar = mknoloc s in
          let new_tk = plug_pvar pvar tk in
          aux (new_tk :: acc) (succ pos) tks
    in List.map (aux [] 0) xs

  let insert_token set left tk =
    (* (tk :: left) ∉ set *)
    if not (List.exists (compare_tokens (left @ [tk])) set)
    (* set[left ← (tk :: left)]*)
    then remplace (compare_tokens left) (left @ [tk]) set
    else set

  (* insert one step *)

  let insert_one set (l,r) = match r with
    | [] -> (set, (l,r))
    | tk :: r -> (insert_token set l tk, (l @ [tk], r))

  let show_tk0 tk = Linear.(match tk with
      | LApp ({S.ppat_desc = S.Ppat_var x}, _ty) -> x.txt
      | LDes (d,_ty) -> d.txt
      | _ -> assert false
    )

  let show_result_splitting rs =
    String.concat "\n" (List.map (fun r ->
        String.concat ";" (List.map show_tk0 r)
      ) rs)

  let init_zs xs = List.map (fun x -> ([],x)) xs

  let result_splitting lcs =
    let tks = List.map (fun cocase -> cocase.lhs) lcs in
    (* 1. Remplace patterns by fresh position variables. *)
    let plugged_tks = plug_variables0 tks in
    _say ~header:"After plugging variables" show_result_splitting plugged_tks;
    (* 2. Insertion of copatterns. *)
    let rec loop acc zs =
      if List.for_all (fun (_,r) -> r = []) zs
      then acc
      else
        let (new_acc,new_zs) = List.fold_left (
            fun (acc,zs) z ->
              let (new_acc,new_z) = insert_one acc z in
              (new_acc, zs @ [new_z])
          ) acc zs
        in loop (new_acc,[]) new_zs
    in fst @@ loop ([],[]) (init_zs plugged_tks)
end

module QTree = struct

  (* This module aims to handle unnested copatterns. *)

  open Linear

  type qtree = {
    path     : (string * S.core_type option) list;
    children : children;
  }

  and children =
    (* final state *)
    | QMatch of qmatch
    (* intermediate state *)
    | QTrees of ((string * S.core_type option) * qtree) list

  and qmatch =
    {
      (* Full path to be matched. *)
      qpath : (string * S.core_type option) list;
      (* The list of cases for the match. *)
      qcases : (S.pattern list * S.expression) list;
      (* Size of the last copattern in order to handle arrow symmetry. *)
      extra : int;
    }

  let qtree path children = {path; children}

  let show_ty = function
    | None -> "no"
    | Some _ -> "ty"

  let show_path p =
    show_as_list (fun (x,ty) -> x ^ " : " ^ show_ty ty) p

  let rec show_qt qt =
    Printf.sprintf "{path: %s; children: %s;}"
      (show_path qt.path)
      (show_children qt.children)

  and show_children = function
    | QMatch _ -> "<qmatch>"
    | QTrees qts -> "(" ^ String.concat ";" (show_assoc <$> qts) ^ ")"

  and show_assoc ((d,_ty), qt) =
    Printf.sprintf "%s --> %s" d (show_qt qt)

  (* Initialize a qtree with a copattern from the result splitting. *)

  let init full_path tks =
    let rec aux acc full_path tks = match tks with
      | [] ->
          let qmatch = QMatch {
              qpath = full_path @ List.rev acc;
              extra = List.length acc;
              qcases = [];
            }
          in
          qtree (List.rev acc) qmatch
      | LApp ({S.ppat_desc = S.Ppat_var x}, ty) :: tks ->
          aux ((x.txt, ty) :: acc) full_path tks
      | LDes (d,ty) :: tks ->
          let path = List.rev acc in
          let qt = aux [] (full_path @ path) tks in
          qtree path (QTrees [(d.txt,ty) , qt])
      | LApp _ :: _ ->
          assert false   (* by construction *)
    in aux [] full_path tks

  (* Insert a copattern from the result splitting into an existing qtree. *)

  let insert qt tks =
    let rec aux acc qt = function
      | [] ->
          let path = List.rev acc in
          let qmatch = QMatch {
              qpath = path;
              extra = List.length acc;
              qcases = [];
            }
          in
          qtree path qmatch
      | LApp ({S.ppat_desc = S.Ppat_var x}, ty) :: tks ->
          aux ((x.txt,ty) :: acc) qt tks
      | LDes ({txt = d}, ty) :: tks ->
          begin match qt.children with
          | QMatch _ -> assert false      (* by construction *)
          | QTrees qts ->
              let path = List.rev acc in
              begin try
                (* d ∈ qts *)
                let new_qts =
                  let cond ((d',_), _) = (d = d') in
                  let act (dt, qt) = (dt, aux path qt tks) in
                  list_map_exists cond act qts
                in
                { qt with children = QTrees new_qts }
              with
              | Not_found ->
                  (* d ∉ qts *)
                  let new_qt = init path tks in
                  let new_child = ((d,ty), new_qt) in
                  { qt with children = QTrees (new_child :: qts) }
              end
          end
      | _ -> assert false
    in aux [] qt tks

  let unnest = function
    | [] ->
        let qmatch = QMatch {qpath = []; qcases = []; extra = 0} in
        qtree [] qmatch
    | tks :: tl ->
        List.fold_left insert (init [] tks) tl

  let unnest xs = unnest (List.rev xs) (* fixme *)


  let collect_and_plug qt cocase  =
    let open S in
    let loc = cocase.pcc_lhs.pcopat_loc in
    let lc = Linear.linearize_cocase cocase in
    let rec sub acc acc2 qt = function
      | [] -> begin match qt.children with
          | QTrees _ ->
              (* The copattern is not deep enough. *)
              Location.prerr_warning loc Warnings.Unused_match;
              qt
          | QMatch qm ->
              (* here we should check the arity to adjust arrow symmetry. *)
              let path = acc @ List.rev acc2 in
              let new_qm = { qm with qcases = qm.qcases @ [(path,lc.rhs)] } in
              { qt with children = QMatch new_qm }
        end
      (* Applicative. *)
      | LApp (p,_) :: tks ->
          sub acc (p :: acc2) qt tks
      (* Destructors. *)
      | [LDes ({txt = d}, _)] ->
          begin match qt.children with
          | QMatch _ -> assert false
          | QTrees xs ->
              let cond ((d',_),_) = (d = d') in
              let act ((d,ty), qt) = match qt.children with
                | QMatch {qcases = [([],_)]} when acc = [] && acc2 = [] ->
                    Location.prerr_warning loc Warnings.Unused_match;
                    ((d,ty), qt)
                | _ ->
                    ((d,ty), sub acc acc2 qt [])
              in
              let new_qts = list_map_exists cond act xs in
              { qt with children = QTrees new_qts }
          end
      | LDes ({txt = d}, _) :: tks ->
          begin match qt.children with
          | QMatch _ -> assert false
          | QTrees xs ->
              let path = acc @ List.rev acc2 in
              let cond ((d',_),_) = (d = d') in
              let act ((d,ty), qt) = ((d,ty), sub [] path qt tks) in
              let new_qts = list_map_exists cond act xs in
              { qt with children = QTrees new_qts }
          end
    in sub [] [] qt lc.lhs

  (* Plug cocases in the qtree generated by the result splitting. *)
  let plugs qtree cocases =
    List.fold_left collect_and_plug qtree cocases

  (* DEBUG *)

  let _show_token = function
    | LDes (d,_) -> d.txt
    | LApp _ -> "App"

  let _show_ty = function
    | None   -> "no"
    | Some _ -> "ty"

  let _show_path p =
    show_as_list (fun (x,ty) -> x.txt ^ " : " ^ show_ty ty) p

end

(**************************************************************************)
(*                                                                        *)
(* Transformation                                                         *)
(*                                                                        *)
(**************************************************************************)

module Trans = struct

  (* Errors. *)

  type trans_error =
    | Missing_type_annotation of Location.t

  let report_error = function
    | Missing_type_annotation loc ->
        Location.errorf ~loc
          "In nested copattern-matching, a type annotation is expected."

  exception Error of trans_error

  let () =
    Location.register_error_of_exn
      (function
        | Error err -> Some (report_error err)
        | _ -> None
      )

  (* Codata and query types, dispatch handlers. *)

  open Ast_helper

  (* let codata_type = *)
  (*   let name = mknoloc_lid "Pervasives.codata" *)
  (*   in Typ.constr name [] *)

  (* let query_type res = *)
  (*   let name = mknoloc_lid "Pervasives.query" in *)
  (*   Typ.constr name [res] *)

  let dispatch = "dispatch"

  let dispatch_id = mknoloc "dispatch"

  let dispatch_lid = mknoloc_lid dispatch

  let apply_to_dispatch e = Exp.(apply (ident dispatch_lid) [(Nolabel, e)])

  (**************************************************************************)
  (*                                                                        *)
  (*          Translate cotypes                                             *)
  (*                                                                        *)
  (**************************************************************************)

  let string_tail s =
    let l = String.length s in
    if l = 0 then ""
    else String.(sub s 1 (pred l))

  (* FIXME #doc *)

  let lower_first_char s =
    String.(make 1 (Char.lowercase_ascii s.[0]) ^ string_tail s)

  let cofield expr d =
    let new_lid = map_last_lid lower_first_char d.txt in
    Pexp_apply (Exp.ident {d with txt = new_lid}, [(Nolabel, expr)])

  (* [upper_fc s] returns a fresh string s with its first char translated to
     uppercase. *)

  let upper_fc s =
    let b = Bytes.of_string s in
    Bytes.set b 0 (Char.uppercase_ascii s.[0]);
    Bytes.to_string b

  (* [to_obs lid_loc] returns a frehs lid with its last string extended with
     "_obs"
  *)

  let to_obs ty_lid =
    {ty_lid with txt = map_last_lid (fun s -> s ^ "_obs") ty_lid.txt}

  (* FIXME #doc *)

  let ty_variant core_type_mapper td =
    let ty_name = td.S.ptype_name.txt in
    let uname = {
      td.S.ptype_name with txt = upper_fc ty_name
    } in
    let lid = mknoloc_lid ty_name in
    let params = fst <$> (core_type_mapper <$ td.S.ptype_params) in
    let fresh_out = Gen.var () in
    let out_var = Typ.var fresh_out in
    let arrow_ty = Typ.(
        arrow Nolabel (constr (to_obs lid) (out_var :: params)) out_var
      ) in
    let poly_arrow = Typ.poly [fresh_out] arrow_ty in
    let field = Type.field dispatch_id poly_arrow in
    let args = Pcstr_record [field] in
    Type.constructor uname ~args

  (* FIXME #doc *)

  let coarrow core_type_mapper output_ty ty =
    let new_ty = core_type_mapper ty in
    let (lid, params) = from_typ_constr new_ty.ptyp_desc in
    let new_output_ty = core_type_mapper output_ty in
    Ptyp_constr (mknoloc lid.txt, new_output_ty :: params)

  (* FIXME #doc *)

  let cotype attributes_mapper core_type_mapper td =
    let tname = td.S.ptype_name.txt in
    let ptype_kind = Ptype_variant [ty_variant core_type_mapper td] in
    let ptype_params = core_type_mapper <$ td.S.ptype_params in
    let ptype_cstrs = List.map (fun (c_ty1, c_ty2, var) ->
        (core_type_mapper c_ty1, core_type_mapper c_ty2, var)
      ) td.S.ptype_cstrs
    in
    { ptype_name = Location.mkloc tname td.S.ptype_loc;
      ptype_params;
      ptype_cstrs;
      ptype_kind;
      ptype_private = td.S.ptype_private;
      ptype_manifest = map_option core_type_mapper td.S.ptype_manifest;
      ptype_attributes = attributes_mapper td.S.ptype_attributes;
      ptype_loc = td.S.ptype_loc;
    }

  let _cotype_obs attributes_mapper core_type_mapper td lds =
    let tname = td.S.ptype_name.txt in
    let params = fst <$> td.S.ptype_params in
    let constructor cld =
      let query = core_type_mapper cld.S.pcld_type in
      let (new_name, params) = match cld.S.pcld_index with
        | None ->
            (None, core_type_mapper <$> params)
        | Some {S.ptyp_desc = S.Ptyp_constr (name, params) } ->
            (Some name, core_type_mapper <$> params)
        | _ -> assert false
      in
      let lid = match new_name with
        | None ->
            mknoloc_lid tname
        | Some name ->
            name
      in
      let res = Typ.constr (to_obs lid) (query :: params) in
      Type.constructor ~res cld.S.pcld_name
    in
    let constructors = constructor <$> lds in
    let ptype_kind = Ptype_variant (constructors) in
    let ptype_params0 = core_type_mapper <$ td.S.ptype_params in
    let ptype_params1 = (Typ.any (), Invariant) :: ptype_params0 in
    let ptype_cstrs = List.map (fun (c_ty1, c_ty2, var) ->
        (core_type_mapper c_ty1, core_type_mapper c_ty2, var)
      ) td.S.ptype_cstrs
    in
    { ptype_name = Location.mkloc (tname ^ "_obs") td.S.ptype_loc;
      ptype_params = ptype_params1;
      ptype_cstrs;
      ptype_kind;
      ptype_private = td.S.ptype_private;
      ptype_manifest = map_option core_type_mapper td.S.ptype_manifest;
      ptype_attributes = attributes_mapper td.S.ptype_attributes;
      ptype_loc = td.S.ptype_loc;
    }


  (* [getters ty_name clds] returns a set of getters corresponding to
     the colabels. For instance, calling [getters stream [head;tail]]
     returns the following value bindings:

     let head (Stream {dispatch}) = dispatch Head
     let tail (Stream {dispatch}) = dispatch Tail
  *)

  let getters {txt = ty_name} clds =
    let ty_lid = Longident.parse ty_name in
    let uname =  map_last_lid upper_fc ty_lid in
    let rec_pat = Pat.record [(dispatch_lid, Pat.var dispatch_id)] Closed in
    let cons_pat = Pat.construct (mknoloc uname) (Some rec_pat) in
    let getter {S.pcld_name} =
      let lid = lid_from_string_loc pcld_name in
      let cons = Exp.construct lid None in
      let body = Exp.fun_ Nolabel None cons_pat (apply_to_dispatch cons) in
      let pat = lower_first_char pcld_name.txt in
      let var = Pat.var (mknoloc pat) in
      Vb.mk var body
    in Pstr_value (Nonrecursive, getter <$> clds)

  (**************************************************************************)
  (*                                                                        *)
  (*           Translate cofunctions                                        *)
  (*                                                                        *)
  (**************************************************************************)

  (* Borrowed from Parser.mly.

     When one writes [let f : type a. ty = M], OCaml translates this into
     [let f : 'a. ty[a'/a] = fun (type a) -> (M : ty)] during the parsing.
     This is done thanks to this [wrap_type_annotation] function.
  *)

  let check_variable vl loc v =
    if List.mem v vl then raise Syntaxerr.(Error(Variable_in_scope(loc, v)))

  let varify_constructors var_names t =
    let rec loop t =
      let desc = match t.ptyp_desc with
        | Ptyp_any -> Ptyp_any
        | Ptyp_var x ->
            check_variable var_names t.ptyp_loc x;
            Ptyp_var x
        | Ptyp_arrow (label, core_type, core_type') ->
            Ptyp_arrow(label, loop core_type, loop core_type')
        | Ptyp_tuple lst -> Ptyp_tuple (List.map loop lst)
        | Ptyp_constr( { txt = Longident.Lident s }, [])
          when List.mem s var_names ->
            Ptyp_var s
        | Ptyp_constr(longident, lst) ->
            Ptyp_constr(longident, List.map loop lst)
        | Ptyp_object (lst, o) ->
            Ptyp_object (List.map (fun (s, attrs, t) -> (s, attrs, loop t)) lst, o)
        | Ptyp_class (longident, lst) ->
            Ptyp_class (longident, List.map loop lst)
        | Ptyp_alias(core_type, string) ->
            check_variable var_names t.ptyp_loc string;
            Ptyp_alias(loop core_type, string)
        | Ptyp_variant(row_field_list, flag, lbl_lst_option) ->
            Ptyp_variant(List.map loop_row_field row_field_list,
                         flag, lbl_lst_option)
        | Ptyp_poly(string_lst, core_type) ->
            List.iter (check_variable var_names t.ptyp_loc) string_lst;
            Ptyp_poly(string_lst, loop core_type)
        | Ptyp_package(longident, lst) ->
            Ptyp_package(longident, loop $> lst)
        | Ptyp_extension (s, arg) ->
            Ptyp_extension (s, arg)
      in {t with ptyp_desc = desc}

    and loop_row_field = function
      | Rtag(label, attrs, flag, lst) ->
          Rtag(label, attrs, flag, List.map loop lst)
      | Rinherit t ->
          Rinherit (loop t)

    in loop t

  let mk_newtypes newtypes exp =
    List.fold_right (fun newtype exp ->
        Exp.mk (Pexp_newtype (newtype, exp))
      ) newtypes exp

  let wrap_type_annotation newtypes core_type body =
    let exp = Exp.mk (Pexp_constraint(body, core_type)) in
    let exp = mk_newtypes newtypes exp in
    (exp, Typ.poly newtypes (varify_constructors newtypes core_type))

  (* FIXME #doc *)

  let dispatch_ty_body lid params =
    let output_var = Gen.var () in
    let output_lid = mknoloc (Longident.parse output_var) in
    let output_typ = Typ.constr output_lid [] in
    let new_typ_constr = Typ.constr (to_obs lid) (output_typ :: params) in
    let result_type = Typ.arrow Nolabel new_typ_constr output_typ in
    (output_var, result_type)

  (* FIXME #doc *)

  let finalizer lid =
    let uname = mknoloc (map_last_lid upper_fc lid) in
    let drpat = Exp.record [(dispatch_lid, Exp.ident dispatch_lid)] None in
    Exp.construct uname (Some drpat)

  (* FIXME #doc *)

  let funs args expr =
    List.fold_right (fun (pat,ty) acc -> match ty with
        | None ->
            Exp.fun_ Nolabel None pat acc
        | Some ty ->
            Exp.fun_ Nolabel None (Pat.constraint_  pat ty) acc
      ) args expr

  let mk_dispatch ty_name params body =
    let (poly_var, new_ty) = dispatch_ty_body ty_name params in
    let (exp, poly) = wrap_type_annotation [poly_var] new_ty body in
    let pat = Pat.constraint_ (Pat.var dispatch_id) poly in
    Vb.mk pat exp

  let let_s es r =
    List.fold_right (fun vb acc -> Exp.let_ Nonrecursive vb acc) es r

  let lazy_force e =
    let force_lid = mknoloc_lid "Lazy.force" in
    Exp.apply (Exp.ident force_lid) [(Nolabel, e)]

  let mk_lazys ty_name params lazy_info =
    let vbs = List.map (fun (x,d) ->
        let e = Exp.construct d None in
        Vb.mk (Pat.var (mknoloc x)) (Exp.lazy_ (apply_to_dispatch e))
      ) lazy_info
    in
    let cases = List.map (fun (x,d) ->
        let p = Pat.construct d None in
        Exp.case p (lazy_force (Exp.ident (mknoloc_lid x)))
      ) lazy_info
    in
    let body = Exp.function_ cases in
    let dispatch_vb = mk_dispatch ty_name params body in
    (vbs :: [[dispatch_vb]])

  let split_on_des loc path ?ty lazy_info cases =
    let res_ty = match ty with
      | None -> raise (Error (Missing_type_annotation loc))
      | Some ty -> result_typ ty.ptyp_desc
    in
    let (ty_name, params) = from_typ_constr res_ty in
    let body = Exp.function_ cases in
    let dispatch_vb = mk_dispatch ty_name params body in
    let lazy_vbs = match lazy_info with
      | None -> []
      | Some info -> mk_lazys ty_name params info
    in
    let final = finalizer ty_name.txt in
    funs path (let_s ([dispatch_vb] :: lazy_vbs) final)

  (* FIXME #doc *)

  let deploy_qmatch expr_mapper pattern_mapper core_typ_mapper qt qmatch =
    let open QTree in
    let new_path = List.map (fun (x,ty) -> match ty with
        | None ->
            Exp.ident (mknoloc_lid x)
        | Some ty ->
            let id = Exp.ident (mknoloc_lid x) in
            Exp.constraint_ id (core_typ_mapper ty)
      ) qmatch.qpath
    in
    match new_path with
    | [] -> begin match qmatch.qcases with
        | [] -> assert false (* by construction *)
        (* cases = .. -> e *)
        | ([],e) :: xs ->
            if List.length xs > 0 then
              Location.prerr_warning e.S.pexp_loc Warnings.Unused_match;
            expr_mapper e
        | _ -> assert false
      end
    | _ ->
        let exp = match new_path with
          | [] -> assert false
          | [x] -> x
          | xs -> Exp.tuple xs
        in
        let mk_case (ps,e) = match pattern_mapper <$> ps with
          | [] -> assert false
          | [p] -> Exp.case p (expr_mapper e)
          | ps -> Exp.case (Pat.tuple ps) (expr_mapper e)
        in
        let cases = List.map mk_case qmatch.qcases in
        let pat_path = List.map (fun (x,ty) ->
            (Pat.var (mknoloc x), map_option core_typ_mapper ty)
          ) qt.path
        in
        funs pat_path (Exp.match_ exp cases)

  let deploy_qtree core_typ_mapper is_lazy qt xs aux =
    let open QTree in
    let ppath = List.map (fun (x,ty) ->
        (Pat.var (mknoloc x), map_option core_typ_mapper ty)
      ) qt.path
    in
    let ((_,ty),_) = list_sample xs in
    let new_ty = map_option core_typ_mapper ty in
    let mk_case ((d,_), qt) =
      let x = mknoloc d in
      let pat = Pat.construct (lid_from_string_loc x) None in
      Exp.case pat (aux qt)
    in
    let lazy_info =
      if not is_lazy then None
      else
        let infos = List.map (fun ((d,_),_) ->
            (Gen.pattern_var (), mknoloc_lid d)
          ) xs
        in Some infos
    in
    let cases = List.map mk_case xs in
    split_on_des Location.none ppath ?ty:new_ty lazy_info cases

  let deploy expr_mapper pattern_mapper core_typ_mapper is_lazy qt =
    let rec aux qt = match qt.QTree.children with
      | QTree.QMatch qmatch ->
          deploy_qmatch expr_mapper pattern_mapper core_typ_mapper qt qmatch
      | QTree.QTrees xs ->
          deploy_qtree core_typ_mapper is_lazy qt xs aux
    in aux qt

  let cofunction_ expr_mapper core_typ_mapper pattern_mapper is_lazy ty cocases =
    let lcs = Linear.linearize_cocase <$> cocases in
    let rs = Unnest.result_splitting lcs in
    _say  ~header:"- Result splitting" Unnest.show_result_splitting rs;
    let qt = QTree.unnest rs in
    _say ~header:"- Qtree before plugging" QTree.show_qt qt;
    let qt = QTree.plugs qt cocases in
    _say ~header:"- Qtree after plugging" QTree.show_qt qt;
    let body = deploy expr_mapper pattern_mapper core_typ_mapper is_lazy qt in
    Pexp_constraint (body, core_typ_mapper ty)

end


(**************************************************************************)
(*                                                                        *)
(* Mapper                                                                 *)
(*                                                                        *)
(**************************************************************************)


(** {2 Extension points} *)

let rec attribute (s, p) = (s, payload p)

and extension (s, p) = (s, payload p)

and attributes atts = attribute <$> atts

and payload = function
  | S.PStr str -> PStr (structure str)
  | S.PSig sign -> PSig (signature sign)
  | S.PTyp typ -> PTyp (core_type typ)
  | S.PPat (p, e) -> PPat (pattern p, map_option expression e)

(** {3 Core language} *)

(* Type expressions *)

and core_type c_ty = {
  ptyp_desc = core_type_desc c_ty.S.ptyp_desc;
  ptyp_loc = c_ty.S.ptyp_loc;
  ptyp_attributes = attributes c_ty.S.ptyp_attributes
}

and core_type_desc = function
  | S.Ptyp_any ->
      Ptyp_any
  | S.Ptyp_var s ->
      Ptyp_var s
  | S.Ptyp_arrow (arg, core_ty1, core_ty2) ->
      Ptyp_arrow (arg, core_type core_ty1, core_type core_ty2)
  | S.Ptyp_coarrow (core_ty1, core_ty2) ->
      Trans.coarrow core_type core_ty1 core_ty2
  | S.Ptyp_tuple core_tys ->
      Ptyp_tuple (core_type <$> core_tys)
  | S.Ptyp_constr (lid, core_tys) ->
      Ptyp_constr (lid, core_type <$> core_tys)
  | S.Ptyp_object (fields, flag) ->
      let field (s, atts, core_ty) = (s, attributes atts, core_type core_ty) in
      Ptyp_object (field <$> fields, flag)
  | S.Ptyp_class (lid, core_tys) ->
      Ptyp_class (lid, core_type <$> core_tys)
  | S.Ptyp_alias (core_ty, s) ->
      Ptyp_alias (core_type core_ty, s)
  | S.Ptyp_variant (r_fields, flag, labels) ->
      let new_r_fields = row_field <$> r_fields in
      Ptyp_variant (new_r_fields, flag, labels)
  | S.Ptyp_poly (ss, core_ty) ->
      Ptyp_poly (ss, core_type core_ty)
  | S.Ptyp_package pkg_ty ->
      Ptyp_package (package_type pkg_ty)
  | S.Ptyp_extension ext ->
      Ptyp_extension (extension ext)

and package_type (lid, pkg) =
  let new_pkg = core_type $> pkg in
  (lid, new_pkg)

and row_field = function
  | S.Rtag (lbl, atts, empty, core_tys) ->
      let new_core_tys = core_type <$> core_tys in
      let new_atts = attributes atts in
      Rtag (lbl, new_atts, empty, new_core_tys)
  | S.Rinherit core_ty ->
      Rinherit (core_type core_ty)

(* Patterns *)

and pattern pat = {
  ppat_desc = pattern_desc pat.S.ppat_desc;
  ppat_loc = pat.S.ppat_loc;
  ppat_attributes = attributes pat.S.ppat_attributes;
}

and pattern_desc = function
  | S.Ppat_any ->
      Ppat_any
  | S.Ppat_var s ->
      Ppat_var s
  | S.Ppat_alias (p, s) ->
      Ppat_alias (pattern p, s)
  | S.Ppat_constant c ->
      Ppat_constant c
  | S.Ppat_interval (c1, c2) ->
      Ppat_interval (c1, c2)
  | S.Ppat_tuple ps ->
      Ppat_tuple (pattern <$> ps)
  | S.Ppat_construct (lid, p) ->
      Ppat_construct (lid, map_option pattern p)
  | S.Ppat_variant (lbl, p) ->
      Ppat_variant (lbl, map_option pattern p)
  | S.Ppat_record (flds, flag) ->
      let new_flds = pattern $> flds in
      Ppat_record (new_flds, flag)
  | S.Ppat_array ps ->
      Ppat_array (pattern <$> ps)
  | S.Ppat_or (p1, p2) ->
      Ppat_or (pattern p1, pattern p2)
  | S.Ppat_constraint (p, core_ty) ->
      Ppat_constraint (pattern p, core_type core_ty)
  | S.Ppat_type lid ->
      Ppat_type lid
  | S.Ppat_lazy p ->
      Ppat_lazy (pattern p)
  | S.Ppat_unpack s ->
      Ppat_unpack s
  | S.Ppat_exception p ->
      Ppat_exception (pattern p)
  | S.Ppat_extension ext ->
      Ppat_extension (extension ext)
  | S.Ppat_open (lid, p) ->
      Ppat_open (lid, pattern p)

(* Value expressions *)

and expression exp = {
  pexp_desc = expression_desc exp.S.pexp_loc exp.S.pexp_desc;
  pexp_loc = exp.S.pexp_loc;
  pexp_attributes = attributes exp.S.pexp_attributes;
}

and expression_desc _loc = function
  | S.Pexp_ident lid ->
      Pexp_ident lid
  | S.Pexp_constant c ->
      Pexp_constant c
  | S.Pexp_let (rec_flag, vbs, e) ->
      Pexp_let (rec_flag, value_binding <$> vbs, expression e)
  | S.Pexp_function cs ->
      Pexp_function (case <$> cs)
  | S.Pexp_fun (lbl, e1, p, e) ->
      Pexp_fun (lbl, map_option expression e1, pattern p, expression e)
  | S.Pexp_apply (e, es) ->
      let new_es = expression $> es in
      Pexp_apply (expression e, new_es)
  | S.Pexp_match (e, cs) ->
      Pexp_match (expression e, case <$> cs)
  | S.Pexp_try (e, cs) ->
      Pexp_try (expression e, case <$> cs)
  | S.Pexp_tuple es ->
      Pexp_tuple (expression <$> es)
  | S.Pexp_construct (lid, e) ->
      Pexp_construct (lid, map_option expression e)
  | S.Pexp_variant (lbl, e) ->
      Pexp_variant (lbl, map_option expression e)
  | S.Pexp_record (flds, e) ->
      let new_flds = expression $> flds in
      Pexp_record (new_flds, map_option expression e)
  | S.Pexp_field (e, lid) ->
      Pexp_field (expression e, lid)
  | S.Pexp_setfield (e1, lid, e2) ->
      Pexp_setfield (expression e1, lid, expression e2)
  | S.Pexp_array es ->
      Pexp_array (expression <$> es)
  | S.Pexp_ifthenelse (e1, e2, e3) ->
      Pexp_ifthenelse (expression e1, expression e2, map_option expression e3)
  | S.Pexp_sequence (e1, e2) ->
      Pexp_sequence (expression e1, expression e2)
  | S.Pexp_while (e1, e2) ->
      Pexp_while (expression e1, expression e2)
  | S.Pexp_for (p, e1, e2, flag, e3) ->
      Pexp_for (pattern p, expression e1, expression e2, flag, expression e3)
  | S.Pexp_constraint (e, core_ty) ->
      Pexp_constraint (expression e, core_type core_ty)
  | S.Pexp_coerce (e, c_ty1, c_ty2) ->
      Pexp_coerce (expression e, map_option core_type c_ty1, core_type c_ty2)
  | S.Pexp_send (e, s) ->
      Pexp_send (expression e, s)
  | S.Pexp_new lid ->
      Pexp_new lid
  | S.Pexp_setinstvar (s, e) ->
      Pexp_setinstvar (s, expression e)
  | S.Pexp_override xs ->
      Pexp_override (expression $> xs)
  | S.Pexp_letmodule (s, m_expr, e) ->
      Pexp_letmodule (s, module_expr m_expr, expression e)
  | S.Pexp_letexception (ext_constructor, e) ->
      Pexp_letexception (extension_constructor ext_constructor, expression e)
  | S.Pexp_assert e ->
      Pexp_assert (expression e)
  | S.Pexp_lazy e ->
      Pexp_lazy (expression e)
  | S.Pexp_poly (e, c_ty) ->
      Pexp_poly (expression e, map_option core_type c_ty)
  | S.Pexp_object class_struct ->
      Pexp_object (class_structure class_struct)
  | S.Pexp_newtype (s, e) ->
      Pexp_newtype (s, expression e)
  | S.Pexp_pack module_e ->
      Pexp_pack (module_expr module_e)
  | S.Pexp_open (flag, lid, e) ->
      Pexp_open (flag, lid, expression e)
  | S.Pexp_extension ext ->
      Pexp_extension (extension ext)
  | S.Pexp_unreachable ->
      Pexp_unreachable
  | S.Pexp_cofunction (is_lazy, ty, cs) ->
      Trans.cofunction_ expression core_type pattern is_lazy ty cs
  | S.Pexp_cofield (e, lid) ->
      Trans.cofield (expression e) lid

and case c = {
  pc_lhs = pattern c.S.pc_lhs;
  pc_guard = map_option expression c.S.pc_guard;
  pc_rhs = expression c.S.pc_rhs;
}

(* Value descriptions *)

and value_description vd = {
  pval_name = vd.S.pval_name;
  pval_type = core_type vd.S.pval_type;
  pval_prim = vd.S.pval_prim;
  pval_attributes = attributes vd.S.pval_attributes;
  pval_loc = vd.S.pval_loc;
}

(* Type declarations *)

and type_declarations tds =
  tds >>= type_declaration

and type_declaration_getters td = match td.S.ptype_kind with
  | S.Ptype_cotype lds ->
      [Trans.getters td.S.ptype_name lds]
  | _ ->
      []

and type_declaration td = match td.S.ptype_kind with
  | S.Ptype_cotype lds -> [
      Trans.cotype attributes core_type td;
      Trans._cotype_obs attributes core_type td lds;
    ]

  | _ ->
      let ptype_params = core_type <$ td.S.ptype_params in
      let ptype_cstrs = List.map (fun (c_ty1, c_ty2, var) ->
          (core_type c_ty1, core_type c_ty2, var)
        ) td.S.ptype_cstrs in
      [{
        ptype_name = td.S.ptype_name;
        ptype_params;
        ptype_cstrs;
        ptype_kind = type_kind td.S.ptype_kind;
        ptype_private = td.S.ptype_private;
        ptype_manifest = map_option core_type td.S.ptype_manifest;
        ptype_attributes = attributes td.S.ptype_attributes;
        ptype_loc = td.S.ptype_loc;
      }]

and type_declaration_with_constraint td =
  let ptype_params = core_type <$ td.S.ptype_params in
  let ptype_cstrs = List.map (fun (c_ty1, c_ty2, var) ->
      (core_type c_ty1, core_type c_ty2, var)
    ) td.S.ptype_cstrs in
  {
    ptype_name = td.S.ptype_name;
    ptype_params;
    ptype_cstrs;
    ptype_kind = type_kind td.S.ptype_kind;
    ptype_private = td.S.ptype_private;
    ptype_manifest = map_option core_type td.S.ptype_manifest;
    ptype_attributes = attributes td.S.ptype_attributes;
    ptype_loc = td.S.ptype_loc;
  }

and type_kind = function
  | S.Ptype_abstract ->
      Ptype_abstract
  | S.Ptype_variant cds ->
      Ptype_variant (constructor_declaration <$> cds)
  | S.Ptype_record lds ->
      Ptype_record (label_declaration <$> lds)
  | S.Ptype_open ->
      Ptype_open
  | S.Ptype_cotype _ ->
      failwith "type_kind::S.Ptype_cotype"

and label_declaration ld = {
  pld_name = ld.S.pld_name;
  pld_mutable = ld.S.pld_mutable;
  pld_type = core_type ld.S.pld_type;
  pld_loc = ld.S.pld_loc;
  pld_attributes = attributes ld.S.pld_attributes;
}

and constructor_declaration cd = {
  pcd_name = cd.S.pcd_name;
  pcd_args = constructor_arguments cd.S.pcd_args;
  pcd_res = map_option core_type cd.S.pcd_res;
  pcd_loc = cd.S.pcd_loc;
  pcd_attributes = attributes cd.S.pcd_attributes;
}

and constructor_arguments = function
  | S.Pcstr_tuple c_tys ->
      Pcstr_tuple (core_type <$> c_tys)
  | S.Pcstr_record lds ->
      Pcstr_record (label_declaration <$> lds)

and type_extension ty_ext =
  let ptyext_params = core_type <$ ty_ext.S.ptyext_params in
  let ptyext_constructors =
    extension_constructor <$> ty_ext.S.ptyext_constructors
  in
  {
    ptyext_path = ty_ext.S.ptyext_path;
    ptyext_params;
    ptyext_constructors;
    ptyext_private = ty_ext.S.ptyext_private;
    ptyext_attributes = attributes ty_ext.S.ptyext_attributes;
  }

and extension_constructor ext_cons = {
  pext_name = ext_cons.S.pext_name;
  pext_kind = extension_constructor_kind ext_cons.S.pext_kind;
  pext_loc = ext_cons.S.pext_loc;
  pext_attributes = attributes ext_cons.S.pext_attributes;
}

and extension_constructor_kind = function
  | S.Pext_decl (cons_args, c_ty) ->
      Pext_decl (constructor_arguments cons_args, map_option core_type c_ty)
  | S.Pext_rebind lid ->
      Pext_rebind lid

(** {4 Class language} *)

(* Type expressions for the class language *)

and class_type class_ty = {
  pcty_desc = class_type_desc class_ty.S.pcty_desc;
  pcty_loc = class_ty.S.pcty_loc;
  pcty_attributes = attributes class_ty.S.pcty_attributes;
}

and class_type_desc = function
  | S.Pcty_constr (lid, c_tys) ->
      Pcty_constr (lid, core_type <$> c_tys)
  | S.Pcty_signature class_sig ->
      Pcty_signature (class_signature class_sig)
  | S.Pcty_arrow (arg_lb, c_ty, class_ty) ->
      Pcty_arrow (arg_lb, core_type c_ty, class_type class_ty)
  | S.Pcty_extension ext ->
      Pcty_extension (extension ext)

and class_signature csig = {
  pcsig_self = core_type csig.S.pcsig_self;
  pcsig_fields = class_type_field <$> csig.S.pcsig_fields;
}

and class_type_field class_ty_fld = {
  pctf_desc = class_type_field_desc class_ty_fld.S.pctf_desc;
  pctf_loc = class_ty_fld.S.pctf_loc;
  pctf_attributes = attributes class_ty_fld.S.pctf_attributes;
}

and class_type_field_desc = function
  | S.Pctf_inherit class_ty ->
      Pctf_inherit (class_type class_ty)
  | S.Pctf_val (s, m_flag, v_flag, c_ty) ->
      Pctf_val (s, m_flag, v_flag, core_type c_ty)
  | S.Pctf_method (s, p_flag, v_flag, c_ty) ->
      Pctf_method (s, p_flag, v_flag, core_type c_ty)
  | S.Pctf_constraint (c_ty1, c_ty2) ->
      Pctf_constraint (core_type c_ty1, core_type c_ty2)
  | S.Pctf_attribute att ->
      Pctf_attribute (attribute att)
  | S.Pctf_extension ext ->
      Pctf_extension (extension ext)

and class_declaration class_info =
  let pci_params = core_type <$ class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_expr class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_description class_info =
  let pci_params = core_type <$ class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_type class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_type_declaration class_info =
  let pci_params = core_type <$ class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_type class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_expr cl = {
  pcl_desc = class_expr_desc cl.S.pcl_desc;
  pcl_loc = cl.S.pcl_loc;
  pcl_attributes = attributes cl.S.pcl_attributes;
}

and class_expr_desc = function
  | S.Pcl_constr (lid, c_tys) ->
      Pcl_constr (lid, core_type <$> c_tys)
  | S.Pcl_structure class_struct ->
      Pcl_structure (class_structure class_struct)
  | S.Pcl_fun (arg_lb, e, p, class_e) ->
      let new_class_e = class_expr class_e in
      let new_p = pattern p in
      Pcl_fun (arg_lb, map_option expression e, new_p, new_class_e)
  | S.Pcl_apply (class_e, ls) ->
      Pcl_apply (class_expr class_e, expression $> ls)
  | S.Pcl_let (flag, vbs, class_e) ->
      Pcl_let (flag, value_binding <$> vbs, class_expr class_e)
  | S.Pcl_constraint (class_e, class_ty) ->
      Pcl_constraint (class_expr class_e, class_type class_ty)
  | S.Pcl_extension ext ->
      Pcl_extension (extension ext)

and class_structure class_str = {
  pcstr_self = pattern class_str.S.pcstr_self;
  pcstr_fields = class_field <$> class_str.S.pcstr_fields;
}

and class_field class_fd = {
  pcf_desc = class_field_desc class_fd.S.pcf_desc;
  pcf_loc = class_fd.S.pcf_loc;
  pcf_attributes = attributes class_fd.S.pcf_attributes;
}

and class_field_desc = function
  | S.Pcf_inherit (flag, class_e, s) ->
      Pcf_inherit (flag, class_expr class_e, s)
  | S.Pcf_val (s, flag, class_fd_kind) ->
      Pcf_val (s, flag, class_field_kind class_fd_kind)
  | S.Pcf_method (s, flag, class_fd_kind) ->
      Pcf_method (s, flag, class_field_kind class_fd_kind)
  | S.Pcf_constraint (c_ty1, c_ty2) ->
      Pcf_constraint (core_type c_ty1, core_type c_ty2)
  | S.Pcf_initializer e ->
      Pcf_initializer (expression e)
  | S.Pcf_attribute att ->
      Pcf_attribute (attribute att)
  | S.Pcf_extension ext ->
      Pcf_extension (extension ext)

and class_field_kind = function
  | S.Cfk_virtual c_ty ->
      Cfk_virtual (core_type c_ty)
  | S.Cfk_concrete (flag, e) ->
      Cfk_concrete (flag, expression e)

(** {5 Module language} *)

(* Type expressions for the module language *)

and module_type mty = {
  pmty_desc = module_type_desc mty.S.pmty_desc;
  pmty_loc = mty.S.pmty_loc;
  pmty_attributes = attributes mty.S.pmty_attributes;

}

and module_type_desc = function
  | S.Pmty_ident lid ->
      Pmty_ident lid
  | S.Pmty_signature sign ->
      Pmty_signature (signature sign)
  | S.Pmty_functor (s, mty1, mty2) ->
      Pmty_functor (s, map_option module_type mty1, module_type mty2)
  | S.Pmty_with (mty, wcs) ->
      Pmty_with (module_type mty, with_constraint <$> wcs)
  | S.Pmty_typeof mod_e ->
      Pmty_typeof (module_expr mod_e)
  | S.Pmty_extension ext ->
      Pmty_extension (extension ext)
  | S.Pmty_alias lid ->
      Pmty_alias lid

and signature sig_items = signature_item <$> sig_items

and signature_item sig_item = {
  psig_desc = signature_item_desc sig_item.S.psig_desc;
  psig_loc = sig_item.S.psig_loc;
}

and signature_item_desc = function
  | S.Psig_value vd ->
      Psig_value (value_description vd)
  | S.Psig_type (flag, ty_decls) ->
      Psig_type (flag, type_declarations ty_decls)
  | S.Psig_typext ty_ext ->
      Psig_typext (type_extension ty_ext)
  | S.Psig_exception ext_constructor ->
      Psig_exception (extension_constructor ext_constructor)
  | S.Psig_module mod_declaration ->
      Psig_module (module_declaration mod_declaration)
  | S.Psig_recmodule mod_declarations ->
      Psig_recmodule (module_declaration <$> mod_declarations)
  | S.Psig_modtype (mod_ty_declaration) ->
      Psig_modtype (module_type_declaration mod_ty_declaration)
  | S.Psig_open od ->
      Psig_open (open_description od)
  | S.Psig_include incl_desc ->
      Psig_include (include_description incl_desc )
  | S.Psig_class class_ds ->
      Psig_class (class_description <$> class_ds)
  | S.Psig_class_type class_ty_ds ->
      Psig_class_type (class_type_declaration <$> class_ty_ds)
  | S.Psig_attribute att ->
      Psig_attribute (attribute att)
  | S.Psig_extension (ext, atts) ->
      Psig_extension (extension ext, attributes atts)

and module_declaration md = {
  pmd_name = md.S.pmd_name;
  pmd_type = module_type md.S.pmd_type;
  pmd_attributes = attributes md.S.pmd_attributes;
  pmd_loc = md.S.pmd_loc;
}

and module_type_declaration mtd = {
  pmtd_name = mtd.S.pmtd_name;
  pmtd_type = map_option module_type mtd.S.pmtd_type;
  pmtd_attributes = attributes mtd.S.pmtd_attributes;
  pmtd_loc = mtd.S.pmtd_loc;

}

and open_description od = {
  popen_lid = od.S.popen_lid;
  popen_override = od.S.popen_override;
  popen_loc = od.S.popen_loc;
  popen_attributes = attributes od.S.popen_attributes;
}

and include_declaration incl = {
  pincl_mod = module_expr incl.S.pincl_mod;
  pincl_loc = incl.S.pincl_loc;
  pincl_attributes = attributes incl.S.pincl_attributes;
}

and include_description incl = {
  pincl_mod = module_type incl.S.pincl_mod;
  pincl_loc = incl.S.pincl_loc;
  pincl_attributes = attributes incl.S.pincl_attributes;
}

and with_constraint = function
  | S.Pwith_type (lid, ty_decl) ->
      Pwith_type (lid, type_declaration_with_constraint ty_decl)
  | S.Pwith_module (lid1, lid2) ->
      Pwith_module (lid1, lid2)
  | S.Pwith_typesubst ty_decl ->
      Pwith_typesubst (type_declaration_with_constraint ty_decl)
  | S.Pwith_modsubst (s, lid) ->
      Pwith_modsubst (s, lid)

(* Value expressions for the module language *)

and module_expr mod_ = {
  pmod_desc = module_expr_desc mod_.S.pmod_desc;
  pmod_loc = mod_.S.pmod_loc;
  pmod_attributes = attributes mod_.S.pmod_attributes;
}

and module_expr_desc = function
  | S.Pmod_ident lid ->
      Pmod_ident lid
  | S.Pmod_structure str ->
      Pmod_structure (structure str)
  | S.Pmod_functor (s, mod_ty, mod_e) ->
      Pmod_functor (s, map_option module_type mod_ty, module_expr mod_e)
  | S.Pmod_apply (mod_e1, mod_e2) ->
      Pmod_apply (module_expr mod_e1, module_expr mod_e2)
  | S.Pmod_constraint (mod_e, mod_ty) ->
      Pmod_constraint (module_expr mod_e, module_type mod_ty)
  | S.Pmod_unpack e ->
      Pmod_unpack (expression e)
  | S.Pmod_extension ext ->
      Pmod_extension (extension ext)

and structure str_items = str_items >>= structure_item

and structure_item str_item =
  let with_loc = Ast_helper.Str.mk ~loc:str_item.S.pstr_loc
  in with_loc <$> structure_item_desc str_item.S.pstr_desc

and structure_item_desc = function
  | S.Pstr_eval (e, atts) ->
      [Pstr_eval (expression e, attributes atts)]
  | S.Pstr_value (flag, vbs) ->
      [Pstr_value (flag, value_binding <$> vbs)]
  | S.Pstr_primitive vd ->
      [Pstr_primitive (value_description vd)]
  | S.Pstr_type (flag, tds) ->
      let new_tds = type_declarations tds in
      let getters = tds >>= type_declaration_getters in
      Pstr_type (flag, new_tds) :: getters
  | S.Pstr_typext ty_ext ->
      [Pstr_typext (type_extension ty_ext)]
  | S.Pstr_exception ext_constructor ->
      [Pstr_exception (extension_constructor ext_constructor)]
  | S.Pstr_module mb ->
      [Pstr_module (module_binding mb)]
  | S.Pstr_recmodule mbs ->
      [Pstr_recmodule (module_binding <$> mbs)]
  | S.Pstr_modtype mod_ty ->
      [Pstr_modtype (module_type_declaration mod_ty)]
  | S.Pstr_open od ->
      [Pstr_open (open_description od)]
  | S.Pstr_class cds ->
      [Pstr_class (class_declaration <$> cds)]
  | S.Pstr_class_type class_ty_ds ->
      [Pstr_class_type (class_type_declaration <$> class_ty_ds)]
  | S.Pstr_include id ->
      [Pstr_include (include_declaration id)]
  | S.Pstr_attribute att ->
      [Pstr_attribute (attribute att)]
  | S.Pstr_extension (ext, atts) ->
      [Pstr_extension (extension ext, attributes atts)]

and value_binding vb = {
  pvb_pat = pattern vb.S.pvb_pat;
  pvb_expr = expression vb.S.pvb_expr;
  pvb_attributes = attributes vb.S.pvb_attributes;
  pvb_loc = vb.S.pvb_loc
}

and module_binding mb = {
  pmb_name = mb.S.pmb_name;
  pmb_expr = module_expr mb.S.pmb_expr;
  pmb_attributes = attributes mb.S.pmb_attributes;
  pmb_loc = mb.S.pmb_loc;
}

(** {6 Toplevel} *)

(* Toplevel phrases *)

and toplevel_phrase = function
  | S.Ptop_def str ->
      Ptop_def (structure str)
  | S.Ptop_dir (s, dir_arg) ->
      Ptop_dir (s, dir_arg)
