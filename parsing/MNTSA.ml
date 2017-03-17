(**************************************************************************)
(*                                                                        *)
(*                    Make Negative Types Smile Again                     *)
(*                                                                        *)
(*                    Paul Laforgue, Yann Régis-Gianas                    *)
(*                                                                        *)
(**************************************************************************)

open Asttypes
open Parsetree
open Parsetree_alpha

(** {0 Helpers} *)

let mknoloc x =
  Location.mknoloc x

let mknoloc_lid id =
  Location.mknoloc (Longident.parse id)

let lid_from_string_loc s =
  Location.mkloc (Longident.parse s.txt) s.loc

let map_last_lid f = Longident.(function
    | Lident s -> Lident (f s)
    | Ldot (lid,s) -> Ldot (lid,f s)
    | Lapply _ -> assert false
  )

let from_typ_constr = function
  | Ptyp_constr (lid,params) -> (lid,params)
  | _ -> assert false

let map_fst f (a,b) = (f a, b)
let map_snd g (a,b) = (a, g b)

let map_option f m = match m with
  | None -> None
  | Some x -> Some (f x)

let ( >>= ) m f = List.fold_right (fun x acc -> f x @ acc) m []

let ( <$> ) f m = List.map f m

(** {0 Linearisation and Transformation} *)

(**************************************************************************)
(*                                                                        *)
(* Linearisation of copattern matching                                    *)
(*                                                                        *)
(**************************************************************************)

module Linear = struct

  (* A copattern token is either of the form:
     - p         (applicative) where p is a pattern
     - d         where d is a destructor
     - (d : ty)  where d is a destructor and ty is a core type
  *)

  type token =
    | LApp of S.pattern
    | LDes of string loc * S.core_type option

  let location_of_token = function
    | LApp p -> p.S.ppat_loc
    | LDes (d, _) -> d.loc

  (* FIXME: alpha-equivalence for applicative token ? *)
  let equal_token l1 l2 =
    match l1, l2 with
    | LApp _, LApp _ -> (* FIXME *) false
    | LDes (d1, _), LDes (d2, _) -> d1.txt = d2.txt
    | _, _ -> false

  (* [linearize q] returns a list of tokens corresponding to the
     linearized interpretation of [q] such that:

     linearize (f#D p)         == [D;p]
     linearize ((f p1 p2)#D1#D2) == [p1;p2;D1;D2]

     Note that we loose the function identifier after linearizing.
  *)

  let linearize q =
    let rec loop acc q = match q.S.pcopat_desc with
      | S.Pcopat_hole _ ->
          acc
      | S.Pcopat_application (q,p) ->
          loop (LApp p :: acc) q
      | S.Pcopat_destructor (q,d,o) ->
          loop (LDes (d, o) :: acc) q
    in loop [] q

  (* A linear cocase is a cocase whose left hand-side is linear. *)

  type linear_cocase = {
    lhs : token list;
    rhs : S.expression;
  }

  let linear_cocase cocase = {
    lhs = linearize cocase.S.pcc_lhs;
    rhs = cocase.S.pcc_rhs;
  }

  (* FIXME #doc *)

  let is_final q = (q.lhs = [])

  (* FIXME #doc *)

  let insert key value xs =
    let rec aux acc = function
      | (k,v) :: xs when k.txt = key.txt ->
         (* FIXME: orelse
            List.rev ((k,v @ [value]) :: acc) @ xs *)
         List.rev acc @ (k,v @ [value]) :: xs
      | x :: xs ->
         aux (x :: acc) xs
      | [] ->
         List.rev ((key,[value]) :: acc)
    in aux [] xs

  (* We transform linear copattern matching into Qtrees.

     - Qtrees are trees whose node values are tokens.

     - Each node also carries a returning type.
     This is necessary in order to handle nested copatterns (remember that
     we are working in a syntax world and we cannot guess any type information).

     - If a qtree is final (i.e we reach a final cocase), the qtree children is
     just an expression. Otherwise, it is a list of qtrees.

       Examples
     --------

     A) the corresponding qtree resulting from translating the copattern
     matching below

     comatch f : ty with
      | f#(D1 : ty2)#D2 -> M
      | f#D1#D3 -> N

     is
                   D2 -> M
                 /
     D1 : ty2 --⟨
                 \
                   D3 -> N
  *)

  type qtree = {
    token    : string loc;            (* FIXME : should be a copattern token *)
    ntype    : S.core_type list;
    children : children;
  }

  and children =
    | Expr of S.expression
    | QTrees of qtree list

  let qtree token ntype children = {token; ntype; children}

  (* FIXME #doc *)

  let insert_tokens acc lcocase = match lcocase.lhs with
    | [] -> []
    | LDes (id, typ) :: qs -> insert id (typ, {lcocase with lhs = qs}) acc
    | LApp _ :: _ -> failwith "QApp::todo"

  (* FIXME #doc *)

  let split_branches qs =
    let rec aux (tys, cs) = function
      | [] ->
         (tys, List.rev cs)
      | (nty, c) :: qs ->
         let tys = match nty with None -> tys | Some ty -> ty :: tys in
         aux (tys, c :: cs) qs
    in
    aux ([], []) qs

  (* FIXME #doc *)

  (** [unnest xs] takes the branches of a copattern-matching as input
     and returns a list of qtrees which represent an unnested
     copattern-matching.
   *)
  let rec unnest (xs : linear_cocase list) =
    List.fold_left insert_tokens [] xs >>= fun (id, qs) ->
    let (tys, qs)  = split_branches qs in
    let (qs1, qs2) = List.partition is_final qs in
    let res1 = List.map (fun q -> qtree id tys (Expr q.rhs)) qs1 in
    let sub_copattern_matching =
      if qs2 = [] then [] else [qtree id tys (QTrees (unnest qs2))]
    in
    res1 @ sub_copattern_matching

  (* FIXME #doc *)

  let rec is_prefix lps1 lps2 = match lps1, lps2 with
    | ([], _) -> true
    | (x :: xs, y :: ys) -> equal_token x y && is_prefix xs ys
    | (_, []) -> false

  (* FIXME #doc *)

  let filter_redundant cocases =
    let hide lps1 lps2 =
      is_prefix lps1 lps2 || is_prefix lps2 lps1
    in
    let is_redundant above_branches branch =
      List.exists (fun (not_redundant, other_branch) ->
        not_redundant && hide other_branch.lhs branch.lhs
      ) above_branches
    in
    let issue_redundancy_warning branch =
      let loc = location_of_token (List.hd branch.lhs) in
      Location.prerr_warning loc Warnings.Unreachable_case;
    in
    let rec aux seen = function
      | [] ->
         List.(rev_map snd (filter fst seen))
      | branch :: cocases ->
         let redundant_branch = is_redundant seen branch in
         if redundant_branch then issue_redundancy_warning branch;
         aux ((not redundant_branch, branch) :: seen) cocases
    in
    aux [] cocases

  let active_linear_cocases cocases =
    filter_redundant (linear_cocase <$> cocases)

  (* DEBUG *)

  let rec show_qt {token;children} =
    Printf.sprintf "{id : %s; children = %s;}"
      token.txt
      (show_children children);

  and show_children = function
    | Expr _ -> "<expr>"
    | QTrees qts -> String.concat ";" (show_qt <$> qts)

  let _show qts =
    String.concat "\n" (show_qt <$> qts)

end

(**************************************************************************)
(*                                                                        *)
(*                           Transformation                               *)
(*                                                                        *)
(**************************************************************************)

module Trans = struct

  open Ast_helper

  (* Generators *)

  let fresh_var =
    let i = ref 0 in
    fun () ->
      let x = char_of_int (!i mod 26 + 97) in
      incr i;
      "~" ^ String.make 1 x

  let fresh_fid =
    let i = ref 0 in
    fun () ->
      incr i;
      "__fid__" ^ string_of_int !i

  let fresh_rhs_id =
    let i = ref 0 in
    fun () ->
      incr i;
      "__rhs__" ^ string_of_int !i

  (* Codata and query types, dispatch handlers. *)

  let codata_type =
    let name = mknoloc_lid "Pervasives.codata"
    in Typ.constr name []

  let query_type res =
    let name = mknoloc_lid "Pervasives.query" in
    Typ.constr name [res]

  let dispatch = "dispatch"

  let dispatch_id = mknoloc "dispatch"

  let dispatch_lid = mknoloc_lid dispatch

  let apply_to_dispatch e = Exp.(apply (ident dispatch_lid) [(Nolabel,e)])

  (**************************************************************************)
  (*                                                                        *)
  (*                    Translate cotypes                                   *)
  (*                                                                        *)
  (**************************************************************************)

  (* A type constructor whose name starts with a bang has its parameters
     expanded with the codata type.
  *)

  let string_tail s =
    let l = String.length s in
    if l = 0 then ""
    else String.(sub s 1 (pred l))

  let skip_bang s =
    assert (s.[0] = '!');
    string_tail s

  let type_constr core_type_mapper lid core_tys =
    let last_lid = Longident.last lid.txt in
    if last_lid.[0] = '!' then
      let new_lid = map_last_lid skip_bang lid.txt in
      let new_params = codata_type :: (core_type_mapper <$> core_tys) in
      Ptyp_constr (Location.mkloc new_lid lid.loc, new_params)
    else
      Ptyp_constr (lid, core_type_mapper <$> core_tys)

  (* FIXME #doc *)

  let lower_first_char s =
    String.(make 1 (Char.lowercase_ascii s.[0]) ^ string_tail s)

  let cofield expr d =
    let new_lid = map_last_lid lower_first_char d.txt in
    Pexp_apply (Exp.ident {d with txt = new_lid}, [(Nolabel, expr)])

  (* FIXME #doc *)

  let ty_variant td =
    let ty_name = skip_bang td.S.ptype_name.txt in
    let uname = {
      td.S.ptype_name with txt = String.uppercase_ascii ty_name
    } in
    let lid = mknoloc_lid ty_name in
    let params = List.map (fun _ ->
        Typ.var (fresh_var ())
      ) td.S.ptype_params
    in
    let fresh_out = fresh_var () in
    let out_var = Typ.var fresh_out in
    let query = query_type out_var in
    let arrow_ty =
      Typ.arrow Nolabel (Typ.constr lid (query :: params)) out_var
    in
    let poly_arrow = Typ.poly [fresh_out] arrow_ty in
    let field = Type.field dispatch_id poly_arrow in
    let args = Pcstr_record [field] in
    let res = Typ.constr lid (codata_type :: params) in
    Type.constructor uname ~args ~res

  (* FIXME #doc *)

  let coarrow core_type_mapper output_ty ty =
    let new_ty = core_type_mapper ty in
    let (lid,params) = from_typ_constr new_ty.ptyp_desc in
    let new_output_ty = core_type_mapper output_ty in
    Ptyp_constr (mknoloc lid.txt, query_type new_output_ty :: params)

  (* FIXME #doc *)

  let cotype attributes_mapper core_type_mapper td lds =
    let tname = skip_bang td.S.ptype_name.txt in
    let lid = mknoloc_lid tname in
    let params = fst <$> td.S.ptype_params in
    let constructor cld =
        let query = query_type (core_type_mapper cld.S.pcld_type) in
        let params = match cld.S.pcld_index with
          | None ->
              core_type_mapper <$> params
          | Some {S.ptyp_desc = S.Ptyp_constr (_, params) } ->
              core_type_mapper <$> params
          | _ ->
             failwith "Syntax error in cotype declaration"
        in
        let res = Typ.constr lid (query :: params) in
        Type.constructor ~res cld.S.pcld_name
    in
    let constructors = constructor <$> lds in
    let ptype_kind = Ptype_variant (ty_variant td :: constructors) in
    let ptype_params0 = map_fst core_type_mapper <$> td.S.ptype_params in
    let ptype_params1 = (Typ.any (), Invariant) :: ptype_params0 in
    let ptype_cstrs = List.map (fun (c_ty1,c_ty2,var) ->
        (core_type_mapper c_ty1, core_type_mapper c_ty2, var)
      ) td.S.ptype_cstrs
    in
    { ptype_name = Location.mkloc tname td.S.ptype_loc;
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

  (* FIXME #names *)

  let getters {txt = ty_name} clds =
    let uname = Longident.parse (String.uppercase_ascii (skip_bang ty_name)) in
    let rpat = Pat.record [(dispatch_lid, Pat.var dispatch_id)] Closed in
    let upat = Pat.construct (mknoloc uname) (Some rpat) in
    let getter {S.pcld_name} =
      let lid = lid_from_string_loc pcld_name in
      let cons = Exp.construct lid None in
      let body = Exp.fun_ Nolabel None upat (apply_to_dispatch cons) in
      let pat = lower_first_char pcld_name.txt in
      let var = Pat.var (mknoloc pat) in
      Vb.mk var body
    in Pstr_value (Nonrecursive, getter <$> clds)

  (**************************************************************************)
  (*                                                                        *)
  (*                     Translate cofunctions                              *)
  (*                                                                        *)
  (**************************************************************************)

  (* Borrowed from Parser.mly.

     When one writes [let f : type a. ty = M], OCaml translates this into
     [let f : 'a. ty[a'/a] = fun (type a) -> (M : ty)] during the parsing.
     This is done thanks to this [wrap_type_annotation] function.
  *)

  let check_variable vl _loc v =
    if List.mem v vl then failwith "Variable_in_scope"
  (* FIXME raise Syntaxerr.(Error(Variable_in_scope(loc,v))) *)

  let varify_constructors var_names t =
    let rec loop t =
      let desc = match t.ptyp_desc with
        | Ptyp_any -> Ptyp_any
        | Ptyp_var x ->
            check_variable var_names t.ptyp_loc x;
            Ptyp_var x
        | Ptyp_arrow (label,core_type,core_type') ->
            Ptyp_arrow(label, loop core_type, loop core_type')
        | Ptyp_tuple lst -> Ptyp_tuple (List.map loop lst)
        | Ptyp_constr( { txt = Longident.Lident s }, [])
          when List.mem s var_names ->
            Ptyp_var s
        | Ptyp_constr(longident, lst) ->
            Ptyp_constr(longident, List.map loop lst)
        | Ptyp_object (lst, o) ->
            Ptyp_object (List.map (fun (s,attrs,t) -> (s,attrs,loop t)) lst,o)
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
        | Ptyp_package(longident,lst) ->
            Ptyp_package(longident,List.map (fun (n,typ) -> (n,loop typ) ) lst)
        | Ptyp_extension (s, arg) ->
            Ptyp_extension (s, arg)
      in {t with ptyp_desc = desc}

    and loop_row_field = function
      | Rtag(label,attrs,flag,lst) ->
          Rtag(label,attrs,flag,List.map loop lst)
      | Rinherit t ->
          Rinherit (loop t)

    in loop t

  let mk_newtypes newtypes exp =
    List.fold_right (fun newtype exp ->
        Exp.mk (Pexp_newtype (newtype, exp))
      ) newtypes exp

  let wrap_type_annotation newtypes core_type body =
    let exp = Exp.mk (Pexp_constraint(body,core_type)) in
    let exp = mk_newtypes newtypes exp in
    (exp, Typ.poly newtypes (varify_constructors newtypes core_type))

  (* FIXME #doc *)

  let dispatch_ty_body lid params =
    let output_var = fresh_var () in
    let output_lid = mknoloc (Longident.parse output_var) in
    let output_typ = Typ.constr output_lid [] in
    let query = query_type output_typ in
    let new_typ_constr = Typ.constr lid (query :: params) in
    let result_type = Typ.arrow Nolabel new_typ_constr output_typ in
    (output_var, result_type)

  (* FIXME #doc *)

  let entrance id ty body =
    let tag = Recursive in
    let vbs = [Vb.mk (Pat.var id) (Exp.constraint_ body ty)] in
    let res = Exp.ident (lid_from_string_loc id) in
    Pexp_let (tag,vbs,res)

  (* Lazy comatch *)

  let mk_lazy expr = Exp.lazy_ expr

  let mk_lazy_force lid =
    let force_lid = mknoloc_lid "Lazy.force" in
    Exp.apply (Exp.ident force_lid) [(Nolabel,Exp.ident lid)]

  (* FIXME #doc *)

  let finalizer lid =
    let uname = mknoloc (map_last_lid String.uppercase_ascii lid) in
    let drpat = Exp.record [(dispatch_lid, Exp.ident dispatch_lid)] None in
    Exp.construct uname (Some drpat)

  (* FIXME #doc *)

  let mk_block id lazy_vbs cases ty_name params =
    let id_pat = Pat.var (mknoloc id) in
    let let_lazy expr =
      List.fold_right (fun vb acc ->
          Exp.let_ Nonrecursive [vb] acc
        ) lazy_vbs expr
    in
    let body = Exp.function_ cases in
    let result = finalizer ty_name.txt in
    let (poly_var,new_ty) = dispatch_ty_body ty_name params in
    let (exp,poly) = wrap_type_annotation [poly_var] new_ty body in
    let pat = Pat.constraint_ id_pat poly in
    let_lazy @@ Exp.let_ Nonrecursive [Vb.mk pat exp] result

  (* FIXME #doc *)

  let mk_dispatch_expr lazy_vbs cases ty =
    mk_block "dispatch" lazy_vbs cases ty

  (* FIXME #doc *)

  let replace_for_lazy xs =
    let rec loop (acc1, acc2) xs = match xs with
      | [] -> (acc1, acc2)
      | vb :: xs ->
          let id = fresh_rhs_id () in
          let a1 = Vb.mk (Pat.var (mknoloc id)) (mk_lazy vb.pc_rhs) in
          let lid = mknoloc_lid id in
          let a2 = Exp.case vb.pc_lhs (mk_lazy_force lid) in
          loop (a1 :: acc1, a2 :: acc2) xs
    in loop ([],[]) (List.rev xs)

  (* FIXME #doc *)

  let pat_cstr_from_str s =
    Pat.construct ~loc:s.loc (lid_from_string_loc s) None

  let implode expr_mapper is_lazy qts =
    let rec implode qts =
      let aux qt (cases, to_deploy) = match qt.Linear.children with
        | Linear.Expr expr ->
            (* final *)
            let new_expr = expr_mapper expr in
            let case = Exp.case (pat_cstr_from_str qt.Linear.token) new_expr in
            (case :: cases, to_deploy)
        | Linear.QTrees qts ->
            (* still to deploy *)
            let anchor = fresh_fid () in
            let anchor_lid = mknoloc_lid anchor in
            let anchor_ident = Exp.ident anchor_lid in
            let tys = qt.Linear.ntype in
            let (tmp_cases,xs) = implode qts in
            let (lazy_vbs, new_cases) =
              if is_lazy then replace_for_lazy tmp_cases else ([], tmp_cases)
            in
            let pat = pat_cstr_from_str qt.Linear.token in
            let case = Exp.case pat anchor_ident in
            (case :: cases, xs @ (anchor,tys,lazy_vbs,new_cases) :: to_deploy)
      in List.fold_right aux qts ([],[])
    in implode qts

  (* FIXME #doc #name *)

  let skip_codata = function
    | [] -> assert false
    | p::ps -> assert (p = codata_type); ps

  let fold_let_ core_ty_mapper xs expr =
    let fold_one (id,(tys : Parsetree_alpha.S.core_type list),lazy_vbs,cases) acc =
      let (ty, _tys) =
        match tys with
        | [] -> failwith "A type annotation is missing in a copattern."
        | ty :: tys -> (ty, tys)
      in
      let pat = Pat.var (mknoloc id) in
      let new_ty = core_ty_mapper ty in
      let (ty_name,params) = from_typ_constr new_ty.ptyp_desc in
      let params = skip_codata params in
      let body = mk_dispatch_expr lazy_vbs cases ty_name params in
      Exp.let_ Nonrecursive [Vb.mk pat body] acc
    in List.fold_right fold_one xs expr

  (* FIXME #doc *)

  let comatch_ expr_mapper core_ty_mapper is_lazy id ty cocases =
    let new_ty = core_ty_mapper ty in
    let (ty_name,params) = from_typ_constr new_ty.ptyp_desc in
    let params = skip_codata params in
    let qts = Linear.(unnest (active_linear_cocases cocases)) in
    (* print_endline (Linear.show qts); *)
    let (cases, xs) = implode expr_mapper is_lazy qts in
    let dispatch_expr =
      if is_lazy then
        let (lazy_vbs,new_cases) = replace_for_lazy cases in
        mk_dispatch_expr lazy_vbs new_cases ty_name params
      else
        mk_dispatch_expr [] cases ty_name params
    in
    let full_body = fold_let_ core_ty_mapper xs dispatch_expr in
    entrance id new_ty full_body

end


(**************************************************************************)
(*                                                                        *)
(*                           Mapper                                       *)
(*                                                                        *)
(**************************************************************************)


(** {2 Extension points} *)

let rec attribute (s,p) = (s, payload p)

and extension (s,p) = (s,payload p)

and attributes atts = attribute <$> atts

and payload = function
  | S.PStr str -> PStr (structure str)
  | S.PSig sign -> PSig (signature sign)
  | S.PTyp typ -> PTyp (core_type typ)
  | S.PPat (p,e) -> PPat (pattern p, map_option expression e)

(** {2 Core language} *)

(* Type expressions *)

and core_type {S.ptyp_desc; ptyp_loc; ptyp_attributes} = {
  ptyp_desc = core_type_desc ptyp_desc;
  ptyp_loc;
  ptyp_attributes = attributes ptyp_attributes
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
  | S.Ptyp_constr (lid,core_tys) ->
      Trans.type_constr core_type lid core_tys
  | S.Ptyp_object (fields, flag) ->
      let field (s,atts,core_ty) = (s, attributes atts, core_type core_ty) in
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
  let new_pkg = map_snd core_type <$> pkg in
  (lid, new_pkg)

and row_field = function
  | S.Rtag (lbl, atts, empty, core_tys) ->
      let new_core_tys = core_type <$> core_tys in
      let new_atts = attributes atts in
      Rtag (lbl, new_atts, empty, new_core_tys)
  | S.Rinherit core_ty ->
      Rinherit (core_type core_ty)

(* Patterns *)

and pattern {S.ppat_desc; ppat_loc; ppat_attributes} = {
  ppat_desc = pattern_desc ppat_desc;
  ppat_loc = ppat_loc;
  ppat_attributes = attributes ppat_attributes;
}

and pattern_desc = function
  | S.Ppat_any ->
      Ppat_any
  | S.Ppat_var s ->
      Ppat_var s
  | S.Ppat_alias (p,s) ->
      Ppat_alias (pattern p, s)
  | S.Ppat_constant c ->
      Ppat_constant c
  | S.Ppat_interval (c1,c2) ->
      Ppat_interval (c1,c2)
  | S.Ppat_tuple ps ->
      Ppat_tuple (pattern <$> ps)
  | S.Ppat_construct (lid, p) ->
      Ppat_construct (lid, map_option pattern p)
  | S.Ppat_variant (lbl, p) ->
      Ppat_variant (lbl, map_option pattern p)
  | S.Ppat_record (flds, flag) ->
      let new_flds = map_snd pattern <$> flds in
      Ppat_record (new_flds, flag)
  | S.Ppat_array ps ->
      Ppat_array (pattern <$> ps)
  | S.Ppat_or (p1,p2) ->
      Ppat_or (pattern p1, pattern p2)
  | S.Ppat_constraint (p,core_ty) ->
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

and expression {S.pexp_desc; pexp_loc; pexp_attributes} = {
  pexp_desc = expression_desc pexp_desc;
  pexp_loc;
  pexp_attributes = attributes pexp_attributes;
}

and expression_desc = function
  | S.Pexp_ident lid ->
      Pexp_ident lid
  | S.Pexp_constant c ->
      Pexp_constant c
  | S.Pexp_let (rec_flag,vbs,e) ->
      Pexp_let (rec_flag, value_binding <$> vbs, expression e)
  | S.Pexp_function cs ->
      Pexp_function (case <$> cs)
  | S.Pexp_fun (lbl,e1,p,e)  ->
      Pexp_fun (lbl, map_option expression e1, pattern p, expression e)
  | S.Pexp_apply (e,es)  ->
      let new_es = map_snd expression <$> es in
      Pexp_apply (expression e, new_es)
  | S.Pexp_match (e,cs) ->
      Pexp_match (expression e, case <$> cs)
  | S.Pexp_try (e,cs) ->
      Pexp_try (expression e, case <$> cs)
  | S.Pexp_tuple es ->
      Pexp_tuple (expression <$> es)
  | S.Pexp_construct (lid,e) ->
      Pexp_construct (lid, map_option expression e)
  | S.Pexp_variant (lbl,e) ->
      Pexp_variant (lbl, map_option expression e)
  | S.Pexp_record (flds,e) ->
      let new_flds = map_snd expression <$> flds in
      Pexp_record (new_flds, map_option expression e)
  | S.Pexp_field (e,lid) ->
      Pexp_field (expression e,lid)
  | S.Pexp_setfield (e1,lid,e2) ->
      Pexp_setfield (expression e1, lid, expression e2)
  | S.Pexp_array es ->
      Pexp_array (expression <$> es)
  | S.Pexp_ifthenelse (e1,e2,e3) ->
      Pexp_ifthenelse (expression e1, expression e2, map_option expression e3)
  | S.Pexp_sequence (e1,e2) ->
      Pexp_sequence (expression e1, expression e2)
  | S.Pexp_while (e1,e2) ->
      Pexp_while (expression e1, expression e2)
  | S.Pexp_for (p,e1,e2,flag,e3) ->
      Pexp_for (pattern p, expression e1, expression e2, flag, expression e3)
  | S.Pexp_constraint (e,core_ty) ->
      Pexp_constraint (expression e, core_type core_ty)
  | S.Pexp_coerce (e,c_ty1,c_ty2) ->
      Pexp_coerce (expression e, map_option core_type c_ty1, core_type c_ty2)
  | S.Pexp_send (e,s) ->
      Pexp_send (expression e, s)
  | S.Pexp_new lid ->
      Pexp_new lid
  | S.Pexp_setinstvar (s,e) ->
      Pexp_setinstvar (s, expression e)
  | S.Pexp_override xs ->
      Pexp_override (map_snd expression <$> xs)
  | S.Pexp_letmodule (s, m_expr, e) ->
      Pexp_letmodule (s, module_expr m_expr, expression e)
  | S.Pexp_letexception (ext_constructor, e) ->
      Pexp_letexception (extension_constructor ext_constructor, expression e)
  | S.Pexp_assert e ->
      Pexp_assert (expression e)
  | S.Pexp_lazy e ->
      Pexp_lazy (expression e)
  | S.Pexp_poly (e,c_ty) ->
      Pexp_poly (expression e, map_option core_type c_ty)
  | S.Pexp_object class_struct ->
      Pexp_object (class_structure class_struct)
  | S.Pexp_newtype (s,e) ->
      Pexp_newtype (s,expression e)
  | S.Pexp_pack module_e ->
      Pexp_pack (module_expr module_e)
  | S.Pexp_open (flag,lid,e) ->
      Pexp_open (flag, lid, expression e)
  | S.Pexp_extension ext ->
      Pexp_extension (extension ext)
  | S.Pexp_unreachable ->
      Pexp_unreachable
  | S.Pexp_comatch (is_lazy,id,ty,cs) ->
      Trans.comatch_ expression core_type is_lazy id ty cs
  | S.Pexp_cofield (e,lid) ->
      Trans.cofield (expression e) lid

and case x = {
  pc_lhs = pattern x.S.pc_lhs;
  pc_guard = map_option expression x.S.pc_guard;
  pc_rhs = expression x.S.pc_rhs;
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

and type_declarations tds = type_declaration <$> tds

and type_declaration_getters td = match td.S.ptype_kind with
  | S.Ptype_cotype lds ->
      [Trans.getters td.S.ptype_name lds]
  | _ ->
      []

and type_declaration td = match td.S.ptype_kind with
  | S.Ptype_cotype lds ->
      Trans.cotype attributes core_type td lds
  | _ ->
      let ptype_params = map_fst core_type <$> td.S.ptype_params in
      let ptype_cstrs = List.map (fun (c_ty1,c_ty2,var) ->
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

and type_declaration_with_constraint td =
  let ptype_params = map_fst core_type <$> td.S.ptype_params in
  let ptype_cstrs = List.map (fun (c_ty1,c_ty2,var) ->
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
  let ptyext_params = map_fst core_type <$> ty_ext.S.ptyext_params in
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
  | S.Pext_decl (cons_args,c_ty) ->
      Pext_decl (constructor_arguments cons_args,map_option core_type c_ty)
  | S.Pext_rebind lid ->
      Pext_rebind lid

(** {2 Class language} *)

(* Type expressions for the class language *)

and class_type class_ty = {
  pcty_desc = class_type_desc class_ty.S.pcty_desc;
  pcty_loc = class_ty.S.pcty_loc;
  pcty_attributes = attributes class_ty.S.pcty_attributes;
}

and class_type_desc = function
  | S.Pcty_constr (lid,c_tys) ->
      Pcty_constr (lid, core_type <$> c_tys)
  | S.Pcty_signature class_sig ->
      Pcty_signature (class_signature class_sig)
  | S.Pcty_arrow (arg_lb,c_ty,class_ty) ->
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
  | S.Pctf_val (s,m_flag,v_flag,c_ty) ->
      Pctf_val (s, m_flag, v_flag, core_type c_ty)
  | S.Pctf_method (s,p_flag,v_flag,c_ty) ->
      Pctf_method (s,p_flag,v_flag, core_type c_ty)
  | S.Pctf_constraint (c_ty1,c_ty2) ->
      Pctf_constraint (core_type c_ty1, core_type c_ty2)
  | S.Pctf_attribute att ->
      Pctf_attribute (attribute att)
  | S.Pctf_extension ext ->
      Pctf_extension (extension ext)

and class_declaration class_info =
  let pci_params = map_fst core_type <$> class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_expr class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_description class_info =
  let pci_params = map_fst core_type <$> class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_type class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_type_declaration class_info =
  let pci_params = map_fst core_type <$> class_info.S.pci_params in
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
  | S.Pcl_constr (lid,c_tys) ->
      Pcl_constr (lid, core_type <$> c_tys)
  | S.Pcl_structure class_struct ->
      Pcl_structure (class_structure class_struct)
  | S.Pcl_fun (arg_lb,e,p,class_e) ->
      let new_class_e = class_expr class_e in
      let new_p = pattern p in
      Pcl_fun (arg_lb, map_option expression e, new_p, new_class_e)
  | S.Pcl_apply (class_e,ls) ->
      Pcl_apply (class_expr class_e, map_snd expression <$> ls)
  | S.Pcl_let (flag,vbs,class_e) ->
      Pcl_let (flag, value_binding <$> vbs, class_expr class_e)
  | S.Pcl_constraint (class_e,class_ty) ->
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
  | S.Pcf_inherit (flag,class_e,s) ->
      Pcf_inherit (flag, class_expr class_e, s)
  | S.Pcf_val (s,flag,class_fd_kind) ->
      Pcf_val (s,flag, class_field_kind class_fd_kind)
  | S.Pcf_method (s,flag,class_fd_kind) ->
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
  | S.Cfk_concrete (flag,e) ->
      Cfk_concrete (flag, expression e)

(** {2 Module language} *)

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
  | S.Pmty_functor (s,mty1,mty2) ->
      Pmty_functor (s, map_option module_type mty1, module_type mty2)
  | S.Pmty_with (mty,wcs) ->
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
  | S.Psig_type (flag,ty_decls) ->
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
  | S.Psig_extension (ext,atts) ->
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
  | S.Pwith_type (lid,ty_decl) ->
      Pwith_type (lid, type_declaration_with_constraint ty_decl)
  | S.Pwith_module (lid1,lid2) ->
      Pwith_module (lid1,lid2)
  | S.Pwith_typesubst ty_decl ->
      Pwith_typesubst (type_declaration_with_constraint ty_decl)
  | S.Pwith_modsubst (s,lid) ->
      Pwith_modsubst (s,lid)

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
  | S.Pmod_functor (s,mod_ty,mod_e) ->
      Pmod_functor (s, map_option module_type mod_ty, module_expr mod_e)
  | S.Pmod_apply (mod_e1,mod_e2) ->
      Pmod_apply (module_expr mod_e1, module_expr mod_e2)
  | S.Pmod_constraint (mod_e,mod_ty) ->
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
  | S.Pstr_eval (e,atts) ->
      [Pstr_eval (expression e, attributes atts)]
  | S.Pstr_value (flag,vbs) ->
      [Pstr_value (flag, value_binding <$> vbs)]
  | S.Pstr_primitive vd ->
      [Pstr_primitive (value_description vd)]
  | S.Pstr_type (flag,tds) ->
      let new_tds = type_declarations tds in
      let getters = tds >>= type_declaration_getters in
      Pstr_type (flag,new_tds) :: getters
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
  | S.Pstr_extension (ext,atts) ->
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

(** {2 Toplevel} *)

(* Toplevel phrases *)

and toplevel_phrase = function
  | S.Ptop_def str ->
      Ptop_def (structure str)
  | S.Ptop_dir (s,dir_arg) ->
      Ptop_dir (s,dir_arg)
