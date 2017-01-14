(**************************************************************************)
(*                                                                        *)
(*                    Make Negative Types Smile Again                     *)
(*                                                                        *)
(*                 Yann Régis-Gianas, Paul Laforgue                       *)
(*                                                                        *)
(**************************************************************************)

open Asttypes
open Parsetree_alpha
open Parsetree

(** {0 Helpers} *)

let map_option f m = match m with
  | None -> None
  | Some x -> Some (f x)

let map_fst f (a,b) = (f a, b)
let map_snd g (a,b) = (a, g b)

let ( >>= ) m f = List.fold_right (fun x acc -> f x @ acc) m []

(** {1 Transformation} *)

module Trans = struct

  open Ast_helper_alpha

  let fresh_var =
    let i = ref 0 in
    fun () ->
      incr i;
      string_of_int !i

  (* let make_obs_name name = {name with txt = name.txt ^ "-o"} *)

  let query_ty res =
    let name = Location.mknoloc @@ Longident.parse "query" in
    Typ.constr name [res]

  let codata =
    let name = Location.mknoloc @@ Longident.parse "codata" in
    Typ.constr name []

  let name_f = "dispatch"

  let ext_ty td =
    let open S in
    let ext_name = {
      td.ptype_name with txt = "%ext_" ^ td.ptype_name.txt
    } in
    let fresh_out = fresh_var () in
    let out_var = Typ.var fresh_out in
    let query = query_ty out_var in
    let params = List.map fst td.ptype_params in
    let ty_lid = {
      td.ptype_name with txt = Longident.parse ("-" ^ td.ptype_name.txt)
    } in
    let arrow_ty =
      Typ.arrow Nolabel (Typ.constr ty_lid (query::params)) out_var
    in
    let poly_arrow = Typ.poly [fresh_out] arrow_ty in
    let field = Type.field (Location.mknoloc name_f) poly_arrow in
    Type.mk ~params:td.ptype_params ~kind:(Ptype_record [field]) ext_name

  let mk_ty_constructor td ext_lid =
    let open S in
    let uname = {
      td.ptype_name with txt = String.uppercase_ascii td.ptype_name.txt
    } in
    let lid = {
      td.ptype_name with txt = Longident.parse ("-" ^ td.ptype_name.txt)
    } in
    let _params = List.map fst td.ptype_params in
    let res = Typ.constr lid (codata :: _params) in
    let arg = Typ.constr ext_lid _params in
    let args = Pcstr_tuple [arg] in
    Type.constructor ~args ~res uname

  let ty_observer td lds =
    let open S in
    let ext_cotype = ext_ty td in
    let lid = {
      td.ptype_name with txt = Longident.parse ("-" ^ td.ptype_name.txt)
    } in
    let constructors = List.map (fun cld ->
        let _params = List.map fst td.ptype_params in
        let query = query_ty cld.pcld_type in
        let res = Typ.constr lid (query :: _params) in
        Type.constructor ~loc:cld.pcld_loc ~attrs:cld.pcld_attributes
          ~res cld.pcld_name
      ) lds in
    let ext_lid = {
      ext_cotype.ptype_name with txt = Longident.parse ext_cotype.ptype_name.txt
    } in
    let ty_constructor = mk_ty_constructor td ext_lid in
    let fresh_out = fresh_var () in
    let cotype = {
      td with
      ptype_name = td.ptype_name;
      ptype_params = (Typ.var fresh_out, Invariant) :: td.ptype_params;
      ptype_kind = Ptype_variant (ty_constructor :: constructors);
    }
    in [cotype; ext_cotype]

  let mk_pat pat = {
    ppat_desc = pat;
    ppat_loc = Location.none;
    ppat_attributes = [];
  }

  let mk_exp e = {
    pexp_desc = e;
    pexp_loc = Location.none;
    pexp_attributes = [];
  }

  let mk_fun p e = mk_exp (Pexp_fun (Nolabel, None, p, e))

  let mk_vb pat exp = {
    pvb_pat = pat;
    pvb_expr = exp ;
    pvb_attributes = [];
    pvb_loc = Location.none;
  }

  let dispatch_app e =
    let dispatch =
      mk_exp (Pexp_ident (Location.mknoloc (Longident.parse "dispatch")))
    in mk_exp (Pexp_apply (dispatch, [(Nolabel,e)]))

  let dispatch_pat =
    let lid = Location.mknoloc (Longident.parse "dispatch") in
    let pat = mk_pat (Ppat_var (Location.mknoloc "dispatch")) in
    mk_pat (Ppat_record ([lid,pat],Closed))

  let getters td lds =
    let uname = S.{             (* 2 *)
        td.ptype_name
        with txt = Longident.parse (String.uppercase_ascii td.ptype_name.txt)
      } in
    let upat = mk_pat (Ppat_construct (uname, Some dispatch_pat)) in
    List.map (fun cld ->
        let k_lid = S.{
            cld.pcld_name with txt = Longident.parse cld.pcld_name.txt
          } in
        let k = mk_exp (Pexp_construct (k_lid,None)) in
        let body = dispatch_app k in
        let full_body = mk_fun upat body in
        let lname = cld.S.pcld_name.txt in
        let b = Bytes.of_string lname in
        Bytes.set b 0 (Char.lowercase_ascii lname.[0]);
        let s = Bytes.to_string b in
        let vpat = mk_pat (Ppat_var (Location.mknoloc s)) in
        mk_vb vpat full_body
      ) lds

  (* let cases_from_cocases cocases = *)
  (*   let act cocase = *)
  (*     let copat = cocase.S.pcc_lhs in *)
  (*     let dest = match copat.S.pcopat_desc with *)
  (*     | (S.Pcopat_destructor (S.{pcopat_desc = S.Pcopat_hole _}, d)) -> d *)
  (*     | _ -> failwith "todo when algo unnesting is ready" *)
  (*     in *)
  (*     let lid = {dest with txt = Longident.parse dest.txt} in *)
  (*     let pat = S.{ *)
  (*         ppat_desc = Ppat_construct (lid,None); *)
  (*         ppat_loc = dest.loc; *)
  (*         ppat_attributes = [] *)
  (*       } *)
  (*     in *)
  (*     let case = S.{ *)
  (*         pc_lhs = pat; *)
  (*         pc_guard = None; *)
  (*         pc_rhs = cocase.S.pcc_rhs; *)
  (*       } *)
  (*     in case *)
  (*   in List.map act cocases *)

  (* let make_obs loc cocases core_ty = *)
  (*   let cases = cases_from_cocases cocases in *)
  (*   let function_ = Exp.function_ ~loc cases in *)
  (*   assert false *)

 end

(** {2 Extension points} *)

let rec attribute (s,p) = (s, payload p)

and extension (s,p) = (s,payload p)

and attributes atts = List.map attribute atts

and payload = function
  | S.PStr str -> PStr (structure str)
  | S.PSig sign -> PSig (signature sign)
  | S.PTyp typ -> PTyp (core_type typ)
  | S.PPat (p,e) -> PPat (pattern p, map_option expression e)

(** {2 Core language} *)

and core_type {S.ptyp_desc; ptyp_loc; ptyp_attributes} = {
  ptyp_desc = core_type_desc ptyp_desc;
  ptyp_loc;
  ptyp_attributes = attributes ptyp_attributes
}

and adapt = Longident.(function
    | Lident s ->
        let l = String.length s in
        Lident (String.sub s 1 (pred l))
    | Ldot (t,s) ->
        let l = String.length s in
        Ldot (t,String.sub s 1 (pred l))
    | Lapply (_,_) -> failwith "adapt::Lapply"
  )

and core_type_desc = function
  | S.Ptyp_any ->
      Ptyp_any
  | S.Ptyp_var s ->
      Ptyp_var s
  | S.Ptyp_arrow (arg, core_ty1, core_ty2) ->
      Ptyp_arrow (arg, core_type core_ty1, core_type core_ty2)
  | S.Ptyp_tuple core_tys ->
      Ptyp_tuple (List.map core_type core_tys)
  | S.Ptyp_constr (lid,core_tys) ->
      let last_lid = Longident.last lid.txt in
      if last_lid.[0] = '!' then
        (* it is a cotype and we have to add a parameter 'codata' *)
        Ptyp_constr (lid, List.map core_type (Trans.codata :: core_tys))
      else if last_lid.[0] = '-' then
        (* it is a cotype but we already added a 'codata' parameter *)
        let new_lid = {lid with txt = adapt lid.txt} in
        Ptyp_constr (new_lid, List.map core_type core_tys)
      else (* it is not a cotype *)
        Ptyp_constr (lid, List.map core_type core_tys)
  | S.Ptyp_object (fields, flag) ->
      let new_fields = List.map (fun (s, atts, core_ty) ->
          (s, attributes atts, core_type core_ty)
        ) fields in
      Ptyp_object (new_fields, flag)
  | S.Ptyp_class (lid, core_tys) ->
      Ptyp_class (lid, List.map core_type core_tys)
  | S.Ptyp_alias (core_ty, s) ->
      Ptyp_alias (core_type core_ty, s)
  | S.Ptyp_variant (r_fields, flag, labels) ->
      let new_r_fields = List.map row_field r_fields in
      Ptyp_variant (new_r_fields, flag, labels)
  | S.Ptyp_poly (ss, core_ty) ->
      Ptyp_poly (ss, core_type core_ty)
  | S.Ptyp_package pkg_ty ->
      Ptyp_package (package_type pkg_ty)
  | S.Ptyp_extension ext ->
      Ptyp_extension (extension ext)

and package_type (lid, pkg) =
  let new_pkg = List.map (map_snd core_type) pkg in
  (lid, new_pkg)

and row_field = function
  | S.Rtag (lbl, atts, empty, core_tys) ->
      let new_core_tys = List.map core_type core_tys in
      let new_atts = attributes atts in
      Rtag (lbl, new_atts, empty, new_core_tys)
  | S.Rinherit core_ty ->
      Rinherit (core_type core_ty)

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
      Ppat_tuple (List.map pattern ps)
  | S.Ppat_construct (lid, p) ->
      Ppat_construct (lid, map_option pattern p)
  | S.Ppat_variant (lbl, p) ->
      Ppat_variant (lbl, map_option pattern p)
  | S.Ppat_record (flds, flag) ->
      let new_flds = List.map (map_snd pattern) flds in
      Ppat_record (new_flds, flag)
  | S.Ppat_array ps ->
      Ppat_array (List.map pattern ps)
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
      let new_vbs = List.map value_binding vbs in
      Pexp_let (rec_flag, new_vbs, expression e)
  | S.Pexp_function cs ->
      Pexp_function (List.map case cs)
  | S.Pexp_fun (lbl,e1,p,e)  ->
      Pexp_fun (lbl, map_option expression e1, pattern p, expression e)
  | S.Pexp_apply (e,es)  ->
      let new_es = List.map (map_snd expression) es in
      Pexp_apply (expression e, new_es)
  | S.Pexp_match (e,cs) ->
      Pexp_match (expression e, List.map case cs)
  | S.Pexp_try (e,cs) ->
      Pexp_try (expression e, List.map case cs)
  | S.Pexp_tuple es ->
      Pexp_tuple (List.map expression es)
  | S.Pexp_construct (lid,e) ->
      Pexp_construct (lid, map_option expression e)
  | S.Pexp_variant (lbl,e) ->
      Pexp_variant (lbl, map_option expression e)
  | S.Pexp_record (flds,e) ->
      let new_flds = List.map (map_snd expression) flds in
      Pexp_record (new_flds, map_option expression e)
  | S.Pexp_field (e,lid) ->
      Pexp_field (expression e,lid)
  | S.Pexp_setfield (e1,lid,e2) ->
      Pexp_setfield (expression e1, lid, expression e2)
  | S.Pexp_array es ->
      Pexp_array (List.map expression es)
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
      Pexp_override (List.map (map_snd expression) xs)
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
      Pexp_newtype (s, expression e)
  | S.Pexp_pack module_e ->
      Pexp_pack (module_expr module_e)
  | S.Pexp_open (flag,lid,e) ->
      Pexp_open (flag, lid, expression e)
  | S.Pexp_extension ext ->
      Pexp_extension (extension ext)
  | S.Pexp_unreachable ->
      Pexp_unreachable
  | S.Pexp_cofunction (_,_) ->
      failwith "MNTSA::cofunction"

and case x = {
  pc_lhs = pattern x.S.pc_lhs;
  pc_guard = map_option expression x.S.pc_guard;
  pc_rhs = expression x.S.pc_rhs;
}

and value_description vd = {
  pval_name = vd.S.pval_name;
  pval_type = core_type vd.S.pval_type;
  pval_prim = vd.S.pval_prim;
  pval_attributes = attributes vd.S.pval_attributes;
  pval_loc = vd.S.pval_loc;
}

and type_declarations tds =
  List.fold_right (fun td acc -> type_declaration td @ acc) tds []

and type_declaration td = match td.S.ptype_kind with
  | S.Ptype_cotype lds ->
      type_declarations (Trans.ty_observer td lds)
  | _ ->
      let ptype_params = List.map (map_fst core_type) td.S.ptype_params in
      let ptype_cstrs = List.map (fun (c_ty1,c_ty2,var) ->
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
  let ptype_params = List.map (map_fst core_type) td.S.ptype_params in
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
      Ptype_variant (List.map constructor_declaration cds)
  | S.Ptype_record lds ->
      Ptype_record (List.map label_declaration lds)
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
      Pcstr_tuple (List.map core_type c_tys)
  | S.Pcstr_record lds ->
      Pcstr_record (List.map label_declaration lds)

and type_extension ty_ext =
  let ptyext_params = List.map (fun (c_ty,var) ->
      (core_type c_ty, var)
    ) ty_ext.S.ptyext_params
  and ptyext_constructors =
    List.map extension_constructor ty_ext.S.ptyext_constructors
  in {
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

and class_type class_ty = {
  pcty_desc = class_type_desc class_ty.S.pcty_desc;
  pcty_loc = class_ty.S.pcty_loc;
  pcty_attributes = attributes class_ty.S.pcty_attributes;
}

and class_type_desc = function
  | S.Pcty_constr (lid,c_tys) ->
      Pcty_constr (lid, List.map core_type c_tys)
  | S.Pcty_signature class_sig ->
      Pcty_signature (class_signature class_sig)
  | S.Pcty_arrow (arg_lb,c_ty,class_ty) ->
      Pcty_arrow (arg_lb, core_type c_ty, class_type class_ty)
  | S.Pcty_extension ext ->
      Pcty_extension (extension ext)

and class_signature csig = {
  pcsig_self = core_type csig.S.pcsig_self;
  pcsig_fields = List.map class_type_field csig.S.pcsig_fields;
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
  let pci_params = List.map (map_fst core_type) class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_expr class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_description class_info =
  let pci_params = List.map (map_fst core_type) class_info.S.pci_params in
  { pci_virt = class_info.S.pci_virt;
    pci_params;
    pci_name = class_info.S.pci_name;
    pci_expr = class_type class_info.S.pci_expr;
    pci_loc = class_info.S.pci_loc;
    pci_attributes = attributes class_info.S.pci_attributes;
  }

and class_type_declaration class_info =
  let pci_params = List.map (map_fst core_type) class_info.S.pci_params in
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
      Pcl_constr (lid, List.map core_type c_tys)
  | S.Pcl_structure class_struct ->
      Pcl_structure (class_structure class_struct)
  | S.Pcl_fun (arg_lb,e,p,class_e) ->
      let new_class_e = class_expr class_e in
      let new_p = pattern p in
      Pcl_fun (arg_lb, map_option expression e, new_p, new_class_e)
  | S.Pcl_apply (class_e,ls) ->
      Pcl_apply (class_expr class_e, List.map (map_snd expression) ls)
  | S.Pcl_let (flag,vbs,class_e) ->
      Pcl_let (flag, List.map value_binding vbs, class_expr class_e)
  | S.Pcl_constraint (class_e,class_ty) ->
      Pcl_constraint (class_expr class_e, class_type class_ty)
  | S.Pcl_extension ext ->
      Pcl_extension (extension ext)

and class_structure class_str = {
  pcstr_self = pattern class_str.S.pcstr_self;
  pcstr_fields = List.map class_field class_str.S.pcstr_fields;
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
      Pmty_with (module_type mty, List.map with_constraint wcs)
  | S.Pmty_typeof mod_e ->
      Pmty_typeof (module_expr mod_e)
  | S.Pmty_extension ext ->
      Pmty_extension (extension ext)
  | S.Pmty_alias lid ->
      Pmty_alias lid

and signature sig_items = List.map signature_item sig_items

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
      Psig_recmodule (List.map module_declaration mod_declarations)
  | S.Psig_modtype (mod_ty_declaration) ->
      Psig_modtype (module_type_declaration mod_ty_declaration)
  | S.Psig_open od ->
      Psig_open (open_description od)
  | S.Psig_include incl_desc ->
      Psig_include (include_description incl_desc )
  | S.Psig_class class_ds ->
      Psig_class (List.map class_description class_ds)
  | S.Psig_class_type class_ty_ds ->
      Psig_class_type (List.map class_type_declaration class_ty_ds)
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

and structure strs = strs >>= structure_item

and structure_item str = match structure_item_desc str.S.pstr_desc with
  | (pstr_desc,None) -> [{pstr_desc;pstr_loc = str.S.pstr_loc}]
  | (pstr_desc,Some exps) ->
      let str_items = List.map (fun pstr_desc ->
          {pstr_desc; pstr_loc = Location.none}
        ) exps in
      {pstr_desc; pstr_loc = str.S.pstr_loc} :: str_items
      (* List.map (fun e -> fst (fst structure_item_desc e)) exp *)

and structure_item_desc = function
  | S.Pstr_eval (e,atts) ->
      (Pstr_eval (expression e, attributes atts),None)
  | S.Pstr_value (flag,vbs) ->
      (Pstr_value (flag, List.map value_binding vbs),None)
  | S.Pstr_primitive vd ->
      (Pstr_primitive (value_description vd),None)
  | S.Pstr_type (flag,tds) ->
      let (new_tds, exps) = type_declarations0 tds in
      (Pstr_type (flag,new_tds), Some exps)
  | S.Pstr_typext ty_ext ->
      (Pstr_typext (type_extension ty_ext),None)
  | S.Pstr_exception (ext_constructor) ->
      (Pstr_exception (extension_constructor ext_constructor),None)
  | S.Pstr_module mb ->
      (Pstr_module (module_binding mb),None)
  | S.Pstr_recmodule mbs ->
      (Pstr_recmodule (List.map module_binding mbs),None)
  | S.Pstr_modtype mod_ty ->
      (Pstr_modtype (module_type_declaration mod_ty),None)
  | S.Pstr_open od ->
      (Pstr_open (open_description od),None)
  | S.Pstr_class cds ->
      (Pstr_class (List.map class_declaration cds),None)
  | S.Pstr_class_type class_ty_ds ->
      (Pstr_class_type (List.map class_type_declaration class_ty_ds),None)
  | S.Pstr_include id ->
      (Pstr_include (include_declaration id),None)
  | S.Pstr_attribute att ->
      (Pstr_attribute (attribute att),None)
  | S.Pstr_extension (ext,atts) ->
      (Pstr_extension (extension ext, attributes atts),None)

and type_declarations0 tds =
  List.fold_right (fun td (td_acc,exp_acc) ->
      let (new_td,new_exp) = type_declaration0 td in
      match new_exp with
      | None ->
          (new_td @ td_acc, exp_acc)
      | Some exp ->
          (new_td @ td_acc, Pstr_value (Nonrecursive,exp) :: exp_acc)
    ) tds ([],[])

and type_declaration0 td = match td.S.ptype_kind with
  | S.Ptype_cotype lds ->
      let (tys,exp) =
        Trans.(ty_observer td lds, getters td lds)
      in
      (type_declarations tys, Some exp)
  | _ -> (type_declaration td, None)

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

and toplevel_phrase = function
  | S.Ptop_def str ->
      Ptop_def (structure str)
  | S.Ptop_dir (s,dir_arg) ->
      Ptop_dir (s,dir_arg)
