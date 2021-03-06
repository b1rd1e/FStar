﻿(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.Extraction.ML.UEnv
open FStar.ST
open FStar.All
open FStar
open FStar.Util
open FStar.Ident
open FStar.Extraction.ML.Syntax
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker

module U  = FStar.Syntax.Util
module BU = FStar.Util
module Const = FStar.Parser.Const

// JP: my understanding of this is: we either bind a type (left injection) or a
// term variable (right injection). In the latter case, the variable may need to
// be coerced, hence the [mlexpr] (instead of the [mlident]). In order to avoid
// shadowing (which may occur, as the F* normalization potentially breaks the
// original lexical structure of the F* term), we ALSO keep the [mlsymbol], but
// only for the purpose of resolving name collisions.
// The boolean tells whether this is a recursive binding or not.
type ty_binding = {
    ty_b_name: mlident;
    ty_b_ty: mlty
}

type exp_binding = {
    exp_b_name: mlident;
    exp_b_expr: mlexpr;
    exp_b_tscheme: mltyscheme;
    exp_b_inst_ok: bool
}

type ty_or_exp_b = either<ty_binding, exp_binding>

type binding =
    | Bv  of bv * ty_or_exp_b
    | Fv  of fv * exp_binding

type tydef = {
    tydef_fv:fv;
    tydef_mlmodule_name:list<mlsymbol>;
    tydef_name:mlsymbol;
    tydef_mangled_name:option<mlsymbol>;
    tydef_def:mltyscheme
}

type uenv = {
    env_tcenv: TypeChecker.Env.env;
    env_bindings:list<binding>;
    env_mlident_map:psmap<mlident>;
    tydefs:list<tydef>;
    type_names:list<fv>;
    currentModule: mlpath // needed to properly translate the definitions in the current file
}

let debug g f =
    let c = string_of_mlpath g.currentModule in
    if Options.debug_at_level c (Options.Other "Extraction")
    then f ()

// TODO delete
let mkFvvar (l: lident) (t:typ) : fv = lid_as_fv l delta_constant None

(* MLTY_Tuple [] extracts to (), and is an alternate choice.
    However, it represets both the unit type and the unit value. Ocaml gets confused sometimes*)
let erasedContent : mlty = MLTY_Erased

let erasableTypeNoDelta (t:mlty) =
    if t = ml_unit_ty then true
    else match t with
        | MLTY_Named (_, (["FStar"; "Ghost"], "erased")) -> true
        (* erase tactic terms, unless extracting for tactic compilation *)
        | MLTY_Named (_, (["FStar"; "Tactics"; "Effect"], "tactic")) -> Options.codegen () <> Some Options.Plugin
        | _ -> false // this function is used by another function which does delta unfolding

(* \mathbb{T} type in the thesis, to be used when OCaml is not expressive enough for the source type *)
let unknownType : mlty =  MLTY_Top

(*copied from ocaml-strtrans.fs*)
let prependTick x = if BU.starts_with x "'" then x else "'A"^x ///the addition of the space is intentional; it's apparently valid syntax of tvars
let removeTick x = if BU.starts_with x "'" then BU.substring_from x 1 else x

let convRange (r:Range.range) : int = 0 (*FIX!!*)
let convIdent (id:ident) : mlident = id.idText

(* TODO : need to make sure that the result of this name change does not collide with a variable already in the context. That might cause a change in semantics.
   E.g. , consider the following in F*
   let mkPair (a:Type) ('a:Type) (ta : a) (ta' : a') = (ta, ta')

   Perhaps this function also needs to look at env.Gamma*)

(* TODO : if there is a single quote in the name of the type variable, the
 * additional tick in the beginning causes issues with the lexer/parser of OCaml
 * (syntax error).
  Perhaps the type variable is interpreted as a string literal.  For an example,
  see
  https://github.com/FStarLang/FStar/blob/f53844512c76bd67b21b4cf68d774393391eac75/lib/FStar.Heap.fst#L49

   Coq seems to add a space after the tick in such cases. Always adding a space for now
  *)

let bv_as_ml_tyvar x = prependTick (bv_as_mlident x)
let bv_as_ml_termvar x =  removeTick (bv_as_mlident x)

let rec lookup_ty_local (gamma:list<binding>) (b:bv) : mlty =
    match gamma with
        | (Bv (b', Inl ty_b)) :: tl -> if (bv_eq b b') then ty_b.ty_b_ty else lookup_ty_local tl b
        | (Bv (b', Inr _)) :: tl -> if (bv_eq b b') then failwith ("Type/Expr clash: "^(b.ppname.idText)) else lookup_ty_local tl b
        | _::tl -> lookup_ty_local tl b
        | [] -> failwith ("extraction: unbound type var "^(b.ppname.idText))

let tyscheme_of_td (_, _, _, vars, _, body_opt) : option<mltyscheme> =
    match body_opt with
    | Some (MLTD_Abbrev t) -> Some (vars, t)
    | _ -> None

//TODO: this two-level search is pretty inefficient: we should optimize it
let lookup_ty_const (env:uenv) ((module_name, ty_name):mlpath) : option<mltyscheme> =
    BU.find_map env.tydefs  (fun tydef ->
        if ty_name = tydef.tydef_name
        && module_name = tydef.tydef_mlmodule_name
        then Some tydef.tydef_def
        else None)

let module_name_of_fv fv = fv.fv_name.v.ns |> List.map (fun (i:ident) -> i.idText)

let maybe_mangle_type_projector (env:uenv) (fv:fv) : option<mlpath> =
    let mname = module_name_of_fv fv in
    let ty_name = fv.fv_name.v.ident.idText in
    BU.find_map env.tydefs  (fun tydef ->
        if tydef.tydef_name = ty_name
        && tydef.tydef_mlmodule_name = mname
        then match tydef.tydef_mangled_name with
             | None -> Some (mname, ty_name)
             | Some mangled -> Some (mname, mangled)
        else None)

let lookup_tyvar (g:uenv) (bt:bv) : mlty = lookup_ty_local g.env_bindings bt

let lookup_fv_by_lid (g:uenv) (lid:lident) : ty_or_exp_b =
    let x = BU.find_map g.env_bindings (function
        | Fv (fv', x) when fv_eq_lid fv' lid -> Some x
        | _ -> None) in
    match x with
        | None -> failwith (BU.format1 "free Variable %s not found\n" (lid.nsstr))
        | Some y -> Inr y

(*keep this in sync with lookup_fv_by_lid, or call it here. lid does not have position information*)
let try_lookup_fv (g:uenv) (fv:fv) : option<exp_binding> =
    BU.find_map g.env_bindings (function
        | Fv (fv', t) when fv_eq fv fv' -> Some t
        | _ -> None)

let lookup_fv (g:uenv) (fv:fv) : exp_binding =
    match try_lookup_fv g fv with
    | None -> failwith (BU.format2 "(%s) free Variable %s not found\n" (Range.string_of_range fv.fv_name.p) (Print.lid_to_string fv.fv_name.v))
    | Some y -> y

let lookup_bv (g:uenv) (bv:bv) : ty_or_exp_b =
    let x = BU.find_map g.env_bindings (function
        | Bv (bv', r) when bv_eq bv bv' -> Some (r)
        | _ -> None) in
    match x with
        | None -> failwith (BU.format2 "(%s) bound Variable %s not found\n" (Range.string_of_range bv.ppname.idRange) (Print.bv_to_string bv))
        | Some y -> y


let lookup  (g:uenv) (x:either<bv,fv>) : ty_or_exp_b * option<fv_qual> =
    match x with
    | Inl x -> lookup_bv g x, None
    | Inr x -> Inr (lookup_fv g x), x.fv_qual

let lookup_term g (t:term) = match t.n with
    | Tm_name x -> lookup g (Inl x)
    | Tm_fvar x -> lookup g (Inr x)
    | _ -> failwith "Impossible: lookup_term for a non-name"

(* do we really need to keep gamma uptodate with hidden binders? For using F* utils, we just need to keep tcenv update.
 An alternative solution is to remove these binders from the type of the inductive constructors

let extend_hidden_ty (g:env) (a:btvar) (mapped_to:mlty) : env =
    let ml_a = as_mlident a.v in
    let tcenv = Env.push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with tcenv=tcenv}
*)

let extend_ty (g:uenv) (a:bv) (mapped_to:option<mlty>) : uenv =
    let ml_a =  bv_as_ml_tyvar a in
    let mapped_to = match mapped_to with
        | None -> MLTY_Var ml_a
        | Some t -> t in
    let gamma = Bv(a, Inl ({ty_b_name=ml_a; ty_b_ty=mapped_to}))::g.env_bindings in
    let mlident_map = BU.psmap_add g.env_mlident_map ml_a "" in
    let tcenv = TypeChecker.Env.push_bv g.env_tcenv a in // push_local_binding g.tcenv (Env.Binding_typ(a.v, a.sort)) in
    {g with env_bindings=gamma; env_mlident_map=mlident_map; env_tcenv=tcenv}

let sanitize (s:string) : string =
  let cs = FStar.String.list_of_string s in
  let valid c = BU.is_letter_or_digit c || c = '_' || c = '\'' in
  let cs' = List.fold_right (fun c cs -> (if valid c then [c] else ['_';'_'])@cs) cs [] in
  let cs' = match cs' with
            | (c::cs) when BU.is_digit c || c = '\'' ->
                  '_'::c::cs
            | _ -> cs in
  FStar.String.string_of_list cs'


// Need to avoid shadowing an existing identifier (see comment about ty_or_exp_b)
let find_uniq ml_ident_map mlident =
  let mlident = sanitize mlident in

  let rec aux sm mlident i =
    let target_mlident = if i = 0 then mlident else mlident ^ (string_of_int i) in
    match BU.psmap_try_find sm target_mlident with
      | Some x -> aux sm mlident (i+1)
      | None -> target_mlident
  in
  aux ml_ident_map mlident 0

let extend_bv (g:uenv) (x:bv) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
              (mk_unit:bool (*some pattern terms become unit while extracting*))
    : uenv
    * mlident
    * exp_binding =
    let ml_ty = match t_x with
        | ([], t) -> t
        | _ -> MLTY_Top in
    let mlident = find_uniq g.env_mlident_map (bv_as_mlident x) in
    let mlx = MLE_Var mlident in
    let mlx = if mk_unit
              then ml_unit
              else if add_unit
              then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mlx, [ml_unit])
              else with_ty ml_ty mlx in
    let t_x = if add_unit then pop_unit t_x else t_x in
    let exp_binding = {exp_b_name=mlident; exp_b_expr=mlx; exp_b_tscheme=t_x; exp_b_inst_ok=is_rec} in
    let gamma = Bv(x, Inr exp_binding)::g.env_bindings in
    let mlident_map = BU.psmap_add g.env_mlident_map mlident "" in
    let tcenv = TypeChecker.Env.push_binders g.env_tcenv (binders_of_list [x]) in
    {g with env_bindings=gamma; env_mlident_map = mlident_map; env_tcenv=tcenv}, mlident, exp_binding

let rec mltyFvars (t: mlty) : list<mlident>  =
    match t with
    | MLTY_Var  x -> [x]
    | MLTY_Fun (t1, f, t2) -> List.append (mltyFvars t1) (mltyFvars t2)
    | MLTY_Named(args, path) -> List.collect mltyFvars args
    | MLTY_Tuple ts -> List.collect mltyFvars ts
    | MLTY_Top
    | MLTY_Erased -> []

let rec subsetMlidents (la : list<mlident>) (lb : list<mlident>)  : bool =
    match la with
    | h::tla -> List.contains h lb && subsetMlidents tla lb
    | [] -> true

let tySchemeIsClosed (tys : mltyscheme) : bool =
    subsetMlidents  (mltyFvars (snd tys)) (fst tys)

let extend_fv' (g:uenv) (x:fv) (y:mlpath) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
    : uenv
    * mlident
    * exp_binding =
    if tySchemeIsClosed t_x
    then
        let ml_ty = match t_x with
            | ([], t) -> t
            | _ -> MLTY_Top in
        let mlpath, mlsymbol =
          let ns, i = y in
          let mlsymbol = avoid_keyword i in
          (ns, mlsymbol), mlsymbol
        in
        let mly = MLE_Name mlpath in
        let mly = if add_unit then with_ty MLTY_Top <| MLE_App(with_ty MLTY_Top mly, [ml_unit]) else with_ty ml_ty mly in
        let t_x = if add_unit then pop_unit t_x else t_x in
        let exp_binding = {exp_b_name=mlsymbol; exp_b_expr=mly; exp_b_tscheme=t_x; exp_b_inst_ok=is_rec} in
        let gamma = Fv(x, exp_binding)::g.env_bindings in
        let mlident_map = BU.psmap_add g.env_mlident_map mlsymbol "" in
        {g with env_bindings=gamma; env_mlident_map=mlident_map}, mlsymbol, exp_binding
    else failwith "freevars found"

let extend_fv (g:uenv) (x:fv) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
    : uenv
    * mlident
    * exp_binding =
    let mlp = mlpath_of_lident x.fv_name.v in
    // the mlpath cannot be determined here. it can be determined at use site, depending on the name of the module where it is used
    // so this conversion should be moved to lookup_fv

    //let _ = printfn "(* old name  \n %A \n new name \n %A \n name in dependent module \n %A \n *) \n"  (Backends.ML.Syntax.mlpath_of_lident x.v) mlp (mlpath_of_lident ([],"SomeDepMod") x.v) in
    extend_fv' g x mlp t_x add_unit is_rec

let extend_lb (g:uenv) (l:lbname) (t:typ) (t_x:mltyscheme) (add_unit:bool) (is_rec:bool)
    : uenv
    * mlident
    * exp_binding =
    match l with
    | Inl x ->
        // FIXME missing in lib; NS: what does ths mean??
        extend_bv g x t_x add_unit is_rec false
    | Inr f ->
        let p, y = mlpath_of_lident f.fv_name.v in
        extend_fv' g f (p, y) t_x add_unit is_rec

let extend_tydef (g:uenv) (fv:fv) (td:one_mltydecl) : uenv * tydef =
    let m = module_name_of_fv fv in
    let _assumed, name, mangled, vars, metadata, body_opt = td in
    let tydef = {
        tydef_fv = fv;
        tydef_mlmodule_name=m;
        tydef_name = name;
        tydef_mangled_name = mangled;
        tydef_def = Option.get (tyscheme_of_td td);
    } in
    {g with tydefs=tydef::g.tydefs; type_names=fv::g.type_names},
    tydef

let extend_type_name (g:uenv) (fv:fv) : uenv =
    {g with type_names=fv::g.type_names}

let is_type_name g fv = g.type_names |> BU.for_some (fv_eq fv)

let is_fv_type g fv =
    is_type_name g fv ||
    g.tydefs |> BU.for_some (fun tydef -> fv_eq fv tydef.tydef_fv)

let emptyMlPath : mlpath = ([],"")

let mkContext (e:TypeChecker.Env.env) : uenv =
   let env = { env_tcenv = e; env_bindings =[]; env_mlident_map=BU.psmap_empty (); tydefs =[]; type_names=[]; currentModule = emptyMlPath} in
   let a = "'a" in
   let failwith_ty = ([a], MLTY_Fun(MLTY_Named([], (["Prims"], "string")), E_IMPURE, MLTY_Var a)) in
   let g, _, _ =
       extend_lb env (Inr (lid_as_fv Const.failwith_lid delta_constant None)) tun failwith_ty false false
   in
   g

let monad_op_name (ed:Syntax.eff_decl) nm =
    (* Extract bind and return of effects as (unqualified) projectors of that effect, *)
    (* same as for actions. However, extracted code should not make explicit use of them. *)
    let lid = U.mk_field_projector_name_from_ident (ed.mname) (id_of_text nm) in
    (mlpath_of_lident lid), lid

let action_name (ed:Syntax.eff_decl) (a:Syntax.action) =
    let nm = a.action_name.ident.idText in
    let module_name = ed.mname.ns in
    let lid = Ident.lid_of_ids (module_name@[Ident.id_of_text nm]) in
    (mlpath_of_lident lid), lid
