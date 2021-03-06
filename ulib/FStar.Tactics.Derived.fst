(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Tactics.Derived

open FStar.Reflection
open FStar.Reflection.Formula
open FStar.Tactics.Types
open FStar.Tactics.Effect
open FStar.Tactics.Builtins
open FStar.Tactics.Result
open FStar.Tactics.Util
open FStar.Tactics.SyntaxHelpers
module L = FStar.List.Tot

(* Another hook to just run a tactic without goals, just by reusing `with_tactic` *)
let run_tactic (t:unit -> Tac unit)
  : Pure unit
         (requires (set_range_of (with_tactic (fun () -> trivial (); t ()) (squash True)) (range_of t)))
         (ensures (fun _ -> True))
  = ()

let goals () : Tac (list goal) = goals_of (get ())
let smt_goals () : Tac (list goal) = smt_goals_of (get ())

let fail (#a:Type) (m:string) = raise #a (TacticFailure m)

(** Return the current *goal*, not its type. (Ignores SMT goals) *)
let _cur_goal () : Tac goal =
    match goals () with
    | []   -> fail "no more goals"
    | g::_ -> g

(** [cur_env] returns the current goal's environment *)
let cur_env () : Tac env = goal_env (_cur_goal ())

(** [cur_goal] returns the current goal's type *)
let cur_goal () : Tac typ = goal_type (_cur_goal ())

(** [cur_witness] returns the current goal's witness *)
let cur_witness () : Tac term = goal_witness (_cur_goal ())

(** [cur_goal_safe] will always return the current goal, without failing.
It must be statically verified that there indeed is a goal in order to
call it. *)
let cur_goal_safe () : TacH goal (requires (fun ps -> ~(goals_of ps == [])))
                                 (ensures (fun ps0 r -> exists g. r == Success g ps0))
 = match goals_of (get ()) with
   | g :: _ -> g

(** [cur_binders] returns the list of binders in the current goal. *)
let cur_binders () : Tac binders =
    binders_of_env (cur_env ())

(** Set the guard policy only locally, without affecting calling code *)
let with_policy pol (f : unit -> Tac 'a) : Tac 'a =
    let old_pol = get_guard_policy () in
    set_guard_policy pol;
    let r = f () in
    set_guard_policy old_pol;
    r

(** Ignore the current goal. If left unproven, this will fail after
the tactic finishes. *)
let dismiss () : Tac unit =
    match goals () with
    | [] -> fail "dismiss: no more goals"
    | _::gs -> set_goals gs

(** Flip the order of the first two goals. *)
let flip () : Tac unit =
    let gs = goals () in
    match goals () with
    | [] | [_]   -> fail "flip: less than two goals"
    | g1::g2::gs -> set_goals (g2::g1::gs)

(** Succeed if there are no more goals left, and fail otherwise. *)
let qed () : Tac unit =
    match goals () with
    | [] -> ()
    | _ -> fail "qed: not done!"

(** [debug str] is similar to [print str], but will only print the message
if the [--debug] option was given for the current module AND
[--debug_level Tac] is on. *)
let debug (m:string) : Tac unit =
    if debugging () then print m

(** [smt] will mark the current goal for being solved through the SMT.
This does not immediately run the SMT: it just dumps the goal in the
SMT bin. Note, if you dump a proof-relevant goal there, the engine will
later raise an error. *)
let smt () : Tac unit =
    match goals (), smt_goals () with
    | [], _ -> fail "smt: no active goals"
    | g::gs, gs' ->
        begin
        set_goals gs;
        set_smt_goals (g :: gs')
        end

let idtac () : Tac unit = ()

(** Push the current goal to the back. *)
let later () : Tac unit =
    match goals () with
    | g::gs -> set_goals (gs @ [g])
    | _ -> fail "later: no goals"

(** [exact e] will solve a goal [Gamma |- w : t] if [e] has type exactly
[t] in [Gamma]. *)
let exact (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact true false t)

(** [exact_with_ref e] will solve a goal [Gamma |- w : t] if [e] has
type [t'] where [t'] is a subtype of [t] in [Gamma]. This is a more
flexible variant of [exact]. *)
let exact_with_ref (t : term) : Tac unit =
    with_policy SMT (fun () -> t_exact true true t)

(** [apply f] will attempt to produce a solution to the goal by an application
of [f] to any amount of arguments (which need to be solved as further goals).
The amount of arguments introduced is the least such that [f a_i] unifies
with the goal's type. *)
let apply (t : term) : Tac unit =
    t_apply true false t

let apply_noinst (t : term) : Tac unit =
    t_apply true true t

(** [apply_raw f] is like [apply], but will ask for all arguments
regardless of whether they appear free in further goals. See the
explanation in [t_apply]. *)
let apply_raw (t : term) : Tac unit =
    t_apply false false t

(** Like [exact], but allows for the term [e] to have a type [t] only
under some guard [g], adding the guard as a goal. *)
let exact_guard (t : term) : Tac unit =
    with_policy Goal (fun () -> t_exact true false t)

let pointwise  (tau : unit -> Tac unit) : Tac unit = t_pointwise BottomUp tau
let pointwise' (tau : unit -> Tac unit) : Tac unit = t_pointwise TopDown  tau

let cur_module () : Tac name =
    moduleof (top_env ())

let open_modules () : Tac (list name) =
    env_open_modules (top_env ())

let rec repeatn (#a:Type) (n : int) (t : unit -> Tac a) : Tac (list a) =
    if n = 0
    then []
    else t () :: repeatn (n - 1) t

let fresh_uvar (o : option typ) : Tac term =
    let e = cur_env () in
    uvar_env e o

let unify t1 t2 : Tac bool =
    let e = cur_env () in
    unify_env e t1 t2


(** [divide n t1 t2] will split the current set of goals into the [n]
first ones, and the rest. It then runs [t1] on the first set, and [t2]
on the second, returning both results (and concatenating remaining goals). *)
let divide (n:int) (l : unit -> Tac 'a) (r : unit -> Tac 'b) : Tac ('a * 'b) =
    if n < 0 then
      fail "divide: negative n";
    let gs, sgs = goals (), smt_goals () in
    let gs1, gs2 = List.Tot.splitAt n gs in

    set_goals gs1; set_smt_goals [];
    let x = l () in
    let gsl, sgsl = goals (), smt_goals () in

    set_goals gs2; set_smt_goals [];
    let y = r () in
    let gsr, sgsr = goals (), smt_goals () in

    set_goals (gsl @ gsr); set_smt_goals (sgs @ sgsl @ sgsr);
    (x, y)

(** [focus t] runs [t ()] on the current active goal, hiding all others
and restoring them at the end. *)
let focus (t : unit -> Tac 'a) : Tac 'a =
    match goals () with
    | [] -> fail "focus: no goals"
    | g::gs ->
        let sgs = smt_goals () in
        set_goals [g]; set_smt_goals [];
        let x = t () in
        set_goals (goals () @ gs); set_smt_goals (smt_goals () @ sgs);
        x

(** Similar to [dump], but only dumping the current goal. *)
let dump1 (m : string) = focus (fun () -> dump m)

let rec mapAll (t : unit -> Tac 'a) : Tac (list 'a) =
    match goals () with
    | [] -> []
    | _::_ -> let (h, t) = divide 1 t (fun () -> mapAll t) in h::t

let rec iterAll (t : unit -> Tac unit) : Tac unit =
    (* Could use mapAll, but why even build that list *)
    match goals () with
    | [] -> ()
    | _::_ -> let _ = divide 1 t (fun () -> iterAll t) in ()

let iterAllSMT (t : unit -> Tac unit) : Tac unit =
    let gs, sgs = goals (), smt_goals () in
    set_goals sgs;
    set_smt_goals [];
    iterAll t;
    let gs', sgs' = goals (), smt_goals () in
    set_goals gs;
    set_smt_goals (gs'@sgs')

(** Runs tactic [t1] on the current goal, and then tactic [t2] on *each*
subgoal produced by [t1]. Each invocation of [t2] runs on a proofstate
with a single goal (they're "focused"). *)
let seq (f : unit -> Tac unit) (g : unit -> Tac unit) : Tac unit =
    focus (fun () -> f (); iterAll g)

let exact_args (qs : list aqualv) (t : term) : Tac unit =
    focus (fun () ->
        let n = List.length qs in
        let uvs = repeatn n (fun () -> fresh_uvar None) in
        let t' = mk_app t (zip uvs qs) in
        exact t';
        iter (fun uv -> if is_uvar uv
                        then unshelve uv
                        else ()) (L.rev uvs)
    )

let exact_n (n : int) (t : term) : Tac unit =
    exact_args (repeatn n (fun () -> Q_Explicit)) t

(** [ngoals ()] returns the number of goals *)
let ngoals () : Tac int = List.length (goals ())

(** [ngoals_smt ()] returns the number of SMT goals *)
let ngoals_smt () : Tac int = List.length (smt_goals ())

let fresh_bv t : Tac bv =
    (* These bvs are fresh anyway through a separate counter,
     * but adding the integer allows for more readability when
     * generating code *)
    let i = fresh () in
    fresh_bv_named ("x" ^ string_of_int i) t

let fresh_binder_named nm t : Tac binder =
    mk_binder (fresh_bv_named nm t)

let fresh_binder t : Tac binder =
    (* See comment in fresh_bv *)
    let i = fresh () in
    fresh_binder_named ("x" ^ string_of_int i) t

let guard (b : bool) : TacH unit (requires (fun _ -> True))
                                 (ensures (fun ps r -> if b
                                                       then Success? r /\ Success?.ps r == ps
                                                       else Failed? r))
        (* ^ the proofstate on failure is not exactly equal (has the psc set) *)
    =
    if not b then
        fail "guard failed"
    else ()

let try_with (f : unit -> Tac 'a) (h : exn -> Tac 'a) : Tac 'a =
    match catch f with
    | Inl e -> h e
    | Inr x -> x

let trytac (t : unit -> Tac 'a) : Tac (option 'a) =
    try Some (t ())
    with
    | _ -> None

let or_else (#a:Type) (t1 : unit -> Tac a) (t2 : unit -> Tac a) : Tac a =
    try t1 ()
    with | _ -> t2 ()

val (<|>) : (unit -> Tac 'a) ->
            (unit -> Tac 'a) ->
            (unit -> Tac 'a)
let (<|>) t1 t2 = fun () -> or_else t1 t2

let first (ts : list (unit -> Tac 'a)) : Tac 'a =
    L.fold_right (<|>) ts (fun () -> fail "no tactics to try") ()

let rec repeat (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    match catch t with
    | Inl _ -> []
    | Inr x -> x :: repeat t

let repeat1 (#a:Type) (t : unit -> Tac a) : Tac (list a) =
    t () :: repeat t

let repeat' (f : unit -> Tac 'a) : Tac unit =
    let _ = repeat f in ()

let norm_term (s : list norm_step) (t : term) : Tac term =
    let e =
        try cur_env ()
        with | _ -> top_env ()
    in
    norm_term_env e s t

(** Join all of the SMT goals into one. This helps when all of them are
expected to be similar, and therefore easier to prove at once by the SMT
solver. TODO: would be nice to try to join them in a more meaningful
way, as the order can matter. *)
let join_all_smt_goals () =
  let gs, sgs = goals (), smt_goals () in
  set_smt_goals [];
  set_goals sgs;
  repeat' join;
  let sgs' = goals () in // should be a single one
  set_goals gs;
  set_smt_goals sgs'

let discard (tau : unit -> Tac 'a) : unit -> Tac unit =
    fun () -> let _ = tau () in ()

// TODO: do we want some value out of this?
let rec repeatseq (#a:Type) (t : unit -> Tac a) : Tac unit =
    let _ = trytac (fun () -> (discard t) `seq` (discard (fun () -> repeatseq t))) in ()

let tadmit () = tadmit_t (`())

let admit1 () : Tac unit =
    tadmit ()

let admit_all () : Tac unit =
    let _ = repeat tadmit in
    ()

(** [is_guard] returns whether the current goal arised from a typechecking guard *)
let is_guard () : Tac bool =
    Tactics.Types.is_guard (_cur_goal ())

let skip_guard () : Tac unit =
    if is_guard ()
    then smt ()
    else fail ""

let guards_to_smt () : Tac unit =
    let _ = repeat skip_guard in
    ()

let simpl   () : Tac unit = norm [simplify; primops]
let whnf    () : Tac unit = norm [weak; hnf; primops; delta]
let compute () : Tac unit = norm [primops; iota; delta; zeta]

let intros () : Tac (list binder) = repeat intro

let intros' () : Tac unit = let _ = intros () in ()
let destruct tm : Tac unit = let _ = t_destruct tm in ()
let destruct_intros tm : Tac unit = seq (fun () -> let _ = t_destruct tm in ()) intros'

private val __cut : (a:Type) -> (b:Type) -> (a -> b) -> a -> b
private let __cut a b f x = f x

let tcut (t:term) : Tac binder =
    let g = cur_goal () in
    let tt = mk_e_app (`__cut) [t; g] in
    apply tt;
    intro ()

let pose (t:term) : Tac binder =
    apply (`__cut);
    flip ();
    exact t;
    intro ()

let intro_as (s:string) : Tac binder =
    let b = intro () in
    rename_to b s;
    b

let pose_as (s:string) (t:term) : Tac binder =
    let b = pose t in
    rename_to b s;
    b

let for_each_binder (f : binder -> Tac 'a) : Tac (list 'a) =
    map f (cur_binders ())

let rec revert_all (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | _::tl -> revert ();
               revert_all tl

(* Some syntax utility functions *)
let bv_to_term (bv : bv) : Tac term = pack (Tv_Var bv)
let binder_to_term (b : binder) : Tac term = let bv, _ = inspect_binder b in bv_to_term bv

// Cannot define this inside `assumption` due to #1091
private
let rec __assumption_aux (bs : binders) : Tac unit =
    match bs with
    | [] ->
        fail "no assumption matches goal"
    | b::bs ->
        let t = binder_to_term b in
        try exact t with | _ ->
        try (apply (`FStar.Squash.return_squash);
             exact t) with | _ ->
        __assumption_aux bs

let assumption () : Tac unit =
    __assumption_aux (cur_binders ())

let destruct_equality_implication (t:term) : Tac (option (formula * term)) =
    match term_as_formula t with
    | Implies lhs rhs ->
        let lhs = term_as_formula' lhs in
        begin match lhs with
        | Comp (Eq _) _ _ -> Some (lhs, rhs)
        | _ -> None
        end
    | _ -> None

private
let __eq_sym #t (a b : t) : Lemma ((a == b) == (b == a)) =
  FStar.PropositionalExtensionality.apply (a==b) (b==a)

(** Like [rewrite], but works with equalities [v == e] and [e == v] *)
let rewrite' (b:binder) : Tac unit =
    ((fun () -> rewrite b)
     <|> (fun () -> binder_retype b;
                    apply_lemma (`__eq_sym);
                    rewrite b)
     <|> (fun () -> fail "rewrite' failed"))
    ()

let rec try_rewrite_equality (x:term) (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | x_t::bs ->
        begin match term_as_formula (type_of_binder x_t) with
        | Comp (Eq _) y _ ->
            if term_eq x y
            then rewrite x_t
            else try_rewrite_equality x bs
        | _ ->
            try_rewrite_equality x bs
        end

let rec rewrite_all_context_equalities (bs:binders) : Tac unit =
    match bs with
    | [] -> ()
    | x_t::bs -> begin
        (try rewrite x_t with | _ -> ());
        rewrite_all_context_equalities bs
    end

let rewrite_eqs_from_context () : Tac unit =
    rewrite_all_context_equalities (cur_binders ())

let rewrite_equality (t:term) : Tac unit =
    try_rewrite_equality t (cur_binders ())

let unfold_def (t:term) : Tac unit =
    match inspect t with
    | Tv_FVar fv ->
        let n = String.concat "." (inspect_fv fv) in
        norm [delta_fully [n]]
    | _ -> fail "unfold_def: term is not a fv"

(** Rewrites left-to-right, and bottom-up, given a set of lemmas stating equalities.
The lemmas need to prove *propositional* equalities, that is, using [==]. *)
let l_to_r (lems:list term) : Tac unit =
    let first_or_trefl () : Tac unit =
        fold_left (fun k l () ->
                    (fun () -> apply_lemma l)
                    `or_else` k)
                  trefl lems () in
    pointwise first_or_trefl

let mk_squash (t : term) : term =
    let sq : term = pack_ln (Tv_FVar (pack_fv squash_qn)) in
    mk_e_app sq [t]

let mk_sq_eq (t1 t2 : term) : term =
    let eq : term = pack_ln (Tv_FVar (pack_fv eq2_qn)) in
    mk_squash (mk_e_app eq [t1; t2])

let grewrite (t1 t2 : term) : Tac unit =
    let e = tcut (mk_sq_eq t1 t2) in
    let e = pack_ln (Tv_Var (bv_of_binder e)) in
    pointwise (fun () -> try exact e with | _ -> trefl ())

let rec iseq (ts : list (unit -> Tac unit)) : Tac unit =
    match ts with
    | t::ts -> let _ = divide 1 t (fun () -> iseq ts) in ()
    | []    -> ()

private val push1 : (#p:Type) -> (#q:Type) ->
                        squash (p ==> q) ->
                        squash p ->
                        squash q
private let push1 #p #q f u = ()

private val push1' : (#p:Type) -> (#q:Type) ->
                         (p ==> q) ->
                         squash p ->
                         squash q
private let push1' #p #q f u = ()

(*
 * Some easier applying, which should prevent frustation
 * (or cause more when it doesn't do what you wanted to)
 *)
val apply_squash_or_lem : d:nat -> term -> Tac unit
let rec apply_squash_or_lem d t =
    (* Before anything, try a vanilla apply and apply_lemma *)
    try apply t with | _ ->
    try apply (`FStar.Squash.return_squash); apply t with | _ ->
    try apply_lemma t with | _ ->

    // Fuel cutoff, just in case.
    if d <= 0 then fail "mapply: out of fuel" else begin

    let ty = tc (cur_env ()) t in
    let tys, c = collect_arr ty in
    match inspect_comp c with
    | C_Lemma pre post ->
       begin
       let post = norm_term [] post in
       (* Is the lemma an implication? We can try to intro *)
       match term_as_formula' post with
       | Implies p q ->
           apply_lemma (`push1);
           apply_squash_or_lem (d-1) t

       | _ ->
           fail "mapply: can't apply (1)"
       end
    | C_Total rt _ ->
       begin match unsquash rt with
       (* If the function returns a squash, just apply it, since our goals are squashed *)
       | Some rt ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term [] rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             fail "mapply: can't apply (1)"
         end

       (* If not, we can try to introduce the squash ourselves first *)
       | None ->
        // DUPLICATED, refactor!
         begin
         let rt = norm_term [] rt in
         (* Is the lemma an implication? We can try to intro *)
         match term_as_formula' rt with
         | Implies p q ->
             apply_lemma (`push1);
             apply_squash_or_lem (d-1) t

         | _ ->
             apply (`FStar.Squash.return_squash);
             apply t
         end
       end
    | _ -> fail "mapply: can't apply (2)"
    end

(* `m` is for `magic` *)
let mapply (t : term) : Tac unit =
    apply_squash_or_lem 10 t

val admit_dump : #a:Type -> (#[(dump "Admitting"; exact (quote (fun () -> admit #a () <: Admit a)))] x : (unit -> Admit a)) -> unit -> Admit a
let admit_dump #a #x () = x ()

val magic_dump : #a:Type -> (#[(dump "Admitting"; exact (quote (magic #a ())))] x : a) -> unit -> Tot a
let magic_dump #a #x () = x

let change_with t1 t2 : Tac unit =
    focus (fun () ->
        grewrite t1 t2;
        iseq [idtac; trivial]
    )

let change_sq (t1 : term) : Tac unit =
    change (mk_e_app (`squash) [t1])

let finish_by (t : unit -> Tac 'a) : Tac 'a =
    let x = t () in
    or_else qed (fun () -> fail "finish_by: not finished");
    x

let solve_then #a #b (t1 : unit -> Tac a) (t2 : a -> Tac b) : Tac b =
    dup ();
    let x = focus (fun () -> finish_by t1) in
    let y = t2 x in
    trefl ();
    y

let add_elem (t : unit -> Tac 'a) : Tac 'a = focus (fun () ->
    apply (`Cons);
    focus (fun () ->
      let x = t () in
      qed ();
      x
    )
  )

(*
 * Specialize a function by partially evaluating it
 * For example:
 *   let rec foo (l:list int) (x:int) :St int =
       match l with
       | [] -> x
       | hd::tl -> x + foo tl x

     let f :int -> St int = synth_by_tactic (specialize (foo [1; 2]) [%`foo])

 * would make the definition of f as x + x + x
 *
 * f is the term that needs to be specialized
 * l is the list of names to be delta-ed
 *)
let specialize (#a:Type) (f:a) (l:list string) :unit -> Tac unit
  = fun () -> solve_then (fun () -> exact (quote f)) (fun () -> norm [delta_only l; iota; zeta])

let tlabel (l:string) =
    match goals () with
    | [] -> fail "tlabel: no goals"
    | h::t ->
        set_goals (set_label l h :: t)

let tlabel' (l:string) =
    match goals () with
    | [] -> fail "tlabel': no goals"
    | h::t ->
        let h = set_label (l ^ get_label h) h in
        set_goals (h :: t)

let focus_all () : Tac unit =
    set_goals (goals () @ smt_goals ());
    set_smt_goals []

private
let rec extract_nth (n:nat) (l : list 'a) : option ('a * list 'a) =
  match n, l with
  | _, [] -> None
  | 0, hd::tl -> Some (hd, tl)
  | _, hd::tl -> begin
    match extract_nth (n-1) tl with
    | Some (hd', tl') -> Some (hd', hd::tl')
    | None -> None
  end

let bump_nth (n:pos) : Tac unit =
  // n-1 since goal numbering begins at 1
  match extract_nth (n - 1) (goals ()) with
  | None -> fail "bump_nth: not that many goals"
  | Some (h, t) -> set_goals (h :: t)

let on_sort_bv (f : term -> Tac term) (xbv:bv) : Tac bv =
  let bvv = inspect_bv xbv in
  let bvv = { bvv with bv_sort = f bvv.bv_sort } in
  let bv = pack_bv bvv in
  bv

let on_sort_binder (f : term -> Tac term) (b:binder) : Tac binder =
  let (bv, q) = inspect_binder b in
  let bv = on_sort_bv f bv in
  let b = pack_binder bv q in
  b

let rec visit_tm (ff : term -> Tac term) (t : term) : Tac term =
  let tv = inspect_ln t in
  let tv' =
    match tv with
    | Tv_FVar _ -> tv
    | Tv_Var bv ->
        let bv = on_sort_bv (visit_tm ff) bv in
        Tv_Var bv

    | Tv_BVar bv ->
        let bv = on_sort_bv (visit_tm ff) bv in
        Tv_BVar bv

    | Tv_Type () -> Tv_Type ()
    | Tv_Const c -> Tv_Const c
    | Tv_Uvar i u -> Tv_Uvar i u
    | Tv_Unknown -> Tv_Unknown
    | Tv_Arrow b c ->
        let b = on_sort_binder (visit_tm ff) b in
        let c = visit_comp ff c in
        Tv_Arrow b c
    | Tv_Abs b t ->
        let b = on_sort_binder (visit_tm ff) b in
        let t = visit_tm ff t in
        Tv_Abs b t
    | Tv_App l (r, q) ->
         let l = visit_tm ff l in
         let r = visit_tm ff r in
         Tv_App l (r, q)
    | Tv_Refine b r ->
        let r = visit_tm ff r in
        Tv_Refine b r
    | Tv_Let r attrs b def t ->
        let def = visit_tm ff def in
        let t = visit_tm ff t in
        Tv_Let r attrs b def t
    | Tv_Match sc brs ->
        let sc = visit_tm ff sc in
        let brs = map (visit_br ff) brs in
        Tv_Match sc brs
    | Tv_AscribedT e t topt ->
        let e = visit_tm ff e in
        let t = visit_tm ff t in
        Tv_AscribedT e t topt
    | Tv_AscribedC e c topt ->
        let e = visit_tm ff e in
        Tv_AscribedC e c topt
  in
  ff (pack_ln tv')
and visit_br (ff : term -> Tac term) (b:branch) : Tac branch =
  let (p, t) = b in
  (p, visit_tm ff t)
and visit_comp (ff : term -> Tac term) (c : comp) : Tac comp =
  let cv = inspect_comp c in
  let cv' =
    match cv with
    | C_Total ret decr ->
        let ret = visit_tm ff ret in
        let decr =
            match decr with
            | None -> None
            | Some d -> Some (visit_tm ff d)
        in
        C_Total ret decr
    | C_Lemma pre post ->
        let pre = visit_tm ff pre in
        let post = visit_tm ff post in
        C_Lemma pre post
    | C_Unknown -> C_Unknown
  in
  pack_comp cv'

exception NotAListLiteral

let rec destruct_list (t : term) : Tac (list term) =
    let head, args = collect_app t in
    match inspect_ln head, args with
    | Tv_FVar fv, [(a1, Q_Explicit); (a2, Q_Explicit)]
    | Tv_FVar fv, [(_, Q_Implicit); (a1, Q_Explicit); (a2, Q_Explicit)] ->
      if inspect_fv fv = cons_qn
      then a1 :: destruct_list a2
      else raise NotAListLiteral
    | Tv_FVar fv, _ ->
      if inspect_fv fv = nil_qn
      then []
      else raise NotAListLiteral
    | _ ->
      raise NotAListLiteral
