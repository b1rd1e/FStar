(*
   Copyright 2019 Microsoft Research

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

module ParMST

module P = FStar.Preorder

open MST


(*
 * This module provides a semantic model for a combined effect of
 * divergence, state, and parallel composition of atomic actions.
 *
 * It is built over a monotonic state effect -- so that we can give lock semantics using monotonicity
 *
 * It is also be possible to give a variant of this semantics for
 * total correctness. However, we specifically focus on partial correctness
 * here so that this semantics can be instantiated with lock operations,
 * which may deadlock. See ParTot.fst for a total-correctness variant of
 * these semantics.
 *
*)


#push-options "--fuel  0 --ifuel 2 --z3rlimit 20 --print_implicits --print_universes \
   --using_facts_from 'Prims FStar.Pervasives FStar.Preorder MST ParMST'"

(**** Begin state defn ****)


/// We start by defining some basic notions for a commutative monoid.
///
/// We could reuse FStar.Algebra.CommMonoid, but this style with
/// quanitifers was more convenient for the proof done here.


let symmetry #a (equals: a -> a -> prop) =
  forall x y. {:pattern (x `equals` y)}
    x `equals` y ==> y `equals` x

let transitive #a (equals:a -> a -> prop) =
  forall x y z. x `equals` y /\ y `equals` z ==> x `equals` z

let associative #a (equals: a -> a -> prop) (f: a -> a -> a)=
  forall x y z. //{:pattern f x (f y z) \/ f (f x y) z}
    f x (f y z) `equals` f (f x y) z

let commutative #a (equals: a -> a -> prop) (f: a -> a -> a) =
  forall x y.{:pattern f x y}
    f x y `equals` f y x

let is_unit #a (x:a) (equals: a -> a -> prop) (f:a -> a -> a) =
  forall y. {:pattern f x y \/ f y x}
    f x y `equals` y /\
    f y x `equals` y

let equals_ext #a (equals:a -> a -> prop) (f:a -> a -> a) =
  forall x1 x2 y. x1 `equals` x2 ==> f x1 y `equals` f x2 y

let fp_heap_0 (#heap:Type) (#hprop:Type)
              (interp:hprop -> heap -> prop)
              (pre:hprop)
    = h:heap{interp pre h}

noeq
type st0 = {
  heap:Type u#1;
  mem:Type u#1;
  locks_preorder:P.preorder mem;
  hprop:Type u#1;
  heap_of_mem: mem -> heap;
  locks_invariant: mem -> hprop;

  m_disjoint: mem -> heap -> prop;
  disjoint: heap -> heap -> prop;
  join: h0:heap -> h1:heap{disjoint h0 h1} -> heap;
  upd_joined_heap: (m:mem) -> (h:heap{m_disjoint m h}) -> mem;

  interp: hprop -> heap -> prop;

  emp:hprop;
  star: hprop -> hprop -> hprop;

  equals: hprop -> hprop -> prop;
}


/// disjointness is symmetric

let disjoint_sym (st:st0)
  = forall h0 h1. st.disjoint h0 h1 <==> st.disjoint h1 h0

let disjoint_join (st:st0)
  = forall m0 m1 m2.
       st.disjoint m1 m2 /\
       st.disjoint m0 (st.join m1 m2) ==>
       st.disjoint m0 m1 /\
       st.disjoint m0 m2 /\
       st.disjoint (st.join m0 m1) m2 /\
       st.disjoint (st.join m0 m2) m1

let join_commutative (st:st0 { disjoint_sym st })
  = forall m0 m1.
      st.disjoint m0 m1 ==>
      st.join m0 m1 == st.join m1 m0

let join_associative (st:st0{disjoint_join st})
  = forall m0 m1 m2.
      st.disjoint m1 m2 /\
      st.disjoint m0 (st.join m1 m2) ==>
      st.join m0 (st.join m1 m2) == st.join (st.join m0 m1) m2

////////////////////////////////////////////////////////////////////////////////

let interp_extensionality #r #s (equals:r -> r -> prop) (f:r -> s -> prop) =
  forall x y h. {:pattern equals x y; f x h} equals x y /\ f x h ==> f y h

let affine (st:st0) =
  forall r0 r1 s. {:pattern (st.interp (r0 `st.star` r1) s) }
    st.interp (r0 `st.star` r1) s ==> st.interp r0 s

let emp_valid (st:st0) =
  forall s.{:pattern st.interp st.emp s}
    st.interp st.emp s

////////////////////////////////////////////////////////////////////////////////

let m_implies_disjoint (st:st0) =
  forall (m:st.mem) (h1:st.heap).
       st.m_disjoint m h1 ==> st.disjoint (st.heap_of_mem m) h1

let mem_valid_locks_invariant (st:st0) =
  forall (m:st.mem). st.interp (st.locks_invariant m) (st.heap_of_mem m)

let valid_upd_heap (st:st0{m_implies_disjoint st}) =
  forall (m:st.mem) (h:st.heap{st.m_disjoint m h}).
               st.heap_of_mem (st.upd_joined_heap m h) == st.join (st.heap_of_mem m) h /\
               st.locks_invariant m == st.locks_invariant (st.upd_joined_heap m h)

////////////////////////////////////////////////////////////////////////////////
let st_laws (st:st0) =
    (* standard laws about the equality relation *)
    symmetry st.equals /\
    transitive st.equals /\
    interp_extensionality st.equals st.interp /\
    (* standard laws for star forming a CM *)
    associative st.equals st.star /\
    commutative st.equals st.star /\
    is_unit st.emp st.equals st.star /\
    equals_ext st.equals st.star /\
    (* We're working in an affine interpretation of SL *)
    affine st /\
    emp_valid st /\
    (* laws about disjoint and join *)
    disjoint_sym st /\
    disjoint_join st /\
    join_commutative st /\
    join_associative st /\
    (* Relations between mem and heap *)
    m_implies_disjoint st /\
    mem_valid_locks_invariant st /\
    valid_upd_heap st

let st = s:st0 { st_laws s }


(**** End state defn ****)


(**** Begin expects, provides, requires, and ensures defns ****)


/// expects (the heap assertion expected by a computation) is simply an st.hprop
///
/// provides, or the post heap assertion, is a st.hprop on [a]-typed result

let post (st:st) (a:Type) = a -> st.hprop


(**** End expects, provides, requires, and ensures defns ****)

effect Mst (a:Type) (#st:st) (req:st.mem -> Type0) (ens:st.mem -> a -> st.mem -> Type0) =
  MSTATE a st.mem st.locks_preorder req ens



(**** Begin interface of actions ****)

/// Actions are essentially state transformers that preserve frames

let preserves_frame (#st:st) (pre post:st.hprop) (m0 m1:st.mem) =
  forall (frame:st.hprop).
    st.interp (st.locks_invariant m0 `st.star` (pre `st.star` frame)) (st.heap_of_mem m0) ==>
    st.interp (st.locks_invariant m1 `st.star` (post `st.star` frame)) (st.heap_of_mem m1)

let action_t (#st:st) (#a:Type) (pre:st.hprop) (post:post st a) =
  unit ->
  Mst a
  (requires fun m0 ->
    st.interp (st.locks_invariant m0 `st.star` pre) (st.heap_of_mem m0))
  (ensures fun m0 x m1 ->
    st.interp (st.locks_invariant m1 `st.star` (post x)) (st.heap_of_mem m1) /\
    preserves_frame pre (post x) m0 m1)

(**** End interface of actions ****)


(**** Begin definition of the computation AST ****)


noeq
type m (st:st) : a:Type u#a -> pre:st.hprop -> post:post st a -> Type =
  | Ret:
    #a:Type u#a ->
    post:post st a ->
    x:a ->
    m st a (post x) post

  | Bind:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post_a:post st a ->
    #b:Type u#a ->
    #post_b:post st b ->
    f:m st a pre post_a ->
    g:(x:a -> Dv (m st b (post_a x) post_b)) ->
    m st b pre post_b

  | Act:
    #a:Type u#a ->
    #pre:st.hprop ->
    #post:post st a ->
    f:action_t #st #a pre post ->
    m st a pre post

  | Frame:
    #a:Type ->
    #pre:st.hprop ->
    #post:post st a ->
    f:m st a pre post ->
    frame:st.hprop ->
    m st a (pre `st.star` frame) (fun x -> post x `st.star` frame)

  | Par:
    #aL:Type u#a ->
    #preL:st.hprop ->
    #postL:post st aL ->
    mL:m st aL preL postL ->
    #aR:Type u#a ->
    #preR:st.hprop ->
    #postR:post st aR ->
    mR:m st aR preR postR ->
    m st (aL & aR) (preL `st.star` preR) (fun (xL, xR) -> postL xL `st.star` postR xR)

(**** End definition of the computation AST ****)


(**** Stepping relation ****)

/// All steps preserve frames

noeq
type step_result (#st:st) (a:Type u#a) (q:post st a) =
  | Step:
    next_pre:st.hprop ->
    m st a next_pre q ->
    nat ->
    step_result a q


(**** Type of the single-step interpreter ****)


/// Interpreter is setup as a Div function from computation trees to computation trees


unfold
let step_req (#st:st)
  (#a:Type u#a) (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post)
: st.mem -> Type0
= fun m0 ->
  st.interp (st.locks_invariant m0 `st.star` pre) (st.heap_of_mem m0)

unfold
let step_ens (#st:st)
  (#a:Type u#a) (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post)
: st.mem -> step_result a post -> st.mem -> Type0
= fun m0 r m1 ->
  let Step next_pre _ _ = r in
  st.interp (st.locks_invariant m1 `st.star` next_pre) (st.heap_of_mem m1) /\
  preserves_frame pre next_pre m0 m1


(**** Auxiliary lemmas ****)

/// Some AC lemmas on `st.star`

let equals_ext_right (#st:st) (p q r:st.hprop)
: Lemma
  (requires q `st.equals` r)
  (ensures (p `st.star` q) `st.equals` (p `st.star` r))
= calc (st.equals) {
    p `st.star` q;
       (st.equals) { }
    q `st.star` p;
       (st.equals) { }
    r `st.star` p;
       (st.equals) { }
    p `st.star` r;
  }

let commute_star_right (#st:st) (p q r:st.hprop)
: Lemma
  ((p `st.star` (q `st.star` r)) `st.equals`
   (p `st.star` (r `st.star` q)))
= calc (st.equals) {
    p `st.star` (q `st.star` r);
       (st.equals) { equals_ext_right p (q `st.star` r) (r `st.star` q) }
    p `st.star` (r `st.star` q);
  }

let assoc_star_right (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` ((q `st.star` r) `st.star` s)) `st.equals`
   (p `st.star` (q `st.star` (r `st.star` s))))
= calc (st.equals) {
    p `st.star` ((q `st.star` r) `st.star` s);
       (st.equals) { equals_ext_right p ((q `st.star` r) `st.star` s)
                                        (q `st.star` (r `st.star` s)) }
    p `st.star` (q `st.star` (r `st.star` s));
  }

let commute_assoc_star_right (#st:st) (p q r s:st.hprop)
: Lemma
  ((p `st.star` ((q `st.star` r) `st.star` s)) `st.equals`
   (p `st.star` (r `st.star` (q `st.star` s))))
= calc (st.equals) {
    p `st.star` ((q `st.star` r) `st.star` s);
       (st.equals) { equals_ext_right p
                       ((q `st.star` r) `st.star` s)
                       ((r `st.star` q) `st.star` s) }
    p `st.star` ((r `st.star` q) `st.star` s);
       (st.equals) { assoc_star_right p r q s }
    p `st.star` (r `st.star` (q `st.star` s));
  }


/// Apply extensionality manually, control proofs

let apply_interp_ext (#st:st) (p q:st.hprop) (m:st.mem)
: Lemma
  (requires
    st.interp p (st.heap_of_mem m) /\
    p `st.equals` q)
  (ensures st.interp q (st.heap_of_mem m))
= ()


/// Lemmas about preserves_frame

let preserves_frame_trans (#st:st)
  (hp1 hp2 hp3:st.hprop) (m1 m2 m3:st.mem)
: Lemma
  (requires
    preserves_frame hp1 hp2 m1 m2 /\
    preserves_frame hp2 hp3 m2 m3)
  (ensures preserves_frame hp1 hp3 m1 m3)
  [SMTPat (preserves_frame hp1 hp2 m1 m2);
   SMTPat (preserves_frame hp1 hp3 m1 m3)]
= ()

let preserves_frame_star (#st:st) (pre post:st.hprop) (m0 m1:st.mem) (frame:st.hprop)
: Lemma
  (requires preserves_frame pre post m0 m1)
  (ensures preserves_frame (pre `st.star` frame) (post `st.star` frame) m0 m1)
  [SMTPat (preserves_frame pre post m0 m1);
   SMTPat (preserves_frame (pre `st.star` frame) (post `st.star` frame) m0 m1)]
= let aux (frame':st.hprop)
    : Lemma
      (requires
        st.interp (st.locks_invariant m0 `st.star` ((pre `st.star` frame) `st.star` frame')) (st.heap_of_mem m0))
      (ensures
        st.interp (st.locks_invariant m1 `st.star` ((post `st.star` frame) `st.star` frame')) (st.heap_of_mem m1))
    = assoc_star_right (st.locks_invariant m0) pre frame frame';
      apply_interp_ext
        (st.locks_invariant m0 `st.star` ((pre `st.star` frame) `st.star` frame'))
        (st.locks_invariant m0 `st.star` (pre `st.star` (frame `st.star` frame')))
        m0;
      assoc_star_right (st.locks_invariant m1) post frame frame';
      apply_interp_ext
        (st.locks_invariant m1 `st.star` (post `st.star` (frame `st.star` frame')))
        (st.locks_invariant m1 `st.star` ((post `st.star` frame) `st.star` frame'))
        m1
  in
  Classical.forall_intro (Classical.move_requires aux)

let preserves_frame_star_left (#st:st) (pre post:st.hprop) (m0 m1:st.mem) (frame:st.hprop)
: Lemma
  (requires preserves_frame pre post m0 m1)
  (ensures preserves_frame (frame `st.star` pre) (frame `st.star` post) m0 m1)
  [SMTPat (preserves_frame pre post m0 m1);
   SMTPat (preserves_frame (frame `st.star` pre) (frame `st.star` post) m0 m1)]
= let aux (frame':st.hprop)
    : Lemma
      (requires
        st.interp (st.locks_invariant m0 `st.star` ((frame `st.star` pre) `st.star` frame')) (st.heap_of_mem m0))
      (ensures
        st.interp (st.locks_invariant m1 `st.star` ((frame `st.star` post) `st.star` frame')) (st.heap_of_mem m1))
    = commute_assoc_star_right (st.locks_invariant m0) frame pre frame';
      apply_interp_ext
        (st.locks_invariant m0 `st.star` ((frame `st.star` pre) `st.star` frame'))
        (st.locks_invariant m0 `st.star` (pre `st.star` (frame `st.star` frame')))
        m0;
      commute_assoc_star_right (st.locks_invariant m1) frame post frame';
      apply_interp_ext
        (st.locks_invariant m1 `st.star` (post `st.star` (frame `st.star` frame')))
        (st.locks_invariant m1 `st.star` ((frame `st.star` post) `st.star` frame'))
        m1
  in
  Classical.forall_intro (Classical.move_requires aux)

let par_st_interp_r (#st:st) (preL:st.hprop)
  (preR:st.hprop)
  (next_preR:st.hprop)
  (m0 m1:st.mem)
: Lemma
  (requires
    preserves_frame preR next_preR m0 m1 /\
    st.interp (st.locks_invariant m0 `st.star` (preL `st.star` preR)) (st.heap_of_mem m0))
  (ensures
    st.interp (st.locks_invariant m1 `st.star` (preL `st.star` next_preR)) (st.heap_of_mem m1))
  [SMTPat (preserves_frame preR next_preR m0 m1);
   SMTPat (st.interp (st.locks_invariant m1 `st.star` (preL `st.star` next_preR)) (st.heap_of_mem m1))]
= commute_star_right (st.locks_invariant m0) preL preR;
  apply_interp_ext
    (st.locks_invariant m0 `st.star` (preL `st.star` preR))
    (st.locks_invariant m0 `st.star` (preR `st.star` preL))
    m0;
  commute_star_right (st.locks_invariant m1) next_preR preL;
  apply_interp_ext
    (st.locks_invariant m1 `st.star` (next_preR `st.star` preL))
    (st.locks_invariant m1 `st.star` (preL `st.star` next_preR))
    m1

(**** Begin stepping functions ****)

let step_ret (#st:st) (i:nat) (#a:Type u#a)
  (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post{Ret? f})

: Mst (step_result a post) (step_req f) (step_ens f)

= MSTATE?.reflect (fun m0 ->
    let Ret p x = f in
    Step (p x) f i, m0)

let step_bind_ret (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post{Bind? f /\ Ret? (Bind?.f f)})

: Mst (step_result a post) (step_req f) (step_ens f)

= MSTATE?.reflect (fun m0 ->
    match f with
    | Bind (Ret p x) g -> Step (p x) (g x) i, m0)

let step_frame_ret (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#p:post st a)
  (f:m st a pre p{Frame? f /\ Ret? (Frame?.f f)})

: Mst (step_result a p) (step_req f) (step_ens f)

= MSTATE?.reflect (fun m0 ->
    match f with  
    | Frame (Ret p x) frame ->
      Step (p x `st.star` frame)
        (Ret (fun x -> p x `st.star` frame) x)
        i, m0)

let step_par_ret (#st:st) (i:nat)
  (#a:Type) (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post{Par? f /\ Ret? (Par?.mL f) /\ Ret? (Par?.mR f)})

: Mst (step_result a post) (step_req f) (step_ens f)

= MSTATE?.reflect (fun m0 ->
  match f with
  | Par (Ret pL xL) (Ret pR xR) ->

    Step (pL xL `st.star` pR xR)
      (Ret (fun (xL, xR) -> pL xL `st.star` pR xR) (xL, xR))
      i, m0)


/// Stream of booleans to decide whether we go left or right

assume val go_left : nat -> bool


/// Step function

let rec step (#st:st) (i:nat) (#a:Type u#a)
  (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post)
: Mst (step_result a post) (step_req f) (step_ens f)
= match f with
  | Ret _ _ -> step_ret i f
  
  | Act f ->
    let x = f () in
    Step (post x) (Ret post x) i
    
  | Bind (Ret _ _) _ -> step_bind_ret i f
  
  | Bind f g ->
    let Step next_pre f j = step i f in
    Step next_pre (Bind f g) j
    
  | Frame (Ret _ _) _ -> step_frame_ret i f
  
  | Frame f frame ->
    let Step next_fpre f j = step i f in
    Step (next_fpre `st.star` frame) (Frame f frame) j
    
  | Par (Ret _ _) (Ret _ _) -> step_par_ret i f
  
  | Par #_ #_ #preL #_ mL #_ #preR #_ mR ->
    if go_left i then
      let Step next_preL mL j = step (i + 1) mL in

      Step (next_preL `st.star` preR) (Par mL mR) j
    else
      let Step next_preR mR j = step (i + 1) mR in
      Step (preL `st.star` next_preR) (Par mL mR) j


let run_ret (#st:st) (i:nat) (#a:Type u#a) (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post{Ret? f})
: Mst a
  (requires fun m0 ->
    st.interp (st.locks_invariant m0 `st.star` pre) (st.heap_of_mem m0))
  (ensures fun m0 x m1 ->
    st.interp (st.locks_invariant m1 `st.star` post x) (st.heap_of_mem m1) /\
    preserves_frame pre (post x) m0 m1)
= MSTATE?.reflect (fun m0 ->
    let Ret _ x = f in
    x, m0)


let rec run (#st:st) (i:nat) (#a:Type u#a) (#pre:st.hprop) (#post:post st a)
  (f:m st a pre post)
: Mst a
  (requires fun m0 ->
    st.interp (st.locks_invariant m0 `st.star` pre) (st.heap_of_mem m0))
  (ensures fun m0 x m1 ->
    st.interp (st.locks_invariant m1 `st.star` post x) (st.heap_of_mem m1) /\
    preserves_frame pre (post x) m0 m1)
= match f with
  | Ret _ x -> run_ret i f

  | _ ->
    let Step new_pre f j = step i f in
    run j f
