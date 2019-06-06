module LowStar.Permissions.Pointer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq

open LowStar.Resource
open LowStar.RST

open LowStar.BufferOps
open LowStar.Permissions
open FStar.Real

type value_with_perms (a: Type0) = vp : (a & Ghost.erased (value_perms a)){
  let (v, p) = vp in
  forall (pid:live_pid (Ghost.reveal p)). get_snapshot_from_pid (Ghost.reveal p) pid == v
}

noeq type pointer (a: Type0) (perm: permission_kind) = {
  v: B.pointer (value_with_perms a);
  pid: Ghost.erased perm_id
}

let ptr_view (#a:Type) (#perm: permission_kind) (ptr:pointer a perm) : view a = 
  reveal_view ();
  let fp = Ghost.hide (B.loc_addr_of_buffer ptr.v) in 
  let inv h = 
    let (_, perm_map) = Seq.index (B.as_seq h ptr.v) 0 in
    B.live h ptr.v /\ B.freeable ptr.v /\
    get_perm_kind_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.pid) = perm
  in
  let sel h = 
    let (_, perm_map) = Seq.index (B.as_seq h ptr.v) 0 in
    let perm = get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.pid) in
    let snapshot = get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.pid) in
    snapshot
  in
  {
    fp = fp;
    inv = inv;
    sel = sel
  }

let ptr_resource (#a:Type) (#perm: permission_kind) (ptr:pointer a perm) = 
  as_resource (ptr_view ptr)

let ptr_read 
  (#a: Type)
  (#perm: permission_kind)
  (ptr: pointer a perm)
  : RST a 
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> allows_read perm)
    (fun h0 x h1 -> 
      x == sel (ptr_view ptr) h0 /\ 
      sel (ptr_view ptr) h0 == sel (ptr_view ptr) h1
    )
  = 
  let (x, _) = !* ptr.v in
  x

let ptr_write 
  (#a: Type)
  (#perm: permission_kind)
  (ptr: pointer a perm)
  (x: a)
  : RST unit 
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> allows_write perm)
    (fun h0 _ h1 -> sel (ptr_view ptr) h1 == x)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  let (_, perm_map) = !* ptr.v in
  ptr.v *= (x, Ghost.hide (change_snapshot (Ghost.reveal perm_map) x))

let ptr_alloc 
  (#a:Type)
  (init:a)
  : RST (pointer a FULL)
    (empty_resource)
    (fun ptr -> ptr_resource ptr)
    (fun _ -> True)
    (fun _ ptr h1 -> sel (ptr_view ptr) h1 == init)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  let perm_map = Ghost.hide (new_value_perms init) in
  let pid = Ghost.hide 1 in
  let ptr_v = B.malloc HS.root (init, perm_map) 1ul in
  { v = ptr_v; pid = pid }

let ptr_free
  (#a:Type)
  (ptr:pointer a FULL)
  : RST unit
    (ptr_resource ptr)
    (fun ptr -> empty_resource)
    (fun _ -> True )
    (fun _ _ _ -> True)
  =
  reveal_rst_inv ();
  reveal_modifies ();
  reveal_empty_resource ();
  B.free ptr.v

#reset-options

let read_write_without_sharing () : RST unit 
  (empty_resource)
  (fun _ -> empty_resource)
  (fun _ -> True)
  (fun _ _ _ -> True)
  = 
  let ptr = rst_frame 
    (empty_resource)
    (fun ptr -> ptr_resource ptr)
    (fun _ -> ptr_alloc 42ul)
  in
  let x1 = rst_frame 
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> ptr_read ptr)
  in
  rst_frame
    (ptr_resource ptr)
    (fun _ -> ptr_resource ptr)
    (fun _ -> ptr_write ptr FStar.UInt32.(x1 +%^ 1ul));
  rst_frame
    (ptr_resource ptr) 
    (fun _ -> empty_resource)
    (fun _ -> ptr_free ptr);
  ()

