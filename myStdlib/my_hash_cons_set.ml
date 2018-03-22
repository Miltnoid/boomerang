(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  Anders Miltner edited it a bit, and is very confused by licenses...   *)
(*  Ryan Beckett also edited it a bit, and might be confused by licenses  *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Core
open Util
open My_hash_cons

module HSetOf(D : HashConsData) = struct

  type elt = D.t

  type t = t_node hash_consed
  and t_node =
    | Empty
    | Leaf of D.t
    | Branch of int * int * t * t
  [@@deriving ord, show, hash]

  let table = HashConsTable.create 100
  let hashcons = HashConsTable.hashcons hash_t_node compare_t_node table

  let empty = hashcons Empty

  let leaf x = hashcons (Leaf x)

  let branch (i,j,l,r) = hashcons (Branch (i,j,l,r))

  let is_empty k =
    match k.node with
    | Empty -> true
    | _ -> false

  let singleton k = leaf k

  let zero_bit k m = phys_equal (k land m) 0

  let rec mem k t =
    match t.node with
    | Empty -> false
    | Leaf j -> phys_equal k.tag j.tag
    | Branch (_, m, l, r) -> mem k (if zero_bit k.tag m then l else r)

  let lowest_bit x = x land (-x)

  let branching_bit p0 p1 = lowest_bit (p0 lxor p1)

  let mask p m = p land (m-1)

  let unsigned_lt n m = n >= 0 && (m < 0 || n < m)

  let join (p0,t0,p1,t1) =
    let m = branching_bit p0 p1 in
    if zero_bit p0 m then
      branch (mask p0 m, m, t0, t1)
    else
      branch (mask p0 m, m, t1, t0)

  let match_prefix k p m = phys_equal (mask k m) p

  let add k t =
    let rec ins t =
      match t.node with
      | Empty -> leaf k
      | Leaf j ->
          if phys_equal j.tag k.tag then t else join (k.tag, leaf k, j.tag, t)
      | Branch (p,m,t0,t1) ->
          if match_prefix k.tag p m then
            if zero_bit k.tag m
            then branch (p, m, ins t0, t1)
            else branch (p, m, t0, ins t1)
          else
            join (k.tag, leaf k, p, t)
    in ins t

  let branch x =
    match x with
    | (_,_,{node=Empty},t) -> t
    | (_,_,t,{node=Empty}) -> t
    | (p,m,t0,t1) -> branch (p,m,t0,t1)

  let remove k t =
    let rec rmv t =
      match t.node with
      | Empty -> empty
      | Leaf j -> if phys_equal k.tag j.tag then empty else t
      | Branch (p,m,t0,t1) ->
          if match_prefix k.tag p m then
            if zero_bit k.tag m
            then branch (p, m, rmv t0, t1)
            else branch (p, m, t0, rmv t1)
          else t
    in rmv t

  let rec merge (s,t) : t =
    match s.node, t.node with
    | Empty, _  -> t
    | _, Empty  -> s
    | Leaf k, _ -> add k t
    | _, Leaf k -> add k s
    | Branch (p,m,s0,s1), Branch (q,n,t0,t1) ->
        if phys_equal m n && match_prefix q p m then
          (* The trees have the same prefix. Merge the subtrees. *)
          branch (p, m, merge (s0,t0), merge (s1,t1))
        else if unsigned_lt m n && match_prefix q p m then
          (* [q] contains [p]. Merge [t] with a subtree of [s]. *)
          if zero_bit q m then
            branch (p, m, merge (s0,t), s1)
                else
            branch (p, m, s0, merge (s1,t))
        else if unsigned_lt n m && match_prefix p q n then
          (* [p] contains [q]. Merge [s] with a subtree of [t]. *)
          if zero_bit p n then
            branch (q, n, merge (s,t0), t1)
          else
            branch (q, n, t0, merge (s,t1))
        else
          (* The prefixes disagree. *)
          join (p, s, q, t)

  let union s t = merge (s,t)

  let rec subset s1 s2 =
    match (s1.node,s2.node) with
    | Empty, _ -> true
    | _, Empty -> false
    | Leaf k1, _ -> mem k1 s2
    | Branch _, Leaf _ -> false
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
        if phys_equal m1 m2 && phys_equal p1 p2 then
          subset l1 l2 && subset r1 r2
        else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
          if zero_bit p1 m2 then
            subset l1 l2 && subset r1 l2
          else
            subset l1 r2 && subset r1 r2
        else
          false

  let rec inter s1 s2 =
    match (s1.node,s2.node) with
    | Empty, _ -> empty
    | _, Empty -> empty
    | Leaf k1, _ -> if mem k1 s2 then s1 else empty
    | _, Leaf k2 -> if mem k2 s1 then s2 else empty
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
        if phys_equal m1 m2 && phys_equal p1 p2 then
          merge (inter l1 l2, inter r1 r2)
        else if unsigned_lt m1 m2 && match_prefix p2 p1 m1 then
          inter (if zero_bit p2 m1 then l1 else r1) s2
        else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
          inter s1 (if zero_bit p1 m2 then l2 else r2)
        else
          empty

  let rec diff s1 s2 =
    match (s1.node,s2.node) with
    | Empty, _ -> empty
    | _, Empty -> s1
    | Leaf k1, _ -> if mem k1 s2 then empty else s1
    | _, Leaf k2 -> remove k2 s1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
        if phys_equal m1 m2 && phys_equal p1 p2 then
          merge (diff l1 l2, diff r1 r2)
        else if unsigned_lt m1 m2 && match_prefix p2 p1 m1 then
          if zero_bit p2 m1 then
            merge (diff l1 s2, r1)
          else
            merge (l1, diff r1 s2)
        else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
          if zero_bit p1 m2 then diff s1 l2 else diff s1 r2
              else
          s1

  let rec cardinal t =
    match t.node with
    | Empty -> 0
    | Leaf _ -> 1
    | Branch (_,_,t0,t1) -> cardinal t0 + cardinal t1

  let rec iter f t =
    match t.node with
    | Empty -> ()
    | Leaf k -> f k
    | Branch (_,_,t0,t1) -> iter f t0; iter f t1

  let rec fold f s accu =
    match s.node with
    | Empty -> accu
    | Leaf k -> f k accu
    | Branch (_,_,t0,t1) -> fold f t0 (fold f t1 accu)

  let rec for_all p t =
    match t.node with
    | Empty -> true
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> for_all p t0 && for_all p t1

  let rec exists p t =
    match t.node with
    | Empty -> false
    | Leaf k -> p k
    | Branch (_,_,t0,t1) -> exists p t0 || exists p t1

  let rec filter pr t =
    match t.node with
    | Empty -> empty
    | Leaf k -> if pr k then t else empty
    | Branch (p,m,t0,t1) -> branch (p, m, filter pr t0, filter pr t1)

  let partition p s =
    let rec part (t,f as acc) s =
      match s.node with
      | Empty -> acc
      | Leaf k -> if p k then (add k t, f) else (t, add k f)
      | Branch (_,_,t0,t1) -> part (part acc t0) t1
    in
    part (empty, empty) s

  let rec choose t =
    match t.node with
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_, _,t0,_) -> choose t0   (* we know that [t0] is non-empty *)

  let elements s =
    let rec elements_aux acc t =
      match t.node with
      | Empty -> acc
      | Leaf k -> k :: acc
      | Branch (_,_,l,r) -> elements_aux (elements_aux acc l) r
    in
    elements_aux [] s

  let rec min_elt t =
    match t.node with
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_,_,s,t) -> min (min_elt s) (min_elt t)

  let rec max_elt t =
    match t.node with
    | Empty -> raise Not_found
    | Leaf k -> k
    | Branch (_,_,s,t) -> max (max_elt s) (max_elt t)

  let equal x y = x.tag = y.tag

  let compare x y = x.tag - y.tag

  let hash x = x.hkey

  let show t =
    let aux x acc = (D.show x) ^ (if acc = "" then acc else "," ^ acc) in
    let elts = fold aux t "" in
    "{" ^ elts ^ "}"

  let make l = List.fold_right ~f:add ~init:empty l

  let rec intersect s1 s2 =
    match (s1.node,s2.node) with
    | Empty, _ -> false
    | _, Empty -> false
    | Leaf k1, _ -> mem k1 s2
    | _, Leaf k2 -> mem k2 s1
    | Branch (p1,m1,l1,r1), Branch (p2,m2,l2,r2) ->
        if phys_equal m1 m2 && phys_equal p1 p2 then
          intersect l1 l2 || intersect r1 r2
        else if unsigned_lt m1 m2 && match_prefix p2 p1 m1 then
          intersect (if zero_bit p2 m1 then l1 else r1) s2
        else if unsigned_lt m2 m1 && match_prefix p1 p2 m2 then
          intersect s1 (if zero_bit p1 m2 then l2 else r2)
        else
          false

end
