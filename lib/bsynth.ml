(******************************************************************************)
(* The Harmony Project                                                        *)
(* harmony@lists.seas.upenn.edu                                               *)
(******************************************************************************)
(* Copyright (C) 2008 J. Nathan Foster and Benjamin C. Pierce                 *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(******************************************************************************)
(* /src/bvalue.ml                                                             *)
(* Boomerang run-time values                                                  *)
(* $Id: bvalue.ml 4998 2011-03-16 21:53:34Z mgree $ *)
(******************************************************************************)

open Ubase
open Hbase

open Bsyntax
open Bident
open Benv

open Stdlib
open Optician 
open Regexcontext
open Lenscontext
open Lang

module Info = Hbase.Info
module MLens = Blenses.MLens

let to_boomerang_regex : Regex.t -> Brx.t =
  Regex.fold
    ~empty_f:Brx.empty
    ~base_f:Brx.mk_string
    ~concat_f:Brx.mk_seq
    ~or_f:Brx.mk_alt
    ~star_f:Brx.mk_star
    ~dist_f:(ident)

let to_boomerang_lens
    (i:Info.t)
  : Lens.t -> MLens.t =
  Lens.fold
    ~const_f:(fun s1 s2 ->
        Blenses.MLens.clobber
          i
          (Brx.mk_string s1)
          s2
          (fun _ -> s1))
    ~concat_f:(Blenses.MLens.concat i)
    ~swap_f:(fun l1 l2 ->
        MLens.permute i [1;0] [l1;l2])
    ~union_f:(MLens.union i)
    ~compose_f:(MLens.compose i)
    ~iterate_f:(MLens.star i)
    ~identity_f:((MLens.copy i) % to_boomerang_regex)
    ~inverse_f:(MLens.invert i)
    ~permute_f:(fun il ml -> MLens.permute i (Permutation.to_int_list il) ml)

let populate_lens_context
    (relevant_regexps:Brx.t list)
    (e:CEnv.t)
  : Lenscontext.LensContext.t =
  let lens_list =
    List.filter_map
      ~f:ident
      (CEnv.fold
         (fun _ (_,v) acc -> (Bvalue.get_l_safe v)::acc)
         e
         [])
  in
  let bij_lens_list =
    List.filter
      ~f:Blenses.MLens.bij
      lens_list
  in
  let lo = List.hd bij_lens_list in
  print_endline (string_of_int (List.length bij_lens_list));
  print_endline (string_of_int (List.length relevant_regexps));
  print_endline "BOPPERS";
  List.iter
    ~f:(fun x ->
        print_endline "\n\n\nBOPPER:";
        print_endline (Brx.string_of_t x);
        let cex =
          Option.map
          ~f:(fun l -> Brx.disjoint_cex
            ((Blenses.MLens.stype l))
            (Brx.mk_complement x))
          lo
        in
        begin match cex with
          | None -> ()
          | Some None -> print_endline "HUH"
          | Some Some s ->
            print_endline s
        end)
    (List.filter
       ~f:(fun r -> (not (Brx.is_empty (Brx.derivative r "BOP"))) && (Brx.is_empty (Brx.derivative r "POB")))
       relevant_regexps)
    ;
  let lenses_types =
    List.filter_map
      ~f:(fun l ->
          print_endline "\n\n\n\nsrc";
          print_endline (Brx.string_of_t (Blenses.MLens.stype l));
          print_endline (Brx.string_of_t (Blenses.MLens.vtype l));
          let stype_o =
            List.find
              ~f:(Brx.equiv (Blenses.MLens.stype l))
              relevant_regexps
          in
          print_endline (string_of_bool (is_none stype_o));
          let vtype_o =
            List.find
              ~f:(Brx.equiv (Blenses.MLens.vtype l))
              relevant_regexps
          in
          print_endline (string_of_bool (is_none vtype_o));
          begin match (stype_o,vtype_o) with
            | (Some stype, Some vtype) -> Some (l,stype,vtype)
            | _ -> None
          end)
      bij_lens_list
  in

  print_endline (string_of_int (List.length lenses_types));

  let optician_lenses_types =
    List.filter_map
      ~f:(fun (l,s,v) ->
          let l_o = Blenses.MLens.to_optician_lens l in
          if Option.is_none l_o then print_endline "deep" else print_endline "peed";
          Option.map
            ~f:(fun l ->
                (l
                ,Brx.to_optician_regexp s
                ,Brx.to_optician_regexp v))
            l_o)
      lenses_types
  in

  LensContext.insert_list_exn LensContext.empty optician_lenses_types

let synth
    (i:Info.t)
    (env:CEnv.t)
    (r1:Brx.t)
    (r2:Brx.t)
    (exs:(string * string) list)
  : Blenses.MLens.t =
  let relevant_components =
    (Brx.relevant_component_list r1)
    @ (Brx.relevant_component_list r2)
  in
  let r1 = Brx.to_optician_regexp r1 in
  let r2 = Brx.to_optician_regexp r2 in
  let lc = populate_lens_context relevant_components env in
  to_boomerang_lens
    i
    (Option.value_exn
       (Gen.gen_lens
          lc
          r1
          r2
          exs))
