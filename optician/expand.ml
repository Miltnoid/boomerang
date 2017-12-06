open Stdlib
open Lang
open Lenscontext
open Regexcontext
open Synth_structs
open Consts
open Normalized_lang

(***** Helper Functions {{{ *****)
let get_rep_var
    (lc:LensContext.t)
    (ud:Id.t)
  : Id.t =
  if !use_lens_context then
    (fst (LensContext.shortest_path_to_rep_elt lc ud))
  else
    ud

type ill = int list list

type 'a openable_datad = opened:bool -> openable:OpenableData.t -> 'a

let ignore_openable_data
    (type a)
    (x:a)
    ~opened:(_:bool)
    ~openable:(_:OpenableData.t)
  : a =
  x

let star_depth_regex_fold
    ~base_f:(base_f:(int -> string -> 'a) openable_datad)
    ~concat_f:(concat_f:(int -> 'a -> 'a -> 'a) openable_datad)
    ~union_f:(union_f:(int -> 'a list -> 'a) openable_datad)
    ~star_f:(star_f:(int -> 'a -> 'a) openable_datad)
    ~diff_f:(diff_f:(int -> 'a -> 'a -> 'a) openable_datad)
    ~inter_f:(inter_f:(int -> 'a list -> 'a) openable_datad)
    (r:ExampledRegex.t)
  : 'a =

  let ignore_ill
      (type a)
      (x:a)
      ~ill:(ill:ill)
    : a =
    x
  in

  ExampledRegex.fold_downward_upward
    ~init:0
    ~upward_base:(ignore_ill base_f)
    ~upward_concat:(ignore_ill concat_f)
    ~upward_union:(ignore_ill union_f)
    ~upward_star:(ignore_ill star_f)
    ~upward_diff:(ignore_ill diff_f)
    ~upward_inter:(ignore_ill inter_f)
    ~downward_star:(ExampledRegex.ignore_data (fun d -> d+1))
    r

let clean_example_openable
    (openable:OpenableData.t)
  : OpenableData.t =
  begin match openable with
    | OpenableData.True -> OpenableData.True
    | OpenableData.False _ -> OpenableData.False []
  end

let clean_creation
    (type a)
    (f:ill:ill -> ?opened:bool -> openable:OpenableData.t -> a)
    ~opened:(opened:bool)
    ~openable:(openable:OpenableData.t)
  : a =
  let openable = clean_example_openable openable in
  f
    ~ill:[]
    ~opened:opened
    ~openable:openable


let clean_example_data : ExampledRegex.t -> ExampledRegex.t =
  let ignore_ill
      (type a)
      (x:a)
      ~ill:(ill:ill)
    : a =
    x
  in

  ExampledRegex.fold
    ~base_f:(ExampledRegex.ignore_data (fun s ->
        ExampledRegex.mk_base ~ill:[] s))
    ~concat_f:(ignore_ill (fun ~opened:on ~openable:oa r1 r2 ->
        (clean_creation ExampledRegex.mk_concat)
          ~opened:on
          ~openable:oa
          r1
          r2))
    ~union_f:(ignore_ill (fun ~opened:on ~openable:oa rs ->
        (clean_creation ExampledRegex.mk_union)
          ~opened:on
          ~openable:oa
          rs))
    ~star_f:(ignore_ill (fun ~opened:on ~openable:oa r ->
        (clean_creation ExampledRegex.mk_star)
          ~opened:on
          ~openable:oa
          r))
    ~diff_f:(ExampledRegex.ignore_data (fun r1 r2 ->
        ExampledRegex.mk_diff
          ~ill:[]
          r1
          r2
          []))
    ~inter_f:(ExampledRegex.ignore_data (fun rs ->
        ExampledRegex.mk_inter
          ~ill:[]
          rs
          []))

(***** }}} *****)

(**** GetSets {{{ *****)
module RegexSet = SetOf(ExampledRegex)

module IntSet = SetOf(IntModule)

module RegexIntSet = SetOf(PairOf(ExampledRegex)(IntModule))

module RegexToIntSetDict = DictOf(ExampledRegex)(IntSet)

let get_current_set
    (lc:LensContext.t)
  : ExampledRegex.t -> RegexIntSet.t =
  snd %
  star_depth_regex_fold
    ~base_f:(ignore_openable_data (fun i s ->
        (ExampledRegex.mk_base [] s,RegexIntSet.empty)))
    ~concat_f:(fun
                ~opened:opened
                ~openable:openable
                i
                (r1,s1)
                (r2,s2) ->
                let r =
                  (clean_creation ExampledRegex.mk_concat)
                    ~opened:opened
                    ~openable:openable
                    r1
                    r2
                in
                let s =
                  if opened then
                    RegexIntSet.union
                      s1
                      s2
                  else
                    RegexIntSet.singleton (r,i)
                in
                (r,s))
    ~union_f:(fun
               ~opened:opened
               ~openable:openable
               i
               rss ->
               let (rs,ss) = List.unzip rss in
               let r =
                 (clean_creation ExampledRegex.mk_union)
                   ~opened:opened
                   ~openable:openable
                   rs
               in
               let s =
                 if opened then
                   List.fold_left
                     ~f:(RegexIntSet.union)
                     ~init:RegexIntSet.empty
                     ss
                 else
                   RegexIntSet.singleton (r,i)
               in
               (r,s))
    ~star_f:(fun
              ~opened:opened
              ~openable:openable
              i
              (r,s) ->
              let r =
                (clean_creation ExampledRegex.mk_star)
                  ~opened:opened
                  ~openable:openable
                  r
              in
              let s =
                if opened then
                  RegexIntSet.map
                    ~f:(fun (r,i) -> (r,i+1))
                    s
                else
                  RegexIntSet.singleton (r,i)
              in
              (r,s))
    ~diff_f:(fun
              ~opened:opened
              ~openable:openable
              i
              (r1,s1)
              (r2,s2) ->
              let r =
                ExampledRegex.mk_diff
                  ~ill:[]
                  r1
                  r2
                  []
              in
              let s =
                if opened then
                  RegexIntSet.union
                    s1
                    s2
                else
                  RegexIntSet.singleton (r,i)
              in
              (r,s))
    ~inter_f:(fun
               ~opened:opened
               ~openable:openable
               i
               rss ->
               let (rs,ss) = List.unzip rss in
               let r =
                 ExampledRegex.mk_inter
                   ~ill:[]
                   rs
                   []
               in
               let s =
                 if opened then
                   List.fold_left
                     ~f:(RegexIntSet.union)
                     ~init:RegexIntSet.empty
                     ss
                 else
                   RegexIntSet.singleton (r,i)
               in
               (r,s))

let rec get_transitive_set
    (rc:RegexContext.t)
    (lc:LensContext.t) =
  (*: ExampledRegex.t -> RegexToIntSetDict.t =*)
  (*let rec get_transitive_set_internal
      (star_depth:int)
    : Regex.t -> RegexToIntSetDict.t =*)
  snd %
  star_depth_regex_fold
    ~base_f:(ignore_openable_data (fun i s ->
        (ExampledRegex.mk_base [] s,RegexToIntSetDict.empty)))
    ~concat_f:(fun
                ~opened:opened
                ~openable:openable
                i
                (r1,s1)
                (r2,s2) ->
                let r =
                  (clean_creation ExampledRegex.mk_concat)
                    ~opened:opened
                    ~openable:openable
                    r1
                    r2
                in
                let s =
                  if OpenableData.is_true openable then
                    RegexToIntSetDict.merge_to_dict
                      ~combiner:IntSet.union
                      s1
                      s2
                  else
                    RegexToIntSetDict.empty
                in
                let s =
                  if opened then
                    s
                  else
                    RegexToIntSetDict.insert_or_merge
                      ~merge:IntSet.union
                      s
                      (failwith "TODO get_rep_var lc r")
                      (IntSet.singleton i)
                in
                (r,s))
    ~union_f:(fun
               ~opened:opened
               ~openable:openable
               i
               rss ->
               let (rs,ss) = List.unzip rss in
               let r =
                 (clean_creation ExampledRegex.mk_union)
                   ~opened:opened
                   ~openable:openable
                   rs
               in
               let s =
                 if opened then
                   List.fold_left
                     ~f:(RegexIntSet.union)
                     ~init:RegexIntSet.empty
                     ss
                 else
                   RegexIntSet.singleton (r,i)
               in
               (r,s))
    ~star_f:(ignore_ill (fun
                          ~opened:opened
                          ~openable:openable
                          i
                          (r,s) ->
                          let r =
                            (clean_creation ExampledRegex.mk_star)
                              ~opened:opened
                              ~openable:openable
                              r
                          in
              let s =
                if opened then
                  RegexIntSet.map
                    ~f:(fun (r,i) -> (r,i+1))
                    s
                else
                  RegexIntSet.singleton (r,i)
              in
              (r,s)))
    ~diff_f:(ignore_ill (fun
              ~opened:opened
              ~openable:openable
              i
              (r1,s1)
              (r2,s2) ->
              let r =
                ExampledRegex.mk_diff
                  ~ill:[]
                  r1
                  r2
                  []
              in
              let s =
                if opened then
                  RegexIntSet.union
                    s1
                    s2
                else
                  RegexIntSet.singleton (r,i)
              in
              (r,s)))
    ~inter_f:(ignore_ill (fun
               ~opened:opened
               ~openable:openable
               i
               rss ->
               let (rs,ss) = List.unzip rss in
               let r =
                 ExampledRegex.mk_inter
                   ~ill:[]
                   rs
                   []
               in
               let s =
                 if opened then
                   List.fold_left
                     ~f:(RegexIntSet.union)
                     ~init:RegexIntSet.empty
                     ss
                 else
                   RegexIntSet.singleton (r,i)
               in
               (r,s)))
    (*star_depth_regex_fold
      ~init_depth:0
      ~base_f:(ExampledRegex.ignore_data (fun i s -> IdToIntSetDict.empty))
      ~concat_f:(fun _ s1 s2 ->
          IdToIntSetDict.merge_to_dict
            ~combiner:IntSet.union
            s1
            s2)
      ~or_f:(fun _ s1 s2 ->
          IdToIntSetDict.merge_to_dict
            ~combiner:IntSet.union
            s1
            s2)
      ~star_f:(fun _ -> ident)
      ~var_f:(fun star_depth v ->
          let iterative_values =
            begin match RegexContext.lookup_for_expansion_exn rc v with
              | None -> IdToIntSetDict.empty
              | Some r -> get_transitive_set_internal star_depth r
            end
          in
          IdToIntSetDict.insert_or_merge
            ~merge:IntSet.union
            iterative_values
            (get_rep_var lc v)
            (IntSet.singleton star_depth))*)
  (*get_transitive_set_internal 0*)

let reachables_set_minus
    (set1:IdToIntSetDict.t)
    (set2:IdToIntSetDict.t)
  : IdIntSet.t * IdIntSet.t =
  let set_combiner
      (s1:IntSet.t)
      (s2:IntSet.t)
    : ((IntSet.t,IntSet.t) either) option =
    let max_s1 = IntSet.max_exn s1 in
    let max_s2 = IntSet.max_exn s2 in
    let c = IntSet.compare_elt max_s1 max_s2 in
    if is_equal c then
      None
    else if is_lt c then
      Some
        (Right
           (IntSet.filter
              ~f:(fun x ->
                  is_gt (IntSet.compare_elt x max_s1))
              s2))
    else
      Some
        (Left
           (IntSet.filter
              ~f:(fun x ->
                  is_gt (IntSet.compare_elt x max_s2))
              s1))
  in
  let problem_elts_options_list =
    IdToIntSetDict.merge
      ~combiner:set_combiner
      ~only_d1_fn:(fun s -> Some (Left s))
      ~only_d2_fn:(fun s -> Some (Right s))
      set1
      set2
  in
  let problem_elts_list =
    List.filter_map
      ~f:(fun (k,vo) ->
          Option.map
            ~f:(fun ev ->
                begin match ev with
                  | Left v -> Left (k,v)
                  | Right v -> Right (k,v)
                end)
            vo)
      problem_elts_options_list
  in
  let lr_problem_elts =
    split_by_either
      problem_elts_list
  in
  pair_apply
    ~f:(fun (kss:(Id.t * IntSet.t) list) ->
        List.fold_left
          ~f:(fun (acc:IdIntSet.t) ((k,s):(Id.t * IntSet.t)) ->
              IntSet.fold
                ~f:(fun (i:int) (acc:IdIntSet.t) ->
                    IdIntSet.insert (k,i) acc)
                ~init:acc
                s
            )
          ~init:IdIntSet.empty
          kss)
    lr_problem_elts




(***** }}} *****)



(**** ForceExpand {{{ *****)
let force_expand
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (problem_elts:IdIntSet.t)
  : ExampledRegex.t -> (ExampledRegex.t * int) =
  let rec force_expand_internal
      (star_depth:int)
      (r:ExampledRegex.t)
    : (ExampledRegex.t * int) =
    star_depth_regex_fold
      ~init_depth:star_depth
      ~empty_f:(fun _ -> (Regex.make_empty,0))
      ~base_f:(fun _ s -> (Regex.make_base s,0))
      ~concat_f:(fun _ (lr,le) (rr,re) ->
          (Regex.make_concat lr rr, le+re))
      ~or_f:(fun _ (lr,le) (rr,re) ->
          (Regex.make_or lr rr, le+re))
      ~star_f:(fun _ (r,e) ->
          (Regex.make_star r, e))
      ~var_f:(fun star_depth v ->
          if IdIntSet.member problem_elts (get_rep_var lc v,star_depth) then
            let r =
              Option.value_exn
                (RegexContext.lookup_for_expansion_exn
                   rc
                   v)
            in
            let (r,e) = force_expand_internal star_depth r in
            (r,e+1)
          else
            (Regex.make_var v,0))
      r
  in
  force_expand_internal 0
(***** }}} *****)




(**** Reveal {{{ *****)
let rec reveal
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (v:Id.t)
    (star_depth:int)
    (r:Regex.t)
  : (Regex.t * int) list =
  begin match r with
    | Regex.RegExVariable v' ->
      if get_rep_var lc v' = v && star_depth = 0 then
        [(Regex.RegExVariable v',0)]
      else
        begin match RegexContext.lookup_for_expansion_exn rc v' with
          | None -> []
          | Some r' ->
            List.map
              ~f:(fun (r,exp) -> (r,exp+1))
              (reveal
                 rc
                 lc
                 v
                 star_depth
                 r')
        end
    | Regex.RegExConcat (r1,r2) ->
      let r1_exposes = reveal rc lc v star_depth r1 in
      let r2_exposes = reveal rc lc v star_depth r2 in
      (List.map
         ~f:(fun (r1e,exp) -> (Regex.RegExConcat (r1e,r2),exp))
         r1_exposes)
      @
      (List.map
         ~f:(fun (r2e,exp) -> (Regex.RegExConcat (r1,r2e),exp))
         r2_exposes)
    | Regex.RegExOr (r1,r2) ->
      let r1_exposes = reveal rc lc v star_depth r1 in
      let r2_exposes = reveal rc lc v star_depth r2 in
      (List.map
         ~f:(fun (r1e,exp) -> (Regex.RegExOr (r1e,r2),exp))
         r1_exposes)
      @
      (List.map
         ~f:(fun (r2e,exp) -> (Regex.RegExOr (r1,r2e),exp))
         r2_exposes)
    | Regex.RegExStar r' ->
      let r'_exposes_with_unfold =
        reveal
          rc
          lc
          v
          star_depth
          r'
      in
      let r'_exposes_underneath =
        reveal
          rc
          lc
          v
          (star_depth-1)
          r'
      in
      let star_r'_exposes_underneath =
        (List.map
           ~f:(fun (r'e,exp) -> (Regex.RegExStar r'e,exp))
           r'_exposes_underneath)
      in
      let unrolled_r'_exposes_left =
        (List.map
           ~f:(fun (r'e,exp) -> (Regex.RegExOr(Regex.RegExBase "", Regex.RegExConcat (r'e, Regex.RegExStar r'e)) ,exp+1))
           r'_exposes_with_unfold)
      in
      let unrolled_r'_exposes_right =
        (List.map
           ~f:(fun (r'e,exp) -> (Regex.RegExOr(Regex.RegExBase "", Regex.RegExConcat (Regex.RegExStar r'e, r'e)) ,exp+1))
           r'_exposes_with_unfold)
      in
      star_r'_exposes_underneath@unrolled_r'_exposes_left@unrolled_r'_exposes_right
    | Regex.RegExEmpty -> []
    | Regex.RegExBase _ -> []
  end
(***** }}} *****)

(**** ExpandOnce {{{ *****)
let expand_once
    (rc:RegexContext.t)
    (qe:QueueElement.t)
  : QueueElement.t list =
  let expanders =
    [StarSemiring.left_unfold_all_stars regex_star_semiring
    ;StarSemiring.right_unfold_all_stars regex_star_semiring
    ;Regex.applies_for_every_applicable_level
        (fun r ->
           option_bind
             ~f:(RegexContext.lookup_for_expansion_exn rc)
             (Regex.separate_var r))]
  in

  let retrieve_new_problems_from_expander
      (transform:ExampledRegex.t -> ExampledRegex.t list)
    : (ExampledRegex.t * ExampledRegex.t) list =
    (List.map
       ~f:(fun le -> (le, QueueElement.get_r2 qe))
       (transform (QueueElement.get_r1 qe)))
    @
    (List.map
       ~f:(fun re -> (QueueElement.get_r1 qe, re))
       (transform (QueueElement.get_r2 qe)))
  in

  let new_problems =
    List.concat_map
      ~f:retrieve_new_problems_from_expander
      expanders
  in

  let new_queue_elements =
    List.map
      ~f:(fun (r1,r2) ->
          QueueElement.make
            ~r1:r1
            ~r2:r2
            ~expansions_performed:((QueueElement.get_expansions_performed qe)+1)
            ~expansions_inferred:(QueueElement.get_expansions_inferred qe)
            ~expansions_forced:(QueueElement.get_expansions_forced qe)
        )
      new_problems
  in

  new_queue_elements
(***** }}} *****)


(**** ExpandRequired {{{ *****)
let expand_required
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (r1:ExampledRegex.t)
    (r2:ExampledRegex.t)
  : (ExampledRegex.t * ExampledRegex.t * int) =
  let r1_transitive_vars = get_transitive_set rc lc r1 in
  let r2_transitive_vars = get_transitive_set rc lc r2 in
  let (left_unreachables,right_unreachables) =
    reachables_set_minus
      r1_transitive_vars
      r2_transitive_vars
  in
  let (r1',e1) = force_expand rc lc left_unreachables r1 in
  let (r2',e2) = force_expand rc lc right_unreachables r2 in
  (r1',r2',e1+e2)
(***** }}} *****)


(**** FixProblemElts {{{ *****)
let fix_problem_elts
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (qe:QueueElement.t)
  : QueueElement.t list =
  let s1 = get_current_set lc (QueueElement.get_r1 qe) in
  let s2 = get_current_set lc (QueueElement.get_r2 qe) in
  let problem_elements =
    (List.map
       ~f:(fun e -> Left e)
       (IdIntSet.as_list (IdIntSet.minus s1 s2)))
    @
    (List.map
       ~f:(fun e -> Right e)
       (IdIntSet.as_list (IdIntSet.minus s2 s1)))
  in
  if List.is_empty problem_elements then
    expand_once
      rc
      qe
  else
    let new_problems =
      List.concat_map
        ~f:(fun se ->
            begin match se with
              | Left (v,star_depth) ->
                let exposes = reveal rc lc v star_depth (QueueElement.get_r2 qe) in
                assert (not (List.is_empty exposes));
                List.map ~f:(fun (e,exp) -> (QueueElement.get_r1 qe,e,exp)) exposes
              | Right (v,star_depth) ->
                let exposes = reveal rc lc v star_depth (QueueElement.get_r1 qe) in
                assert (not (List.is_empty exposes));
                List.map ~f:(fun (e,exp) -> (e,QueueElement.get_r2 qe,exp)) exposes
            end)
        problem_elements
    in
    List.map
      ~f:(fun (r1,r2,exp) ->
          QueueElement.make
            ~r1:r1
            ~r2:r2
            ~expansions_performed:((QueueElement.get_expansions_performed qe) + exp)
            ~expansions_inferred:((QueueElement.get_expansions_inferred qe)+exp)
            ~expansions_forced:(QueueElement.get_expansions_forced qe))
      new_problems
(***** }}} *****)

let expand
    (rc:RegexContext.t)
    (lc:LensContext.t)
    (qe:QueueElement.t)
  : QueueElement.t list =
  if (!use_naive_expansion_search) then
    expand_once
      rc
      qe
  else
    let (r1,r2,exs) =
      expand_required
        rc
        lc
        (QueueElement.get_r1 qe)
        (QueueElement.get_r2 qe)
    in
    if (exs <> 0) then
      [
        QueueElement.make
          ~r1:r1
          ~r2:r2
          ~expansions_performed:((QueueElement.get_expansions_performed qe) + exs)
          ~expansions_inferred:((QueueElement.get_expansions_inferred qe) + exs)
          ~expansions_forced:((QueueElement.get_expansions_forced qe) + exs)
      ]
    else if !use_only_forced_expansions then
      expand_once
        rc
        qe
    else
      fix_problem_elts
        rc
        lc
        qe
