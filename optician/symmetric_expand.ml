open MyStdlib
open Lang
open Lenscontext
open Synth_structs
open Consts

(***** Helper Functions {{{ *****)
let get_rep_var
    (lc:LensContext.t)
    (r:Regex.t)
  : Regex.t =
  if !use_lens_context then
    (fst (LensContext.shortest_path_to_rep_elt lc r))
  else
    r

let stochastic_star_depth_regex_fold
    (type a)
    ~empty_f:(empty_f:int -> a)
    ~base_f:(base_f:int -> string -> a)
    ~concat_f:(concat_f:int -> a -> a -> a)
    ~or_f:(or_f:int -> Probability.t -> a -> a -> a)
    ~star_f:(star_f:int -> Probability.t -> a -> a)
    ~closed_f:(closed_f:int -> StochasticRegex.t -> a -> a)
    (r:StochasticRegex.t)
  : a =
  fst
    (StochasticRegex.fold_downward_upward
       ~init:0
       ~upward_empty:(fun i -> ((empty_f i), StochasticRegex.empty))
       ~upward_base:(fun i s -> (base_f i s, StochasticRegex.make_base s))
       ~upward_concat:(fun i (x1,r1) (x2,r2) ->
           (concat_f i x1 x2
           ,StochasticRegex.make_concat r1 r2))
       ~upward_or:(fun i p (x1,r1) (x2,r2) ->
           (or_f i p x1 x2
           ,StochasticRegex.make_or r1 r2 p))
       ~upward_star:(fun i p (x',r') ->
           (star_f i p x'
           ,StochasticRegex.make_star r' p))
       ~upward_closed:(fun i (x',r') ->
           (closed_f i r' x'
           ,StochasticRegex.make_closed r'))
       ~downward_star:(fun d -> d+1)
       r)

let star_depth_regex_fold
    (type a)
    ~empty_f:(empty_f:int -> a)
    ~base_f:(base_f:int -> string -> a)
    ~concat_f:(concat_f:int -> a -> a -> a)
    ~or_f:(or_f:int -> a -> a -> a)
    ~star_f:(star_f:int -> a -> a)
    ~closed_f:(closed_f:int -> Regex.t -> a -> a)
    (r:Regex.t)
  : a =
  fst
    (Regex.fold_downward_upward
       ~init:0
       ~upward_empty:(fun i -> ((empty_f i), Regex.empty))
       ~upward_base:(fun i s -> (base_f i s, Regex.make_base s))
       ~upward_concat:(fun i (x1,r1) (x2,r2) ->
           (concat_f i x1 x2
           ,Regex.make_concat r1 r2))
       ~upward_or:(fun i (x1,r1) (x2,r2) ->
           (or_f i x1 x2
           ,Regex.make_or r1 r2))
       ~upward_star:(fun i (x',r') ->
           (star_f i x'
           ,Regex.make_star r'))
       ~upward_closed:(fun i (x',r') ->
           (closed_f i r' x'
           ,Regex.make_closed r'))
       ~downward_star:(fun d -> d+1)
       r)

(***** }}} *****)

(**** GetSets {{{ *****)
module IntSet = HCSetOf(IntModule)
module HCRegexInt = HashConsOf(PairOf(Regex)(IntModule))
module RegexIntSet = HCSetOf(HCRegexInt)
module RegexToIntSetDict = HCDictOf(Regex)(IntSet)

let get_current_set
    (lc:LensContext.t)
    (sr:StochasticRegex.t)
  : RegexIntSet.t =
  star_depth_regex_fold
    ~empty_f:(fun _ -> RegexIntSet.empty)
    ~base_f:(fun _ _ -> RegexIntSet.empty)
    ~concat_f:(fun _ s1 s2 ->
        RegexIntSet.union
          s1
          s2)
    ~or_f:(fun _ s1 s2 ->
        RegexIntSet.union
          s1
          s2)
    ~star_f:(fun _ s -> s)
    ~closed_f:(fun i r' _ ->
        let r'' = get_rep_var lc r' in
        RegexIntSet.singleton (HCRegexInt.hashcons (r'',i)))
    (StochasticRegex.to_regex sr)

let rec get_transitive_set
    (lc:LensContext.t)
  : Regex.t -> RegexToIntSetDict.t =
  star_depth_regex_fold
    ~empty_f:(fun _ -> RegexToIntSetDict.empty)
    ~base_f:(fun _ _ -> RegexToIntSetDict.empty)
    ~concat_f:(fun _ s1 s2 ->
        RegexToIntSetDict.merge_to_dict
          ~combiner:IntSet.union
          s1
          s2)
    ~or_f:(fun _ s1 s2 ->
        RegexToIntSetDict.merge_to_dict
          ~combiner:IntSet.union
          s1
          s2)
    ~star_f:(fun _ -> ident)
    ~closed_f:(fun star_depth r s ->
        RegexToIntSetDict.insert_or_combine
          ~combiner:IntSet.union
          s
          (get_rep_var lc r)
          (IntSet.singleton star_depth))

let reachables_set_minus
    (set1:RegexToIntSetDict.t)
    (set2:RegexToIntSetDict.t)
  : RegexIntSet.t * RegexIntSet.t =
  let set_combiner
      (s1:IntSet.t)
      (s2:IntSet.t)
    : ((IntSet.t,IntSet.t) either) option =
    let max_s1 = IntSet.max_exn s1 in
    let max_s2 = IntSet.max_exn s2 in
    let c = Int.compare max_s1 max_s2 in
    if is_equal c then
      None
    else if is_lt c then
      Some
        (Right
           (IntSet.filter
              ~f:(fun x ->
                  is_gt (Int.compare x max_s1))
              s2))
    else
      Some
        (Left
           (IntSet.filter
              ~f:(fun x ->
                  is_gt (Int.compare x max_s2))
              s1))
  in
  let problem_elts_options_list =
    RegexToIntSetDict.merge
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
    ~f:(fun (kss:(Regex.t * IntSet.t) list) ->
        List.fold_left
          ~f:(fun (acc:RegexIntSet.t) ((k,s):(Regex.t * IntSet.t)) ->
              IntSet.fold
                ~f:(fun (i:int) (acc:RegexIntSet.t) ->
                    RegexIntSet.add (HCRegexInt.hashcons (k,i)) acc)
                ~init:acc
                s
            )
          ~init:RegexIntSet.empty
          kss)
    lr_problem_elts




(***** }}} *****)



(**** ForceExpand {{{ *****)
let force_expand
    (lc:LensContext.t)
    (problem_elts:RegexIntSet.t)
    (r:StochasticRegex.t)
  : (StochasticRegex.t * int) =
  stochastic_star_depth_regex_fold
    ~empty_f:(fun _ -> (StochasticRegex.empty,0))
    ~base_f:(fun _ s -> (StochasticRegex.make_base s,0))
    ~concat_f:(fun _ (lr,le) (rr,re) ->
        (StochasticRegex.make_concat lr rr, le+re))
    ~or_f:(fun _ p (lr,le) (rr,re) ->
        (StochasticRegex.make_or lr rr p, le+re))
    ~star_f:(fun _ p (r,e) ->
        (StochasticRegex.make_star r p, e))
    ~closed_f:(fun star_depth r (r_expanded,e) ->
        if RegexIntSet.member
            problem_elts
            (HCRegexInt.hashcons (get_rep_var lc (StochasticRegex.to_regex r),star_depth))
        then
          (r_expanded,e+1)
        else
          (StochasticRegex.make_closed r,0))
    r
(***** }}} *****)




(**** Reveal {{{ *****)
let rec reveal
    (lc:LensContext.t)
    (reveal_ident:Regex.t)
    (star_depth:int)
    (r:StochasticRegex.t)
  : (StochasticRegex.t * int) list =
  begin match StochasticRegex.node r with
    | StochasticRegex.Closed r' ->
      let r'_base = StochasticRegex.to_regex r' in
      if get_rep_var lc r'_base = reveal_ident && star_depth = 0 then
        [(StochasticRegex.make_closed r',0)]
      else
        List.map
          ~f:(fun (r,exp) -> (r,exp+1))
          (reveal
             lc
             reveal_ident
             star_depth
             r')
    | StochasticRegex.Concat (r1,r2) ->
      let r1_exposes = reveal lc reveal_ident star_depth r1 in
      let r2_exposes = reveal lc reveal_ident star_depth r2 in
      (List.map
         ~f:(fun (r1e,exp) -> (StochasticRegex.make_concat r1e r2,exp))
         r1_exposes)
      @
      (List.map
         ~f:(fun (r2e,exp) -> (StochasticRegex.make_concat r1 r2e,exp))
         r2_exposes)
    | StochasticRegex.Or (r1,r2,p) ->
      let r1_exposes = reveal lc reveal_ident star_depth r1 in
      let r2_exposes = reveal lc reveal_ident star_depth r2 in
      (List.map
         ~f:(fun (r1e,exp) -> (StochasticRegex.make_or r1e r2 p,exp))
         r1_exposes)
      @
      (List.map
         ~f:(fun (r2e,exp) -> (StochasticRegex.make_or r1 r2e p,exp))
         r2_exposes)
    | StochasticRegex.Star (r',p) ->
      let r'_exposes_with_unfold =
        reveal
          lc
          reveal_ident
          star_depth
          r'
      in
      let r'_exposes_underneath =
        reveal
          lc
          reveal_ident
          (star_depth-1)
          r'
      in
      let star_r'_exposes_underneath =
        (List.map
           ~f:(fun (r'e,exp) -> (StochasticRegex.make_star r'e p,exp))
           r'_exposes_underneath)
      in
      let unrolled_r'_exposes_left =
        (List.map
           ~f:(fun (r'e,exp) ->
               StochasticStarSemiring.unfold_left
                 stochastic_regex_star_semiring
                 r'e
                 p
               ,exp+1)
           r'_exposes_with_unfold)
      in
      let unrolled_r'_exposes_right =
        (List.map
           ~f:(fun (r'e,exp) ->
               StochasticStarSemiring.unfold_right
                 stochastic_regex_star_semiring
                 r'e
                 p
               ,exp+1)
           r'_exposes_with_unfold)
      in
      star_r'_exposes_underneath@
      unrolled_r'_exposes_left@
      unrolled_r'_exposes_right
    | StochasticRegex.Empty -> []
    | StochasticRegex.Base _ -> []
  end
(***** }}} *****)

(**** ExpandOnce {{{ *****)
let expand_once
    (qe:SymmetricQueueElement.t)
  : SymmetricQueueElement.t list =
  let expanders =
    [StochasticStarSemiring.left_unfold_all_stars stochastic_regex_star_semiring
    ;StochasticStarSemiring.right_unfold_all_stars stochastic_regex_star_semiring
    ;StochasticRegex.applies_for_every_applicable_level
        (fun r -> (StochasticRegex.separate_closed r))]
  in

  let retrieve_new_problems_from_expander
      (transform:StochasticRegex.t -> StochasticRegex.t list)
    : (StochasticRegex.t * StochasticRegex.t) list =
    (List.map
       ~f:(fun le -> (le, SymmetricQueueElement.get_r2 qe))
       (transform (SymmetricQueueElement.get_r1 qe)))
    @
    (List.map
       ~f:(fun re -> (SymmetricQueueElement.get_r1 qe, re))
       (transform (SymmetricQueueElement.get_r2 qe)))
  in

  let new_problems =
    List.concat_map
      ~f:retrieve_new_problems_from_expander
      expanders
  in

  let new_problem_count = List.length new_problems in

  let new_queue_elements =
    List.map
      ~f:(fun (r1,r2) ->
          SymmetricQueueElement.make
            ~r1:r1
            ~r2:r2
            ~expansion_choices:(new_problem_count::(SymmetricQueueElement.get_expansions_choices qe))
            ~expansions_performed:((SymmetricQueueElement.get_expansions_performed qe)+1)
            ~expansions_inferred:(SymmetricQueueElement.get_expansions_inferred qe)
            ~expansions_forced:(SymmetricQueueElement.get_expansions_forced qe)
            ()
          )
      new_problems
  in

  new_queue_elements
(***** }}} *****)


(**** ExpandRequired {{{ *****)
let expand_required
    (lc:LensContext.t)
    (r1:StochasticRegex.t)
    (r2:StochasticRegex.t)
  : (StochasticRegex.t * StochasticRegex.t * int) =
  let r1_transitive_vars =
    get_transitive_set
      lc
      (StochasticRegex.to_regex r1)
  in
  let r2_transitive_vars =
    get_transitive_set
      lc
      (StochasticRegex.to_regex r2)
  in
  let (left_unreachables,right_unreachables) =
    reachables_set_minus
      r1_transitive_vars
      r2_transitive_vars
  in
  let (r1',e1) = force_expand lc left_unreachables r1 in
  let (r2',e2) = force_expand lc right_unreachables r2 in
  (r1',r2',e1+e2)
(***** }}} *****)


(**** FixProblemElts {{{ *****)
let fix_problem_elts
    (lc:LensContext.t)
    (qe:SymmetricQueueElement.t)
  : SymmetricQueueElement.t list =
  let s1 = get_current_set lc (SymmetricQueueElement.get_r1 qe) in
  let s2 = get_current_set lc (SymmetricQueueElement.get_r2 qe) in
  let problem_elements =
    (List.map
       ~f:(fun e -> Left e)
       (RegexIntSet.as_list (RegexIntSet.diff s1 s2)))
    @
    (List.map
       ~f:(fun e -> Right e)
       (RegexIntSet.as_list (RegexIntSet.diff s2 s1)))
  in
  begin match problem_elements with
    | [] ->
      expand_once
        qe
    | h::_ ->
      let new_problems =
        begin match h with
          | Left d ->
            let (v,star_depth) = d.node in
            let exposes = reveal lc v star_depth (SymmetricQueueElement.get_r2 qe) in
            assert (not (List.is_empty exposes));
            List.map ~f:(fun (e,exp) -> (SymmetricQueueElement.get_r1 qe,e,exp)) exposes
          | Right d ->
            let (v,star_depth) = d.node in
            let exposes = reveal lc v star_depth (SymmetricQueueElement.get_r1 qe) in
            assert (not (List.is_empty exposes));
            List.map ~f:(fun (e,exp) -> (e,SymmetricQueueElement.get_r2 qe,exp)) exposes
        end
      in
      let new_problem_count = List.length new_problems in
      List.map
        ~f:(fun (r1,r2,exp) ->
            SymmetricQueueElement.make
              ~r1:r1
              ~r2:r2
              ~expansion_choices:(new_problem_count::(SymmetricQueueElement.get_expansions_choices qe))
              ~expansions_performed:((SymmetricQueueElement.get_expansions_performed qe) + exp)
              ~expansions_inferred:((SymmetricQueueElement.get_expansions_inferred qe)+exp)
              ~expansions_forced:(SymmetricQueueElement.get_expansions_forced qe)
              ())
        new_problems
  end
(***** }}} *****)

let expand
    (lc:LensContext.t)
    (qe:SymmetricQueueElement.t)
  : SymmetricQueueElement.t list =
  if (!use_naive_expansion_search) then
    expand_once
      qe
  else
    let (r1,r2,exs) =
      expand_required
        lc
        (SymmetricQueueElement.get_r1 qe)
        (SymmetricQueueElement.get_r2 qe)
    in
    if (exs <> 0) then
      [
        SymmetricQueueElement.make
          ~r1:r1
          ~r2:r2
          ~expansion_choices:(1::(SymmetricQueueElement.get_expansions_choices qe))
          ~expansions_performed:((SymmetricQueueElement.get_expansions_performed qe) + exs)
          ~expansions_inferred:((SymmetricQueueElement.get_expansions_inferred qe) + exs)
          ~expansions_forced:((SymmetricQueueElement.get_expansions_forced qe) + exs)
          ()
      ]
    else if !use_only_forced_expansions then
      expand_once
        qe
    else
      fix_problem_elts
        lc
        qe
