open Stdlib

module LabelledPlusTimesStarTreeOf
    (BD : Data)
    (PD : Data)
    (TD : Data)
    (SD : Data)
    (L  : Data) =
struct
  type nonempty_t =
    | Base of BD.t
    | Plus of PD.t * labelled_t list
    | Times of TD.t * labelled_t list
    | Star of SD.t * labelled_t

  and  labelled_t = nonempty_t * L.t
  [@@deriving ord, show, hash]

  type t =
    | Empty
    | Nonempty of nonempty_t
  [@@deriving ord, show, hash]

  let fold_downward_upward
      (type a)
      (type b)
      (type c)
      ~init:(init:b)
      ~upward_empty:(upward_empty:c)
      ~upward_nonempty:(upward_nonempty:a -> c)
      ~upward_base:(upward_base:b -> BD.t -> a)
      ~upward_plus:(upward_plus:b -> PD.t -> (L.t * a) list -> a)
      ~upward_times:(upward_times:b -> TD.t -> (L.t * a) list -> a)
      ~upward_star:(upward_star:b -> SD.t -> L.t -> a -> a)
      ?downward_plus:(downward_plus:b -> PD.t -> L.t -> b = curry3 fst_trip)
      ?downward_times:(downward_times:b -> TD.t -> L.t -> b = curry3 fst_trip)
      ?downward_star:(downward_star:b -> SD.t -> L.t -> b = curry3 fst_trip)
      (ptst:t)
    : c =
    let rec fold_downward_upward_nonempty_internal
        (downward_acc:b)
        (nptst:nonempty_t)
      : a =
      begin match nptst with
        | Base bd ->
          upward_base downward_acc bd
        | Plus (pd,ts) ->
          upward_plus
            downward_acc
            pd
            (List.map
               ~f:(fun (t,l) ->
                   let downward_acc' = downward_plus downward_acc pd l in
                   (l
                   ,fold_downward_upward_nonempty_internal downward_acc' t))
               ts)
        | Times (td,ts) ->
          upward_times
            downward_acc
            td
            (List.map
               ~f:(fun (t,l) ->
                   let downward_acc' = downward_times downward_acc td l in
                   (l
                   ,fold_downward_upward_nonempty_internal downward_acc' t))
               ts)
        | Star (sd,(t,l)) ->
          let downward_acc' = downward_star downward_acc sd l in
          upward_star
            downward_acc
            sd
            l
            (fold_downward_upward_nonempty_internal downward_acc' t)
      end

    in
    begin match ptst with
      | Empty -> upward_empty
      | Nonempty nptst ->
        upward_nonempty
          (fold_downward_upward_nonempty_internal init nptst)
    end


  let fold
      (type a)
      (type c)
      ~empty_f:(empty_f:c)
      ~nonempty_f:(nonempty_f:a -> c)
      ~base_f:(base_f:BD.t -> a)
      ~plus_f:(plus_f:PD.t -> (L.t * a) list -> a)
      ~times_f:(times_f:TD.t -> (L.t * a) list -> a)
      ~star_f:(star_f:SD.t -> L.t -> a -> a)
      v
    : c =
    fold_downward_upward
      ~init:()
      ~upward_empty:(empty_f)
      ~upward_nonempty:(nonempty_f)
      ~upward_base:(thunk_of base_f)
      ~upward_plus:(thunk_of plus_f)
      ~upward_times:(thunk_of times_f)
      ~upward_star:(thunk_of star_f)
      v
end

module PlusTimesStarTreeOf
    (BD : Data)
    (PD : Data)
    (TD : Data)
    (SD : Data) =
struct
  type nonempty_t =
    | Base of BD.t
    | Plus of PD.t * nonempty_t list
    | Times of TD.t * nonempty_t list
    | Star of SD.t * nonempty_t
  [@@deriving ord, show, hash]

  type t =
    | Empty
    | Nonempty of nonempty_t
  [@@deriving ord, show, hash]

  let empty : t = Empty
  let nonempty (ne:nonempty_t) : t = Nonempty ne

  let fold_downward_upward
      ~init:(init:'b)
      ~upward_empty:(upward_empty:'c)
      ~upward_nonempty:(upward_nonempty:'a -> 'c)
      ~upward_base:(upward_base:'b -> BD.t -> 'a)
      ~upward_plus:(upward_plus:'b -> PD.t -> 'a list -> 'a)
      ~upward_times:(upward_times:'b -> TD.t -> 'a list -> 'a)
      ~upward_star:(upward_star:'b -> SD.t -> 'a -> 'a)
      ?downward_plus:(downward_plus:'b -> PD.t -> 'b = curry fst)
      ?downward_times:(downward_times:'b -> TD.t -> 'b = curry fst)
      ?downward_star:(downward_star:'b -> SD.t -> 'b = curry fst)
      (ptst:t)
    : 'c =
    let rec fold_downward_upward_nonempty_internal
        (downward_acc:'b)
        (nptst:nonempty_t)
      : 'a =
      begin match nptst with
        | Base bd ->
          upward_base downward_acc bd
        | Plus (pd,ts) ->
          let downward_acc' = downward_plus downward_acc pd in
          upward_plus
            downward_acc
            pd
            (List.map
               ~f:(fold_downward_upward_nonempty_internal downward_acc')
               ts)
        | Times (td,ts) ->
          let downward_acc' = downward_times downward_acc td in
          upward_times
            downward_acc
            td
            (List.map
               ~f:(fold_downward_upward_nonempty_internal downward_acc')
               ts)
        | Star (sd,t) ->
          let downward_acc' = downward_star downward_acc sd in
          upward_star
            downward_acc
            sd
            (fold_downward_upward_nonempty_internal downward_acc' t)
      end

    in
    begin match ptst with
      | Empty -> upward_empty
      | Nonempty nptst ->
        upward_nonempty
          (fold_downward_upward_nonempty_internal init nptst)
    end


  let fold
      ~empty_f:(empty_f:'c)
      ~nonempty_f:(nonempty_f:'a -> 'c)
      ~base_f:(base_f:BD.t -> 'a)
      ~plus_f:(plus_f:PD.t -> 'a list -> 'a)
      ~times_f:(times_f:TD.t -> 'a list -> 'a)
      ~star_f:(star_f:SD.t -> 'a -> 'a)
      (v:t)
    : 'c =
    fold_downward_upward
      ~init:()
      ~upward_empty:(empty_f)
      ~upward_nonempty:(nonempty_f)
      ~upward_base:(thunk_of base_f)
      ~upward_plus:(thunk_of plus_f)
      ~upward_times:(thunk_of times_f)
      ~upward_star:(thunk_of star_f)
      v
end

module DNFPlusTimesStarTree
    (BD : Data)
    (PD : Data)
    (TD : Data)
    (SD : Data) =
struct
  type disjunction = PD.t * sequence list
  and sequence = TD.t * atom list
  and atom =
    | Star of SD.t * disjunction
    | Base of BD.t
  [@@deriving ord, show, hash]

  type t = disjunction
  [@@deriving ord, show, hash]

  module PTST = PlusTimesStarTreeOf(BD)(PD)(TD)(SD)

  let plus
      (pd:PD.t)
      (flatten_plus:PD.t list -> PD.t)
      (dnfs:t list)
    : t =
    let (pds,sss) = List.unzip dnfs in
    (flatten_plus pds, List.concat sss)

  let times
      (td:PD.t)
      (flatten_plus:PD.t list -> PD.t)
      (flatten_times:TD.t list -> TD.t)
      ((p1,ss1):t)
      ((p2,ss2):t)
    : t =
    let seq_times (t1,as1) (t2,as2) =
      (flatten_times [t1;t2], as1@as2)
    in
    (flatten_plus [p1;p2]
    ,cartesian_map
        ~f:seq_times
        ss1
        ss2)

  let atom_to_t
      (sd_extender:SD.t -> PD.t * TD.t)
      (bd_extender:BD.t -> PD.t * TD.t)
      (a:atom)
    : t =
    let (pd,td) =
      begin match a with
        | Star (sd,d) ->
          sd_extender sd
        | Base bd ->
          bd_extender bd
      end
    in
    let seq = (td,[a]) in
    (pd,[seq])

  let from_tree
      (sd_extender:SD.t -> PD.t * TD.t)
      (bd_extender:BD.t -> PD.t * TD.t)
      (empty:t)
      (v:PTST.t)
    : t =
    (*PTST.fold
      ~empty_f:empty
      ~nonempty_f:ident
      ~base_f:(fun bd -> atom_to_t sd_extender bd_extender (Base bd))
      ~plus_f:(fun pd dnfs -> plus pd dnf1 dnf2)*)
    failwith "TODO"
end

module NormalizedPlusTimesStarTreeOf
    (BD : Data)
    (PD : Data)
    (TD : Data)
    (SD : Data) =
struct
  module NormalizationScript =
  struct
    module PD_NormalizationLabel =
    struct
      type t =
        {
          label : PD.t                 ;
          perm  : CountedPermutation.t ;
        }
      [@@deriving ord, show, hash, make]
    end

    module TD_NormalizationLabel =
    struct
      type t =
        {
          label : TD.t                 ;
          perm  : CountedPermutation.t ;
        }
      [@@deriving ord, show, hash, make]
    end

    include PlusTimesStarTreeOf
        (BD)
        (PD_NormalizationLabel)
        (TD_NormalizationLabel)
        (SD)
  end

  module NonNormalizedTree = PlusTimesStarTreeOf(BD)(PD)(TD)(SD)

  include LabelledPlusTimesStarTreeOf
      (BD)
      (PD)
      (TD)
      (SD)
      (IntModule)

  let from_tree : NonNormalizedTree.t -> t * NormalizationScript.t =
    NonNormalizedTree.fold
      ~empty_f:(Empty,NormalizationScript.Empty)
      ~nonempty_f:(fun (nt,nns) ->
          (Nonempty nt,
           NormalizationScript.Nonempty nns))
      ~base_f:(fun bl ->
          (Base bl,
           NormalizationScript.Base bl))
      ~plus_f:(fun p nsnts ->
          let (nts,nss) = List.unzip nsnts in
          let (perm,sv) =
            CountedPermutation.sorting
              ~cmp:(compare_nonempty_t)
              nts
          in
          let nvs =
            List.map
              ~f:(fun xs ->
                  (List.hd_exn xs
                  ,List.length xs))
              sv
          in
          let norm_label =
            NormalizationScript.PD_NormalizationLabel.make
              ~label:p
              ~perm:perm
          in
          (Plus (p,nvs)
          ,NormalizationScript.Plus (norm_label,nss)))
      ~times_f:(fun t nsnts ->
          let (nts,nss) = List.unzip nsnts in
          let (perm,sv) =
            CountedPermutation.sorting
              ~cmp:(compare_nonempty_t)
              nts
          in
          let nvs =
            List.map
              ~f:(fun xs ->
                  (List.hd_exn xs
                  ,List.length xs))
              sv
          in
          let norm_label =
            NormalizationScript.TD_NormalizationLabel.make
              ~label:t
              ~perm:perm
          in
          (Times (t,nvs)
          ,NormalizationScript.Times (norm_label,nss)))
      ~star_f:(fun s (t,ns) ->
          (Star (s,(t,1))
          ,NormalizationScript.Star (s,ns)))
end

module StarSemiringTreeAlignmentOf
    (BD : Data)
    (PD : Data)
    (TD : Data)
    (SD : Data) =
  PlusTimesStarTreeOf
    (PairOf(BD)(BD))
    (PairOf(PD)(Permutation))
    (PairOf(TD)(Permutation))
    (SD)
