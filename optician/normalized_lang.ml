open Stdlib
open Lang


(**** Exampled Regex {{{ *****)

module OpenableData =
struct
  type t = 
    | False of string list
    | True
  [@@deriving ord, show, hash]

  let mk_true : t = True

  let mk_false
      (ss:string list)
    : t =
    False ss

  let strings_exn
    (t:t)
    : string list =
    begin match t with
      | False ss -> ss
      | True -> failwith "expected false openable"
    end

  let is_true
      (t:t)
    : bool =
    begin match t with
      | True -> true
      | _ -> false
    end

  let is_false
      (t:t)
    : bool =
    not (is_true t)
end

module ExampledRegex =
struct
  type ill = int list list
  [@@deriving ord, show, hash]

  type d = 
    | ERegExBase   of string
    | ERegExConcat of t * t
    | ERegExUnion  of t list
    | ERegExStar   of t
    | ERegExInter  of t list
    | ERegExDiff   of t * t

  and t =
    {
      desc     : d              ;
      ill      : ill            ;
      opened   : bool           ;
      openable : OpenableData.t ;
    }
  [@@deriving ord, show, hash]

  let mk_t
      ~desc:(desc:d)
      ~ill:(ill:ill)
      ~opened:(opened:bool)
      ~openable:(openable:OpenableData.t)
    : t =
    {
      desc     = desc     ;
      ill      = ill      ;
      opened   = false    ;
      openable = openable ;
    }

  let mk_empty : t =
    let d = ERegExUnion [] in
    mk_t
      ~desc:d
      ~ill:[]
      ~opened:true
      ~openable:OpenableData.mk_true

  let mk_base
      ~ill:ill
      (s:string)
    : t =
    let d = ERegExBase s in
    mk_t
      ~desc:d
      ~ill:ill
      ~opened:true
      ~openable:OpenableData.mk_true

  let mk_concat
      ~ill:(ill:ill)
      ?opened:(opened:bool = false)
      ~openable:(openable:OpenableData.t)
      (r1:t)
      (r2:t)
    : t =
    begin match (r1.desc,r2.desc) with
      | (ERegExBase "", _) ->
        assert (r1.ill = ill);
        r2
      | (_, ERegExBase "") ->
        assert (r2.ill = ill);
        r1
      | (ERegExBase s1, ERegExBase s2) ->
        assert (r1.ill = r2.ill && ill = r1.ill);
        mk_base ~ill:ill (s1^s2)
      | _ ->
        let d = ERegExConcat (r1,r2) in
        mk_t
          ~ill:ill
          ~desc:d
          ~opened:false
          ~openable:openable
    end

  let mk_union
      ~ill:(ill:ill)
      ?opened:(opened:bool = false)
      ~openable:(openable:OpenableData.t)
      (rs:t list)
    : t =
    begin match rs with
      | [] ->
        mk_empty
      | [r] -> r
      | _ ->
        let d = ERegExUnion rs in
        mk_t
          ~ill:ill
          ~desc:d
          ~opened:opened
          ~openable:openable
    end

  let mk_star
      ~ill:(ill:ill)
      ?opened:(opened:bool = false)
      ~openable:(openable:OpenableData.t)
      (r:t)
    : t =
    begin match r.desc with
      | ERegExUnion [] ->
        mk_base ~ill:ill ""
      | _ ->
        let d = ERegExStar r in
        mk_t
          ~ill:ill
          ~desc:d
          ~opened:opened
          ~openable:openable
    end

  let mk_diff
      ~ill:(ill:ill)
      (r1:t)
      (r2:t)
      (ss:string list)
    : t =
    let d = ERegExDiff (r1,r2) in
    mk_t
      ~ill:ill
      ~desc:d
      ~opened:false
      ~openable:(OpenableData.mk_false ss)

  let mk_inter
      ~ill:(ill:ill)
      (rs:t list)
      (ss:string list)
    : t =
    let d = ERegExInter rs in
    mk_t
      ~ill:ill
      ~desc:d
      ~opened:false
      ~openable:(OpenableData.mk_false ss)

  type 'a datad = ill:ill -> opened:bool -> openable:OpenableData.t -> 'a

  let ignore_data
      (x:'a)
    : 'a datad =
    fun ~ill:_ ~opened:_ ~openable:_ -> x

  let fold_downward_upward
      (type a)
      (type b)
      ~init:(init:b)
      ~upward_base:(upward_base:(b -> string -> a) datad)
      ~upward_concat:(upward_concat:(b -> a -> a -> a) datad)
      ~upward_union:(upward_union:(b -> a list -> a) datad)
      ~upward_star:(upward_star:(b -> a -> a) datad)
      ~upward_diff:(upward_diff:(b -> a -> a -> a) datad)
      ~upward_inter:(upward_inter:(b -> a list -> a) datad)
      ?downward_concat:(downward_concat:(b -> b) datad = ignore_data ident)
      ?downward_union:(downward_union:(b -> b) datad = ignore_data ident)
      ?downward_star:(downward_star:(b -> b) datad = ignore_data ident)
      ?downward_diff:(downward_diff:(b -> b) datad = ignore_data ident)
      ?downward_inter:(downward_inter:(b -> b) datad = ignore_data ident)
    : t -> a =
    let rec fold_downward_upward_internal
        (downward_acc:b)
        (r:t)
      : a =
      let openable = r.openable in
      let opened = r.opened in
      let ill = r.ill in
      let apply_openness x = x ~ill:ill ~opened:opened ~openable:openable in
      begin match r.desc with
        | ERegExBase s ->
          apply_openness upward_base downward_acc s
        | ERegExConcat (r1,r2) ->
          let downward_acc' = apply_openness downward_concat downward_acc in
          (apply_openness upward_concat)
            downward_acc
            (fold_downward_upward_internal downward_acc' r1)
            (fold_downward_upward_internal downward_acc' r2)
        | ERegExUnion rs ->
          let downward_acc' = apply_openness downward_union downward_acc in
          (apply_openness upward_union)
            downward_acc
            (List.map ~f:(fold_downward_upward_internal downward_acc') rs)
        | ERegExStar r' ->
          let downward_acc' = apply_openness downward_star downward_acc in
          (apply_openness upward_star)
            downward_acc
            (fold_downward_upward_internal downward_acc' r')
        | ERegExDiff (r1,r2) ->
          let downward_acc' = apply_openness downward_diff downward_acc in
          (apply_openness upward_diff)
            downward_acc
            (fold_downward_upward_internal downward_acc' r1)
            (fold_downward_upward_internal downward_acc' r2)
        | ERegExInter (rs) ->
          let downward_acc' = apply_openness downward_inter downward_acc in
          (apply_openness upward_inter)
            downward_acc
            (List.map ~f:(fold_downward_upward_internal downward_acc') rs)
      end
    in
    fold_downward_upward_internal init

  let fold
      (type a)
      ~base_f:(base_f:(string -> a) datad)
      ~concat_f:(concat_f:(a -> a -> a) datad)
      ~union_f:(union_f:(a list -> a) datad)
      ~star_f:(star_f:(a -> a) datad)
      ~diff_f:(diff_f:(a -> a -> a) datad)
      ~inter_f:(inter_f:(a list -> a) datad)
      (r:t)
    : a =
    let thunk_inside
        (type a)
        (f:a datad)
      : (unit -> a) datad =
      let tf
          ~ill:ill
          ~opened:opened
          ~openable:openable
          () =
        f ~ill:ill ~opened:opened ~openable:openable
      in
      tf
    in

    fold_downward_upward
      ~init:()
      ~upward_base:(thunk_inside base_f)
      ~upward_concat:(thunk_inside concat_f)
      ~upward_union:(thunk_inside union_f)
      ~upward_star:(thunk_inside star_f)
      ~upward_diff:(thunk_inside diff_f)
      ~upward_inter:(thunk_inside inter_f)
      r
end 

type exampled_regex =
  | ERegExEmpty
  | ERegExBase of string * (int list list)
  | ERegExConcat of exampled_regex * exampled_regex * (int list list)
  | ERegExOr of exampled_regex  * exampled_regex * (int list list)
  | ERegExStar of exampled_regex * (int list list)
  | ERegExVariable of Id.t * string list * (int list list)

let extract_iterations_consumed (er:exampled_regex) : int list list =
  begin match er with
    | ERegExEmpty -> []
    | ERegExBase (_,ill) -> ill
    | ERegExConcat (_,_,ill) -> ill
    | ERegExOr (_,_,ill) -> ill
    | ERegExStar (_,ill) -> ill
    | ERegExVariable (_,_,ill) -> ill
  end

let took_regex (er:exampled_regex)
    (iteration:int list) : bool =
  let ill = extract_iterations_consumed er in
  List.mem ~equal:(=) ill iteration

let rec extract_string (er:exampled_regex) (iteration:int list)
  : string =
  begin match er with
    | ERegExEmpty -> failwith "no string"
    | ERegExBase (s,_) -> s
    | ERegExConcat (er1,er2,_) ->
      (extract_string er1 iteration) ^
      (extract_string er2 iteration)
    | ERegExOr (er1,er2,_) ->
      if took_regex er1 iteration then
        extract_string er1 iteration
      else
        extract_string er2 iteration
    | ERegExStar (er',_) ->
        let valid_iterations =
          List.rev
            (List.filter
              ~f:(fun it -> List.tl_exn it = iteration)
              (extract_iterations_consumed er')) in
        String.concat
          (List.map
            ~f:(extract_string er')
            valid_iterations)
    | ERegExVariable (_,sl,ill) ->
        let dat_opt = List.findi
          ~f:(fun _ il -> il = iteration)
          ill in
        begin match dat_opt with
        | None -> failwith "im horrible"
        | Some (i,_) ->
            List.nth_exn sl i
        end
  end

let extract_example_list (er:exampled_regex) : int list list =
  begin match er with
  | ERegExEmpty -> []
  | ERegExBase (_,ill) -> ill
  | ERegExConcat (_,_,ill) -> ill
  | ERegExOr (_,_,ill) -> ill
  | ERegExStar (_,ill) -> ill
  | ERegExVariable (_,_,ill) -> ill
  end

let rec exampled_regex_to_string (r:exampled_regex) : string =
  begin match r with
  | ERegExBase (s,ill) -> paren (s ^ string_of_int_list_list ill)
  | ERegExConcat (r1,r2,ill) ->
    paren
      ((exampled_regex_to_string r1)
       ^ (exampled_regex_to_string r2)
       ^ string_of_int_list_list ill)
  | ERegExOr (r1,r2,ill) ->
    paren(
        paren (exampled_regex_to_string r1)
      ^ "+"
      ^ paren (exampled_regex_to_string r2)
      ^ string_of_int_list_list ill)
  | ERegExStar (r',ill) ->
    paren (paren (exampled_regex_to_string r') ^ "*" ^ string_of_int_list_list ill)
  | ERegExVariable (s,ss,ill) -> paren ((Id.show s) ^ (bracket (
      String.concat
        ~sep:";"
        ss) ^ string_of_int_list_list ill))
  | ERegExEmpty -> "{}"
  end


(***** }}} *****)


(**** Exampled DNF Regex {{{ *****)

type exampled_atom =
  | EAVariable of Id.t * Id.t * Lens.t * string list * int list list
  | EAStar of exampled_dnf_regex * int list list

and exampled_clause = (exampled_atom) list * string list * (int list list)

and exampled_dnf_regex = exampled_clause list * int list list

let rec exampled_dnf_regex_to_string ((r,ill):exampled_dnf_regex) : string =
  paren ((String.concat
  ~sep:" + "
  (List.map ~f:exampled_clause_to_string r)) ^ "," ^ (string_of_int_list_list ill))

and exampled_clause_to_string ((atoms,strings,examples):exampled_clause) : string =
  paren (bracket (
    String.concat
    ~sep:";"
    (List.map ~f:exampled_atom_to_string atoms)))
  ^ "," ^
  (bracket (
    String.concat
    ~sep:";"
    strings))
  ^ "," ^
  (bracket (
    String.concat
    ~sep:";"

    (List.map ~f:
          (fun il -> bracket (String.concat ~sep:";"
          (List.map ~f:string_of_int il)))
          examples)))

and exampled_atom_to_string (a:exampled_atom) : string =
  begin match a with
  | EAVariable (s,_,_,sl,ill) -> paren (
      (Id.show s) ^ "," ^
      bracket (
        String.concat
        ~sep:";"
        sl) ^ "," ^ string_of_int_list_list ill
      )
  | EAStar (r,ill) -> (paren ((exampled_dnf_regex_to_string r) ^ (string_of_int_list_list ill))) ^ "*"
  end

(***** }}} *****)

type ordered_exampled_atom =
  | OEAVar of Id.t * Id.t * Lens.t * string list
  | OEAStar of ordered_exampled_dnf_regex

and ordered_exampled_clause = ((ordered_exampled_atom * int) list) list * string
list * (int list list)

and ordered_exampled_dnf_regex = (ordered_exampled_clause * int) list list

let rec compare_exampled_atoms (a1:exampled_atom) (a2:exampled_atom) :
  comparison =
    begin match (a1,a2) with
      | (EAVariable (s1,_,_,el1,_), EAVariable (s2,_,_,el2,_)) ->
        let cmp = Id.compare s1 s2 in
        if (is_equal cmp) then
          ordered_partition_order
            compare
            el1
            el2
        else
          cmp
    | (EAStar (r1,_), EAStar (r2,_)) -> compare_exampled_dnf_regexs r1 r2
    | _ -> 0
    end 

and compare_exampled_clauses ((atoms1,_,ints1):exampled_clause)
                             ((atoms2,_,ints2):exampled_clause)
  : comparison =
  let cmp = ordered_partition_order compare_exampled_atoms atoms1 atoms2 in
  if (is_equal cmp) then
    ordered_partition_order
      (fun x y -> (compare x y))
      ints1
      ints2
  else
    cmp

and compare_exampled_dnf_regexs ((r1,_):exampled_dnf_regex) ((r2,_):exampled_dnf_regex) : comparison =
  ordered_partition_order
    compare_exampled_clauses
      r1
      r2

let rec compare_ordered_exampled_atoms (a1:ordered_exampled_atom)
                                       (a2:ordered_exampled_atom)
                                     : comparison =
    begin match (a1,a2) with
      | (OEAVar (s1,_,_,el1), OEAVar (s2,_,_,el2)) ->
        let cmp = compare s1 s2 in
        if is_equal cmp then
          compare_list
            ~cmp:compare
            el1
            el2
        else
          cmp
    | (OEAStar r1, OEAStar r2) -> compare_ordered_exampled_dnf_regexs r1 r2
    | (OEAStar _, OEAVar _) -> 1
    | (OEAVar _, OEAStar _) -> -1
    end 

and compare_ordered_exampled_clauses
        ((atoms_partitions1,_,ints1):ordered_exampled_clause)
        ((atoms_partitions2,_,ints2):ordered_exampled_clause)
  : comparison =
  let cmp =
    ordered_partition_dictionary_order
      compare_ordered_exampled_atoms
      atoms_partitions1
      atoms_partitions2
  in
  if is_equal cmp then
    compare_list
      ~cmp:(compare)
      ints1
      ints2
  else
    cmp

and compare_ordered_exampled_dnf_regexs (r1:ordered_exampled_dnf_regex)
  (r2:ordered_exampled_dnf_regex) : comparison =
    ordered_partition_dictionary_order
      compare_ordered_exampled_clauses
        r1
        r2

let rec to_ordered_exampled_atom (a:exampled_atom) : ordered_exampled_atom =
  begin match a with
  | EAVariable (s,sorig,lmap,el,_) -> OEAVar (s,sorig,lmap,el)
  | EAStar (r,_) -> OEAStar (to_ordered_exampled_dnf_regex r)
  end

and to_ordered_exampled_clause ((atoms,strings,exnums):exampled_clause) : ordered_exampled_clause =
  let ordered_atoms = List.map ~f:to_ordered_exampled_atom atoms in
  let ordered_ordered_atoms =
    sort_and_partition_with_indices
      compare_ordered_exampled_atoms
      ordered_atoms in
  (ordered_ordered_atoms,strings,(List.sort ~cmp:compare exnums))

and to_ordered_exampled_dnf_regex ((r,_):exampled_dnf_regex)
        : ordered_exampled_dnf_regex =
  let ordered_clauses = List.map ~f:to_ordered_exampled_clause r in
  sort_and_partition_with_indices
    compare_ordered_exampled_clauses
    ordered_clauses


(**** DNF Lens {{{ *****)

type atom_lens =
  | AtomLensIterate of dnf_lens
  | AtomLensVariable of Lens.t

and clause_lens = atom_lens list * Permutation.t * string list * string list

and dnf_lens = clause_lens list * Permutation.t

let rec dnf_lens_to_string ((clause_lenses, permutation):dnf_lens) : string =
  let atom_lens_to_string (a:atom_lens) : string =
    begin match a with
    | AtomLensIterate l -> "iterate" ^ (paren (dnf_lens_to_string l))
    | AtomLensVariable lc -> "librarycall(" ^ (Lens.show lc) ^ ")"
    end in
  let clause_lens_to_string ((atomls,permutation,strings1,strings2):clause_lens) : string =
    paren (
      paren (
        String.concat (List.map ~f:atom_lens_to_string atomls) ~sep:","
      )
      ^ " , " ^
      paren (
        Permutation.show permutation
      )
      ^ " , " ^
      paren (
        String.concat (List.map ~f:(fun x -> "'"^x^"'") strings1) ~sep:","

      )
      ^ " , " ^
      paren (
        String.concat (List.map ~f:(fun x -> "'"^x^"'") strings2) ~sep:","
      )
    ) in
  paren (
    String.concat (List.map ~f:clause_lens_to_string clause_lenses) ~sep:","
  )
  ^ " , " ^
  paren (
    Permutation.show permutation
  )

let rec compare_dnf_lens
    (dl1:dnf_lens)
    (dl2:dnf_lens)
  : comparison =
  pair_compare
    (compare_list ~cmp:compare_clause_lens)
    Permutation.compare
    dl1
    dl2

and compare_clause_lens
    (cl1:clause_lens)
    (cl2:clause_lens)
  : comparison =
  quad_compare
    (compare_list ~cmp:compare_atom_lens)
    Permutation.compare
    (compare_list ~cmp:compare_string)
    (compare_list ~cmp:compare_string)
    cl1
    cl2

and compare_atom_lens
    (al1:atom_lens)
    (al2:atom_lens)
  : comparison =
  begin match (al1,al2) with
    | (AtomLensIterate dl1, AtomLensIterate dl2) ->
      compare_dnf_lens dl1 dl2
    | (AtomLensIterate _, _) -> -1
    | (_, AtomLensIterate _) -> 1
    | (AtomLensVariable l1, AtomLensVariable l2) ->
      Lens.compare l1 l2
  end

(***** }}} *****)

(**** DNF Regex {{{ *****)

type atom =
  | AVar of Id.t
  | AStar of dnf_regex

and clause = atom list * string list

and dnf_regex = clause list

let empty_dnf_string : dnf_regex = [([],[""])]

let concat_dnf_regexs (r1:dnf_regex) (r2:dnf_regex) : dnf_regex =
  cartesian_map
    ~f:(fun (a1s,s1s) (a2s,s2s) -> (a1s@a2s,weld_lists (^) s1s s2s))
    r1
    r2

let or_dnf_regexs (r1:dnf_regex) (r2:dnf_regex) : dnf_regex =
  r1 @ r2

let concat_clause_dnf_rx (cl:clause) (r:dnf_regex) : dnf_regex =
  concat_dnf_regexs [cl] r

let concat_dnf_rx_clause (r:dnf_regex) (cl:clause) : dnf_regex =
  concat_dnf_regexs r [cl]

let rec exponentiate_dnf (r:dnf_regex) (n:int) : dnf_regex =
  if n < 0 then
    failwith "invalid exponential"
  else if n = 0 then
    empty_dnf_string
  else
    concat_dnf_regexs (exponentiate_dnf r (n-1)) r

let rec quotiented_star_dnf (r:dnf_regex) (n:int) : dnf_regex =
  if n < 1 then
    failwith "invalid modulation"
  else if n = 1 then
    empty_dnf_string
  else
    or_dnf_regexs (quotiented_star_dnf r (n-1)) (exponentiate_dnf r (n-1))

let singleton_atom (a:atom) : dnf_regex =
  [([a],["";""])]


let rec compare_atoms (a1:atom) (a2:atom) : comparison =
  begin match (a1,a2) with
  | (AVar s1, AVar s2) -> compare s1 s2
  | (AVar  _, AStar         _) -> -1
  | (AStar         _, AVar  _) -> 1
  | (AStar        r1, AStar        r2) -> compare_dnf_regexs r1 r2
  end

and compare_clauses ((atoms1,_):clause) ((atoms2,_):clause) : comparison =
  ordered_partition_order compare_atoms atoms1 atoms2

and compare_dnf_regexs (r1:dnf_regex) (r2:dnf_regex) : comparison =
  ordered_partition_order compare_clauses r1 r2



let rec dnf_regex_to_string (clauses:dnf_regex) : string =
  (String.concat (List.map ~f:(fun c -> paren (clause_to_string c)) clauses) ~sep:"+")

and clause_to_string ((atoms,strings):clause) : string =
  paren ((paren (String.concat (List.map ~f:atom_to_string atoms) ~sep:","))
    ^ ","
    ^ (paren (String.concat strings ~sep:",")))

and atom_to_string (a:atom) : string =
  begin match a with
  | AStar dnf_rx -> (paren (dnf_regex_to_string dnf_rx)) ^ "*"
  | AVar s -> Id.show s
  end

(***** }}} *****)




