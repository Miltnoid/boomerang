open Stdlib
open Lang


(**** Exampled Regex {{{ *****)

type 'a example_data =
  {
    arg1_data : 'a ;
    arg2_data : 'a ;
    output_data : 'a ;
  }
[@@deriving ord, show, hash, make]

let map_example_data
    (f:'a -> 'b)
    (ed:'a example_data)
  : 'b example_data =
  make_example_data
    ~arg1_data:(f ed.arg1_data)
    ~arg2_data:(f ed.arg2_data)
    ~output_data:(f ed.output_data)

let unzip_example_data
    (ed:('a * 'b) example_data)
  : 'a example_data * 'b example_data =
  (map_example_data fst ed
  ,map_example_data snd ed)

let merge_example_data
    (f:'a -> 'b -> 'c)
    (ed1:'a example_data)
    (ed2:'b example_data)
  : 'c example_data =
  make_example_data
    ~arg1_data:(f ed1.arg1_data ed2.arg1_data)
    ~arg2_data:(f ed1.arg2_data ed2.arg2_data)
    ~output_data:(f ed1.output_data ed2.output_data)

type parsing_example_data = (int list list) example_data
[@@deriving ord, show, hash]

type example_string_data = (string list) example_data
[@@deriving ord, show, hash]

let empty_parsing_example_data =
  make_example_data
    ~arg1_data:[]
    ~arg2_data:[]
    ~output_data:[]

let empty_string_example_data =
  make_example_data
    ~arg1_data:[]
    ~arg2_data:[]
    ~output_data:[]

type exampled_regex =
  | ERegExEmpty
  | ERegExBase of string * (int list list) example_data
  | ERegExConcat of exampled_regex * exampled_regex * (int list list) example_data
  | ERegExOr of exampled_regex  * exampled_regex * (int list list) example_data
  | ERegExStar of exampled_regex * (int list list) example_data
  | ERegExClosed of Regex.t * example_string_data * (int list list) example_data

let extract_example_data (er:exampled_regex) : parsing_example_data =
  begin match er with
    | ERegExEmpty -> empty_parsing_example_data
    | ERegExBase (_,pd) -> pd
    | ERegExConcat (_,_,pd) -> pd
    | ERegExOr (_,_,pd) -> pd
    | ERegExStar (_,pd) -> pd
    | ERegExClosed (_,_,pd) -> pd
  end

type run_mode = Arg1 | Arg2 | Output

let extract_iterations_consumed
    (m:run_mode)
    (er:exampled_regex)
  : int list list =
  begin match m with
    | Arg1 -> (extract_example_data er).arg1_data
    | Arg2 -> (extract_example_data er).arg2_data
    | Output -> (extract_example_data er).output_data
  end

let took_regex
    (m:run_mode)
    (er:exampled_regex)
    (iteration:int list) : bool =
  let ill = extract_iterations_consumed m er in
  List.mem ~equal:(=) ill iteration

let extract_data
    (m:run_mode)
    (d:'a example_data)
  : 'a =
  begin match m with
    | Arg1 -> d.arg1_data
    | Arg2 -> d.arg2_data
    | Output -> d.output_data
  end

let rec extract_string
    (m:run_mode)
    (er:exampled_regex)
    (iteration:int list)
  : string =
  begin match er with
    | ERegExEmpty -> failwith "no string"
    | ERegExBase (s,_) -> s
    | ERegExConcat (er1,er2,_) ->
      (extract_string m er1 iteration) ^
      (extract_string m er2 iteration)
    | ERegExOr (er1,er2,_) ->
      if took_regex m er1 iteration then
        extract_string m er1 iteration
      else
        extract_string m er2 iteration
    | ERegExStar (er',_) ->
        let valid_iterations =
          List.rev
            (List.filter
              ~f:(fun it -> List.tl_exn it = iteration)
              (extract_iterations_consumed m er')) in
        String.concat
          (List.map
            ~f:(extract_string m er')
            valid_iterations)
    | ERegExClosed (_,sl,ill) ->
      let dat_opt = List.findi
          ~f:(fun _ il -> il = iteration)
          (extract_data m ill) in
      begin match dat_opt with
        | None -> failwith "im horrible"
        | Some (i,_) ->
            List.nth_exn (extract_data m sl) i
        end
  end

(*let rec exampled_regex_to_string (r:exampled_regex) : string =
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
  | ERegExClosed (s,ss,ill) -> paren ((Regex.show s) ^ (bracket (
      String.concat
        ~sep:";"
        ss) ^ string_of_int_list_list ill))
  | ERegExEmpty -> "{}"
  end*)


(***** }}} *****)


(**** Exampled DNF Regex {{{ *****)

type exampled_atom =
  | EAClosed of Regex.t *
                Regex.t *
                Lens.t *
                (string list) example_data *
                (int list list) example_data *
                (string list) example_data
  | EAStar of exampled_dnf_regex * (int list list) example_data * Regex.t

and exampled_clause = (exampled_atom) list * string list * (int list list) example_data

and exampled_dnf_regex = exampled_clause list * int list list example_data

let get_atom_regex (ea:exampled_atom) : Regex.t =
  begin match ea with
    | EAClosed (_,r,_,_,_,_) ->
      Regex.make_closed r
    | EAStar (_,_,r) -> r
  end

(*let rec exampled_dnf_regex_to_string ((r,ill):exampled_dnf_regex) : string =
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
  | EAClosed (s,_,_,sl,ill,_) -> paren (
      (Regex.show s) ^ "," ^
      bracket (
        String.concat
        ~sep:";"
        sl) ^ "," ^ string_of_int_list_list ill
      )
  | EAStar (r,ill,_) -> (paren ((exampled_dnf_regex_to_string r) ^ (string_of_int_list_list ill))) ^ "*"
  end*)

(***** }}} *****)

type ordered_exampled_atom =
  | OEAClosed of Regex.t * Regex.t * Lens.t * string list example_data
  | OEAStar of ordered_exampled_dnf_regex

and ordered_exampled_clause = ((ordered_exampled_atom * int) list) list * string
list * (int list list) example_data

and ordered_exampled_dnf_regex = (ordered_exampled_clause * int) list list

(*let rec compare_exampled_atoms (a1:exampled_atom) (a2:exampled_atom) :
  comparison =
    begin match (a1,a2) with
      | (EAClosed (s1,_,_,el1,_,_), EAClosed (s2,_,_,el2,_,_)) ->
        let cmp = Regex.compare s1 s2 in
        if (is_equal cmp) then
          ordered_partition_order
            String.compare
            el1
            el2
        else
          cmp
    | (EAStar (r1,_,_), EAStar (r2,_,_)) -> compare_exampled_dnf_regexs r1 r2
    | _ -> 0
    end 

and compare_exampled_clauses ((atoms1,_,ints1):exampled_clause)
                             ((atoms2,_,ints2):exampled_clause)
  : comparison =
  let cmp = ordered_partition_order compare_exampled_atoms atoms1 atoms2 in
  if (is_equal cmp) then
    ordered_partition_order
      (fun x y -> failwith "BREAK PLZ"(*(compare x y)*))
      ints1
      ints2
  else
    cmp

and compare_exampled_dnf_regexs ((r1,_):exampled_dnf_regex) ((r2,_):exampled_dnf_regex) : comparison =
  ordered_partition_order
    compare_exampled_clauses
      r1
      r2*)

let rec compare_ordered_exampled_atoms (a1:ordered_exampled_atom)
                                       (a2:ordered_exampled_atom)
                                     : comparison =
    begin match (a1,a2) with
      | (OEAClosed (s1,_,_,el1), OEAClosed (s2,_,_,el2)) ->
        let cmp = Regex.compare s1 s2 in
        if is_equal cmp then
          compare_example_string_data
            el1
            el2
        else
          cmp
    | (OEAStar r1, OEAStar r2) -> compare_ordered_exampled_dnf_regexs r1 r2
    | (OEAStar _, OEAClosed _) -> 1
    | (OEAClosed _, OEAStar _) -> -1
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
    compare_parsing_example_data
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
  | EAClosed (s,sorig,lmap,el,_,_) -> OEAClosed (s,sorig,lmap,el)
  | EAStar (r,_,_) -> OEAStar (to_ordered_exampled_dnf_regex r)
  end

and to_ordered_exampled_clause ((atoms,strings,exnums):exampled_clause) : ordered_exampled_clause =
  let ordered_atoms = List.map ~f:to_ordered_exampled_atom atoms in
  let ordered_ordered_atoms =
    sort_and_partition_with_indices
      compare_ordered_exampled_atoms
      ordered_atoms in
  (ordered_ordered_atoms
  ,strings
  ,make_example_data
      ~arg1_data:(List.sort ~cmp:(compare_list ~cmp:Int.compare) exnums.arg1_data)
      ~arg2_data:(List.sort ~cmp:(compare_list ~cmp:Int.compare) exnums.arg2_data)
      ~output_data:(List.sort ~cmp:(compare_list ~cmp:Int.compare) exnums.output_data))

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
  | AClosed of Regex.t
  | AStar of dnf_regex

and clause = atom list * string list

and dnf_regex = clause list
[@@deriving ord, show, hash]

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
  | (AClosed s1, AClosed s2) -> Regex.compare s1 s2
  | (AClosed  _, AStar         _) -> -1
  | (AStar         _, AClosed  _) -> 1
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
  | AClosed s -> Regex.show s
  end

(***** }}} *****)




