open Stdlib
open Lang

(***** The main LensContext module {{{ *****)
module LensContext = struct
  module OutgoingD = DictOf(Regex)(ListOf(PairOf(Lens)(Regex)))

  module DS = DisjointSetOf(Regex)

  type t = { outgoing : OutgoingD.t ;
             equivs   : DS.t        ; }
  [@@deriving ord, show, hash]

  let empty = { outgoing = OutgoingD.empty ;
                equivs   = DS.empty        ; }

  let update_outgoing (outgoing:OutgoingD.t)
      (rx1:Regex.t) (rx2:Regex.t) (l:Lens.t)
    : OutgoingD.t =
    let outgoing = begin match OutgoingD.lookup outgoing rx1 with
      | None -> OutgoingD.insert outgoing rx1 [(l,rx2)]
      | Some ol -> OutgoingD.insert outgoing rx1 ((l,rx2)::ol)
    end in
    let outgoing = begin match OutgoingD.lookup outgoing rx2 with
      | None -> OutgoingD.insert outgoing rx2 [(Lens.LensInverse l,rx1)]
      | Some ol -> OutgoingD.insert outgoing rx2 ((Lens.LensInverse l,rx1)::ol)
    end in
    outgoing

  let update_equivs (equivs:DS.t) (r1:Regex.t) (r2:Regex.t)
    : DS.t =
    DS.union_elements
      equivs
      r1
      r2

  (* TODO: is this the right thing, simpler if just between vars ? *)
  let insert_exn (lc:t) (l:Lens.t) (r1:Regex.t) (r2:Regex.t) : t =
        { outgoing = update_outgoing lc.outgoing r1 r2 l;
          equivs   = update_equivs lc.equivs r1 r2       ; }

  let insert_list_exn (lc:t) (nirsl:(Lens.t * Regex.t * Regex.t) list) : t =
    List.fold_left
      ~f:(fun acc (l,r1,r2) -> insert_exn acc l r1 r2)
      ~init:lc
      nirsl

  let get_outgoing_edges (outgoing:OutgoingD.t) (source:Regex.t)
    : (Lens.t * Regex.t) list =
    begin match OutgoingD.lookup outgoing source with
      | None -> []
      | Some connections -> connections
    end

  let create_from_list_exn (nirsl:(Lens.t * Regex.t * Regex.t) list) : t =
    insert_list_exn empty nirsl

  module M = ListOf(PairOf(Lens)(Regex))

  let shortest_path
      (lc:t)
      (regex1:Regex.t)
      (regex2:Regex.t)
    : Lens.t option =
    let outgoing = lc.outgoing in
    let rec shortest_path_internal
        (accums:(Lens.t * Regex.t) list) : Lens.t =
      let satisfying_path_option =
        List.find
          ~f:(fun (_,n) -> is_equal (Regex.compare n regex2))
          accums
      in
      begin match satisfying_path_option with
        | None ->
          let accums =
            List.concat_map
              ~f:(fun (l,n) ->
                  let valid_outgoing_edges =
                    List.filter
                      ~f:(fun (l',_) -> not (Lens.has_common_sublens l' l))
                      (get_outgoing_edges outgoing n)
                  in
                  List.map
                    ~f:(fun (l',n') -> (Lens.LensCompose (l',l),n'))
                    valid_outgoing_edges)
              accums
          in
          shortest_path_internal accums
        | Some (l,_) -> l
      end
    in
    let regex1_rep = DS.find_representative lc.equivs regex1 in
    let regex2_rep = DS.find_representative lc.equivs regex2 in
    if regex1_rep <> regex2_rep then
      None
    else if is_equal (Regex.compare regex1 regex2) then
      Some (Lens.LensIdentity (regex1))
    else
      Some (shortest_path_internal (get_outgoing_edges outgoing regex1))

  let shortest_path_exn (lc:t) (regex1:Regex.t) (regex2:Regex.t)
    : Lens.t =
    begin match shortest_path lc regex1 regex2 with
      | None -> 
        failwith ("regexes not in same equivalence class: r1"
                  ^ (Regex.show regex1)
                  ^ "r2:"
                  ^ (Regex.show regex2))
      | Some l -> l
    end

  let shortest_path_to_rep_elt (lc:t) (regex:Regex.t) : Regex.t * Lens.t =
    let rep_element = DS.find_representative lc.equivs regex in
    let shortest_path = shortest_path_exn lc regex rep_element in
    (rep_element,shortest_path)

  let autogen_id_from_base (lc:t) (base:string) : Id.t =
    let rec fresh nopt =
      let (x,next) =
        begin match nopt with
          | None -> (base,Some 1)
          | Some n -> (Printf.sprintf "%s%d" base n, Some (n+1))
        end
      in
      x
    in
    Id.Id (fresh None)

  let autogen_id (lc:t) (l:Lens.t) : Id.t =
    let base = Lens.show l in
    let rec fresh nopt =
      let (x,next) =
        begin match nopt with
          | None -> (base,Some 1)
          | Some n -> (Printf.sprintf "%s%d" base n, Some (n+1))
        end
      in
      fresh next
    in
    Id.Id (fresh None)
      
  let autogen_fresh_id (lc:t) : Id.t =
    autogen_id_from_base lc "l"
end

(***** }}} *****)
