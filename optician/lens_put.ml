open Stdlib
open Regexcontext
open Lenscontext
open Lang
open Eval
open Normalized_lang
open Typing

let rec lens_putl_internal
    (lc:LensContext.t)
    (l:Lens.t)
    (er:exampled_regex)
    (iteration:int list)
  : string =
  begin match (l,er) with
    | (Lens.LensConst (s1,s2), ERegExBase (s2',_)) ->
        if s2 = s2' then
          s1
        else
          failwith "bad typecheck const"
    | (Lens.LensConcat (l1,l2), ERegExConcat (er1,er2,_)) ->
        (lens_putl_internal lc l1 er1 iteration) ^
        (lens_putl_internal lc l2 er2 iteration)
    | (Lens.LensSwap (l1,l2), ERegExConcat (er1,er2,_)) ->
        (lens_putl_internal lc l1 er2 iteration) ^
        (lens_putl_internal lc l2 er1 iteration)
    | (Lens.LensUnion (l1,l2), ERegExOr (er1,er2,_)) ->
        if took_regex er1 iteration then
          lens_putl_internal lc l1 er1 iteration
        else
          lens_putl_internal lc l2 er2 iteration
    | (Lens.LensCompose (l1,l2),_) ->
      let intermediary_string = lens_putl_internal lc l1 er iteration in
      let (_,intermediary_regex) = type_lens l2 in
      let intermediary_er_o = regex_to_exampled_regex
          intermediary_regex
          [intermediary_string]
      in
      begin match intermediary_er_o with
        | None -> failwith "bad input to lens"
        | Some intermediary_er -> lens_putl_internal lc l2 intermediary_er [0]
      end
    | (Lens.LensIterate l', ERegExStar (er',_)) ->
        let valid_iterations =
          List.rev
            (List.filter
              ~f:(fun it -> List.tl_exn it = iteration)
              (extract_iterations_consumed er')) in
        String.concat
          (List.map
            ~f:(lens_putl_internal lc l' er')
            valid_iterations)
    | (Lens.LensIdentity _, _) ->
      extract_string er iteration
    | (Lens.LensInverse l', _) ->
      lens_putr_internal lc l' er iteration
    | (Lens.LensPermute (p,ls), _) ->
      let rec extract_reversed_concat_list
          (er:exampled_regex)
          (n:int)
        : exampled_regex list =
        if n = 0 then
          []
        else if n = 1 then
          [er]
        else
          begin match er with
            | ERegExConcat(er1,er2,_) ->
              er2::(extract_reversed_concat_list er1 (n-1))
            | _ -> failwith "bad typecheck disagreeing types"
          end
      in
      let concat_list =
        List.rev
          (extract_reversed_concat_list er (List.length ls))
      in
      let permed_concat_list =
        Permutation.apply_inverse_to_list_exn
          p
          concat_list
      in
      let er_l_list = List.zip_exn permed_concat_list ls in
      List.fold
        ~f:(fun s (er,l) ->
            s ^ (lens_putl_internal lc l er iteration))
        ~init:""
        er_l_list
    | _ -> failwith "bad typecheck disagreeing types"
  end

and lens_putr_internal
    (lc:LensContext.t)
    (l:Lens.t)
    (er:exampled_regex)
    (iteration:int list)
  : string =
  begin match (l,er) with
    | (Lens.LensConst (s1,s2), ERegExBase (s1',_)) ->
        if s1 = s1' then
          s2
        else
          failwith "bad typecheck const"
    | (Lens.LensConcat (l1,l2), ERegExConcat (er1,er2,_)) ->
        (lens_putr_internal lc l1 er1 iteration) ^
        (lens_putr_internal lc l2 er2 iteration)
    | (Lens.LensSwap (l1,l2), ERegExConcat (er1,er2,_)) ->
        (lens_putr_internal lc l2 er2 iteration) ^
        (lens_putr_internal lc l1 er1 iteration)
    | (Lens.LensUnion (l1,l2), ERegExOr (er1,er2,_)) ->
        if took_regex er1 iteration then
          lens_putr_internal lc l1 er1 iteration
        else
          lens_putr_internal lc l2 er2 iteration
    | (Lens.LensCompose (l1,l2),_) ->
      let intermediary_string = lens_putr_internal lc l2 er iteration in
      let (intermediary_regex,_) = type_lens l1 in
      let intermediary_er_o = regex_to_exampled_regex
          intermediary_regex
          [intermediary_string]
      in
      begin match intermediary_er_o with
        | None -> failwith "bad input to lens"
        | Some intermediary_er -> lens_putr_internal lc l1 intermediary_er [0]
      end
    | (Lens.LensIterate l', ERegExStar (er',_)) ->
        let valid_iterations =
          List.rev
            (List.filter
              ~f:(fun it -> List.tl_exn it = iteration)
              (extract_iterations_consumed er')) in
        String.concat
          (List.map
            ~f:(lens_putr_internal lc l' er')
            valid_iterations)
    | (Lens.LensIdentity _, _) ->
      extract_string er iteration
    | (Lens.LensInverse l', _) ->
      lens_putl_internal lc l' er iteration
    | (Lens.LensPermute (p,ls), _) ->
      let rec extract_reversed_concat_list
          (er:exampled_regex)
          (n:int)
        : exampled_regex list =
        if n = 0 then
          []
        else if n = 1 then
          [er]
        else
          begin match er with
            | ERegExConcat(er1,er2,_) ->
              er2::(extract_reversed_concat_list er1 (n-1))
            | _ -> failwith "bad typecheck disagreeing types"
          end
      in
      let concat_list =
        List.rev
          (extract_reversed_concat_list er (List.length ls))
      in
      let er_l_list = List.zip_exn concat_list ls in
      let permed_er_l_list =
        Permutation.apply_to_list_exn
          p
          er_l_list
      in
      List.fold
        ~f:(fun s (er,l) ->
            s ^ (lens_putl_internal lc l er iteration))
        ~init:""
        permed_er_l_list
    | _ -> failwith "bad typecheck disagreeing types"
  end

let lens_putr
    (lc:LensContext.t)
    (l:Lens.t)
    (s:string)
  : string =
  let (sr,_) = type_lens l in
  let exampled_sr_o = regex_to_exampled_regex sr [s] in
  begin match exampled_sr_o with
    | None -> failwith ("bad input to lens" ^ s)
    | Some exampled_sr -> lens_putr_internal lc l exampled_sr [0]
  end

let lens_putl
    (lc:LensContext.t)
    (l:Lens.t)
    (s:string)
  : string =
  let (_,tr) = type_lens l in
  let exampled_sr_o = regex_to_exampled_regex tr [s] in
  begin match exampled_sr_o with
    | None -> failwith ("bad input to lens: " ^ s)
    | Some exampled_sr -> lens_putl_internal lc l exampled_sr [0]
  end
