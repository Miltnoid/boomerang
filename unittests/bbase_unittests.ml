open Stdlib
open OUnit2
open Ounit_extensions
open Optician.Normalized_lang
open Bbase

let test_to_exampled_regex_base _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_base "a" [[0]])
    (Brx.to_exampled_regex (Brx.mk_string "a") ["a"])

let test_to_exampled_regex_empty _ =
  assert_exampled_regex_equiv
    ExampledRegex.mk_empty
    (Brx.to_exampled_regex
       Brx.empty
       [])

let test_to_exampled_regex_concat _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_concat
       ~openable:OpenableData.mk_true
       (ExampledRegex.mk_base "a" [[0]])
       (ExampledRegex.mk_base "b" [[0]])
       [[0]])
    (Brx.to_exampled_regex
       (Brx.mk_seq
          (Brx.mk_string "a")
          (Brx.mk_string "b"))
       ["ab"])

let test_to_exampled_regex_union _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_union
       ~openable:OpenableData.mk_true
       [ExampledRegex.mk_base "bb" [[0]]
       ;ExampledRegex.mk_base "aa" [[1]]]
       [[0];[1]])
    (Brx.to_exampled_regex
       (Brx.mk_alt
          (Brx.mk_string "aa")
          (Brx.mk_string "bb"))
       ["bb";"aa"])

let test_to_exampled_regex_star _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_star
       ~openable:OpenableData.mk_true
       (ExampledRegex.mk_base "a" [[0;0];[1;0]])
       [[0]])
    (Brx.to_exampled_regex
       (Brx.mk_star (Brx.mk_string "a"))
       ["aa"])

let test_to_exampled_regex_iter _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_concat
       ~openable:OpenableData.mk_true
       (ExampledRegex.mk_base "a" [[0]])
       (ExampledRegex.mk_union
          ~openable:OpenableData.mk_true
          [ExampledRegex.mk_base "" []
          ;ExampledRegex.mk_base "a" [[0]]]
          [[0]])
       [[0]])
    (Brx.to_exampled_regex
       (Brx.mk_iter (Brx.mk_string "a") 1 2)
       ["aa"])

let test_to_exampled_regex_cset _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_union
       ~openable:OpenableData.mk_true
       [ExampledRegex.mk_base "B" [[1]]
       ;ExampledRegex.mk_base "A" [[0]]]
       [[0];[1]])
    (Brx.to_exampled_regex
       (Brx.mk_cset [(65,66)])
       ["A";"B"])

let test_to_exampled_regex_concat_ambig _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_concat
       ~openable:(OpenableData.mk_false ["aaaa";"aa"])
       (ExampledRegex.mk_star
          ~openable:(OpenableData.mk_false [])
          (ExampledRegex.mk_base "a" [])
          [])
       (ExampledRegex.mk_star
          ~openable:(OpenableData.mk_false [])
          (ExampledRegex.mk_base "a" [])
          [])
       [[0];[1]])
    (Brx.to_exampled_regex
       (Brx.mk_seq
          (Brx.mk_star (Brx.mk_string "a"))
          (Brx.mk_star (Brx.mk_string "a")))
       ["aaaa";"aa"])

let test_to_exampled_regex_union_ambig _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_union
       ~openable:(OpenableData.mk_false ["a"])
       [ExampledRegex.mk_base "a" []
       ;ExampledRegex.mk_star
          ~openable:(OpenableData.mk_false [])
          (ExampledRegex.mk_base
             "a"
             [])
          []]
       [[0]])
    (Brx.to_exampled_regex
       (Brx.mk_alt
          (Brx.mk_star (Brx.mk_string "a"))
          (Brx.mk_string "a"))
       ["a"])

let test_to_exampled_regex_star_ambig _ =
  assert_exampled_regex_equiv
    (ExampledRegex.mk_star
       ~openable:(OpenableData.mk_false ["aaa"])
       (ExampledRegex.mk_union
          ~openable:(OpenableData.mk_false [])
          [ExampledRegex.mk_base "a" []
          ;ExampledRegex.mk_base "aa" []]
          [])
       [[0]])
    (Brx.to_exampled_regex
       (Brx.mk_star (Brx.mk_alt (Brx.mk_string "a") (Brx.mk_string "aa")))
       ["aaa"])

let to_exampled_regex_suite = "Test Brx to_exampled_regex" >:::
  [
    "test_to_exampled_regex_base" >:: test_to_exampled_regex_base;
    "test_to_exampled_regex_empty" >:: test_to_exampled_regex_empty;
    "test_to_exampled_regex_concat" >:: test_to_exampled_regex_concat;
    "test_to_exampled_regex_union" >:: test_to_exampled_regex_union;
    "test_to_exampled_regex_star" >:: test_to_exampled_regex_star;
    "test_to_exampled_regex_iter" >:: test_to_exampled_regex_iter;
    "test_to_exampled_regex_cset" >:: test_to_exampled_regex_cset;
    "test_to_exampled_regex_concat_ambig" >:: test_to_exampled_regex_concat_ambig;
    "test_to_exampled_regex_union_ambig" >:: test_to_exampled_regex_union_ambig;
    "test_to_exampled_regex_star_ambig" >:: test_to_exampled_regex_star_ambig;
  ]

let _ = run_test_tt_main to_exampled_regex_suite
