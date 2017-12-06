open Optician.Normalized_lang
open Ounit_general_extensions

let assert_exampled_regex_equiv =
  assert_equal
    ~cmp:(ExampledRegex.compare)
    ~printer:(ExampledRegex.show)
