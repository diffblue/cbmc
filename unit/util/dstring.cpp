/*******************************************************************\

Module: Unit tests for dstringt

Author: Diffblue Ltd

\*******************************************************************/

/// \file
/// Unit tests for constructing dstringt via std::string_view, in particular
/// the embedded-NUL and non-NUL-terminated content that the (ptr, len)
/// string_container representation can express but the previous const char*
/// path could not.

#include <util/dstring.h>
#include <util/string_hash.h>

#include <testing-utils/use_catch.h>

#include <string>
#include <string_view>

TEST_CASE("dstringt string_view construction", "[core][util][dstring]")
{
  SECTION("const char*, std::string and std::string_view agree on ids")
  {
    const dstringt from_char_ptr{"hello"};
    const dstringt from_string{std::string{"hello"}};
    const dstringt from_view{std::string_view{"hello"}};

    REQUIRE(from_char_ptr == from_string);
    REQUIRE(from_char_ptr == from_view);
    REQUIRE(from_char_ptr.get_no() == from_view.get_no());

    // the hashing formula must agree across the entry points too
    REQUIRE(hash_string(std::string_view{"hello"}) == hash_string("hello", 5));
  }

  SECTION("content with an embedded NUL is distinct and round-trips")
  {
    const std::string embedded{"a\0b", 3};
    const dstringt with_nul{std::string_view{embedded}};
    const dstringt just_a{"a"};

    REQUIRE(with_nul != just_a);
    REQUIRE(as_string(with_nul).size() == 3);
    REQUIRE(as_string(with_nul) == embedded);
  }

  SECTION("a non-NUL-terminated sub-view stores exactly size() bytes")
  {
    // buffer[3] is 'd', i.e. the sub-view is not NUL-terminated at its end
    const char buffer[] = "abcdef";
    const std::string_view sub{buffer, 3};
    const dstringt d{sub};

    REQUIRE(as_string(d).size() == 3);
    REQUIRE(as_string(d) == "abc");
  }
}
