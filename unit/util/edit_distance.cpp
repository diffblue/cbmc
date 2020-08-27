/// \file
/// \author Diffblue Ltd.
/// Unit tests for checking if two strings are within a certain edit distance

#include <testing-utils/use_catch.h>
#include <util/edit_distance.h>

TEST_CASE("edit distance 0", "[core][util][edit_distance]")
{
  auto const hello = levenshtein_automatont{"hello", 0};

  // Distance 0
  REQUIRE(hello.matches("hello"));
  REQUIRE(hello.get_edit_distance("hello").value() == 0);

  // Distance 1
  REQUIRE_FALSE(hello.matches("hallo"));
  REQUIRE_FALSE(hello.matches("hell"));
  REQUIRE_FALSE(hello.matches("helloo"));
  REQUIRE_FALSE(hello.matches("chello"));

  // Distance 2
  REQUIRE_FALSE(hello.matches("helol"));
  REQUIRE_FALSE(hello.matches("help"));
  REQUIRE_FALSE(hello.matches("yohello"));

  // Distance 3
  REQUIRE_FALSE(hello.matches("kelp"));
  REQUIRE_FALSE(hello.matches("hilt"));
  REQUIRE_FALSE(hello.matches("wallow"));

  // Distance > 3
  REQUIRE_FALSE(hello.matches("unrelated"));
}

TEST_CASE("edit distance 1", "[core][util][edit_distance]")
{
  auto const hello = levenshtein_automatont{"hello", 1};

  // Distance 0
  REQUIRE(hello.matches("hello"));
  REQUIRE(hello.get_edit_distance("hello").value() == 0);

  // Distance 1
  REQUIRE(hello.matches("hallo"));
  REQUIRE(hello.get_edit_distance("hallo").value() == 1);
  REQUIRE(hello.matches("hell"));
  REQUIRE(hello.get_edit_distance("hell").value() == 1);
  REQUIRE(hello.matches("helloo"));
  REQUIRE(hello.get_edit_distance("helloo").value() == 1);
  REQUIRE(hello.matches("chello"));
  REQUIRE(hello.get_edit_distance("chello").value() == 1);

  // Distance 2
  REQUIRE_FALSE(hello.matches("helol"));
  REQUIRE_FALSE(hello.matches("help"));
  REQUIRE_FALSE(hello.matches("yohello"));

  // Distance 3
  REQUIRE_FALSE(hello.matches("kelp"));
  REQUIRE_FALSE(hello.matches("hilt"));
  REQUIRE_FALSE(hello.matches("wallow"));

  // Distance > 3
  REQUIRE_FALSE(hello.matches("unrelated"));
}

TEST_CASE("edit distance 2", "[core][util][edit_distance]")
{
  auto const hello = levenshtein_automatont{"hello", 2};

  // Distance 0
  REQUIRE(hello.matches("hello"));
  REQUIRE(hello.get_edit_distance("hello").value() == 0);

  // Distance 1
  REQUIRE(hello.matches("hallo"));
  REQUIRE(hello.get_edit_distance("hallo").value() == 1);
  REQUIRE(hello.matches("hell"));
  REQUIRE(hello.get_edit_distance("hell").value() == 1);
  REQUIRE(hello.matches("helloo"));
  REQUIRE(hello.get_edit_distance("helloo").value() == 1);
  REQUIRE(hello.matches("chello"));
  REQUIRE(hello.get_edit_distance("chello").value() == 1);

  // Distance 2
  REQUIRE(hello.matches("helol"));
  REQUIRE(hello.get_edit_distance("helol").value() == 2);
  REQUIRE(hello.matches("help"));
  REQUIRE(hello.get_edit_distance("help").value() == 2);
  REQUIRE(hello.matches("yohello"));
  REQUIRE(hello.get_edit_distance("yohello").value() == 2);

  // Distance 3
  REQUIRE_FALSE(hello.matches("kelp"));
  REQUIRE_FALSE(hello.matches("hilt"));
  REQUIRE_FALSE(hello.matches("wallow"));

  // Distance > 3
  REQUIRE_FALSE(hello.matches("unrelated"));
}

TEST_CASE("edit distance 3", "[core][util][edit_distance]")
{
  auto const hello = levenshtein_automatont{"hello", 3};

  // Distance 0
  REQUIRE(hello.matches("hello"));
  REQUIRE(hello.get_edit_distance("hello").value() == 0);

  // Distance 1
  REQUIRE(hello.matches("hallo"));
  REQUIRE(hello.get_edit_distance("hallo").value() == 1);
  REQUIRE(hello.matches("hell"));
  REQUIRE(hello.get_edit_distance("hell").value() == 1);
  REQUIRE(hello.matches("helloo"));
  REQUIRE(hello.get_edit_distance("helloo").value() == 1);
  REQUIRE(hello.matches("chello"));
  REQUIRE(hello.get_edit_distance("chello").value() == 1);

  // Distance 2
  REQUIRE(hello.matches("helol"));
  REQUIRE(hello.get_edit_distance("helol").value() == 2);
  REQUIRE(hello.matches("help"));
  REQUIRE(hello.get_edit_distance("help").value() == 2);
  REQUIRE(hello.matches("yohello"));
  REQUIRE(hello.get_edit_distance("yohello").value() == 2);

  // Distance 3
  REQUIRE(hello.matches("kelp"));
  REQUIRE(hello.get_edit_distance("kelp").value() == 3);
  REQUIRE(hello.matches("hilt"));
  REQUIRE(hello.get_edit_distance("hilt").value() == 3);
  REQUIRE(hello.matches("wallow"));
  REQUIRE(hello.get_edit_distance("wallow").value() == 3);

  // Distance > 3
  REQUIRE_FALSE(hello.matches("unrelated"));
}
