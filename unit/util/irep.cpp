// Copyright 2018 Michael Tautschnig

/// \file Tests that irept memory consumption is fixed

#include <testing-utils/use_catch.h>
#include <util/irep.h>

SCENARIO("irept_memory", "[core][utils][irept]")
{
  GIVEN("Always")
  {
    THEN("An irept is just a pointer")
    {
      REQUIRE(sizeof(irept) == sizeof(void *));
    }

    THEN("The storage size of an irept is fixed")
    {
#ifdef SHARING
      const std::size_t ref_count_size = sizeof(unsigned);
#else
      const std::size_t ref_count_size = 0;
#endif

#ifndef USE_STD_STRING
      const std::size_t data_size = sizeof(dstringt);
      REQUIRE(sizeof(dstringt) == sizeof(unsigned));
#else
      const std::size_t data_size = sizeof(std::string);
      REQUIRE(sizeof(std::string) == sizeof(void *));
#endif

      const std::size_t sub_size = sizeof(std::vector<int>);
#ifndef _GLIBCXX_DEBUG
      REQUIRE(sizeof(std::vector<int>) == 3 * sizeof(void *));
#endif

#if !NAMED_SUB_IS_FORWARD_LIST
      const std::size_t named_size = sizeof(std::map<int, int>);
#  ifndef _GLIBCXX_DEBUG
#    ifdef __APPLE__
      REQUIRE(sizeof(std::map<int, int>) == 3 * sizeof(void *));
#    elif defined(_WIN32)
      REQUIRE(sizeof(std::map<int, int>) == 2 * sizeof(void *));
#    else
      REQUIRE(sizeof(std::map<int, int>) == 6 * sizeof(void *));
#    endif
#  endif
#else
      const std::size_t named_size = sizeof(std::forward_list<int>);
#  ifndef _GLIBCXX_DEBUG
      REQUIRE(sizeof(std::forward_list<int>) == sizeof(void *));
#  endif
#endif

#if HASH_CODE
      const std::size_t hash_code_size = sizeof(std::size_t);
#else
      const std::size_t hash_code_size = 0;
#endif

      REQUIRE(
        sizeof(irept::dt) ==
        ref_count_size + data_size + sub_size + named_size + hash_code_size);
    }

    THEN("get_nil_irep yields ID_nil")
    {
      REQUIRE(get_nil_irep().id() == ID_nil);
      REQUIRE(get_nil_irep().is_nil());
      REQUIRE(!get_nil_irep().is_not_nil());
    }
  }

  GIVEN("Parts of an irep")
  {
    irept irep("some_id", {{"some_member", irept("other")}}, {irept("op")});

    THEN("It is properly initialized")
    {
      REQUIRE(irep.id() == "some_id");
      REQUIRE(irep.find("some_member") == irept("other"));
      REQUIRE(irep.get_sub().size() == 1);
      REQUIRE(irep.get_sub().front() == irept("op"));
    }
  }

  GIVEN("An initialized irep")
  {
    irept irep("some_id");
    irept irep_copy(irep);
    irept irep_assign = irep;

    irept irep_other("some_other_id");

    THEN("Its id is some_id")
    {
      REQUIRE(irep.id() == "some_id");
      REQUIRE(irep_copy.id() == "some_id");
      REQUIRE(irep_assign.id() == "some_id");

      REQUIRE(irep_other.id() == "some_other_id");

      // TODO(tautschnig): id_string() should be deprecated in favour of
      // id2string(...)
      REQUIRE(irep.id_string().size() == 7);
    }

    THEN("Swapping works")
    {
      irep.swap(irep_other);

      REQUIRE(irep.id() == "some_other_id");
      REQUIRE(irep_copy.id() == "some_id");
      REQUIRE(irep_assign.id() == "some_id");

      REQUIRE(irep_other.id() == "some_id");
    }
  }

  GIVEN("An irep")
  {
    irept irep;

    THEN("Its id is empty")
    {
      REQUIRE(irep.is_not_nil());
      REQUIRE(irep.id().empty());
    }

    THEN("Its id can be set")
    {
      irep.id("new_id");
      REQUIRE(irep.id() == "new_id");
    }

    THEN("find of a non-existent element yields nil")
    {
      REQUIRE(irep.find("no-such-element").is_nil());
    }

    THEN("Adding/removing elements is possible")
    {
      REQUIRE(irep.get_sub().empty());
      REQUIRE(irep.get_named_sub().empty());

      irept &e = irep.add("a_new_element");
      REQUIRE(e.id().empty());
      e.id("some_id");
      REQUIRE(irep.find("a_new_element").id() == "some_id");

      irept irep2("second_irep");
      irep.add("a_new_element", irep2);
      REQUIRE(!irept::is_comment("a_new_element"));
      REQUIRE(irep.find("a_new_element").id() == "second_irep");
      std::size_t named_sub_size =
        std::distance(irep.get_named_sub().begin(), irep.get_named_sub().end());
      REQUIRE(named_sub_size == 1);

      irep.add("#a_comment", irep2);
      REQUIRE(irept::is_comment("#a_comment"));
      REQUIRE(irep.find("#a_comment").id() == "second_irep");
      named_sub_size =
        std::distance(irep.get_named_sub().begin(), irep.get_named_sub().end());
      REQUIRE(named_sub_size == 2);
      REQUIRE(irept::number_of_non_comments(irep.get_named_sub()) == 1);

      irept bak(irep);
      irep.remove("no_such_id");
      REQUIRE(bak == irep);
      irep.remove("a_new_element");
      REQUIRE(bak != irep);
      REQUIRE(irep.find("a_new_element").is_nil());

      irep.move_to_sub(bak);
      REQUIRE(irep.get_sub().size() == 1);

      irep.move_to_named_sub("another_entry", irep2);
      REQUIRE(irep.get_sub().size() == 1);
      named_sub_size =
        std::distance(irep.get_named_sub().begin(), irep.get_named_sub().end());
      REQUIRE(named_sub_size == 2);

      irept irep3;
      irep.move_to_named_sub("#a_comment", irep3);
      REQUIRE(irep.find("#a_comment").id().empty());
      REQUIRE(irep.get_sub().size() == 1);
      named_sub_size =
        std::distance(irep.get_named_sub().begin(), irep.get_named_sub().end());
      REQUIRE(named_sub_size == 2);

      irept irep4;
      irep.move_to_named_sub("#another_comment", irep4);
      named_sub_size =
        std::distance(irep.get_named_sub().begin(), irep.get_named_sub().end());
      REQUIRE(named_sub_size == 3);

      irept irep5("moved_irep");
      irep.add("a_moved_element", std::move(irep5));
      REQUIRE(irep.find("a_moved_element").id() == "moved_irep");
      named_sub_size =
        std::distance(irep.get_named_sub().begin(), irep.get_named_sub().end());
      REQUIRE(named_sub_size == 4);
    }

    THEN("Setting and getting works")
    {
      // TODO(tautschnig): get_string() should be deprecated in favour of
      // id2string(...)
      REQUIRE(irep.get_string("no_such_id").empty());

      REQUIRE(irep.get("no_such_id").empty());
      // TODO(tautschnig): it's not clear whether we need all of the below
      // variants in the API
      REQUIRE(!irep.get_bool("no_such_id"));
      REQUIRE(irep.get_int("no_such_id") == 0);
      REQUIRE(irep.get_size_t("no_such_id") == 0u);
      REQUIRE(irep.get_long_long("no_such_id") == 0);

      irep.set("some_id", "some string");
      REQUIRE(irep.get("some_id") == "some string");
      irept irep2("second_irep");
      irep.set("a_new_element", irep2);
      REQUIRE(irep.find("a_new_element").id() == "second_irep");
      irep.set("numeric_id", 1);
      REQUIRE(irep.get_bool("numeric_id"));
      irep.set("numeric_id", 42);
      REQUIRE(!irep.get_bool("numeric_id"));
      REQUIRE(irep.get_int("numeric_id") == 42);
      REQUIRE(irep.get_size_t("numeric_id") == 42u);
      REQUIRE(irep.get_long_long("numeric_id") == 42);

      irept irep3("move me");
      irep.set("another_moved_element", std::move(irep3));
      REQUIRE(irep.find("another_moved_element").id() == "move me");

      irep.clear();
      REQUIRE(irep.id().empty());
      REQUIRE(irep.get_sub().empty());
      REQUIRE(irep.get_named_sub().empty());

      irep.make_nil();
      REQUIRE(irep.id() == ID_nil);
      REQUIRE(irep.get_sub().empty());
      REQUIRE(irep.get_named_sub().empty());
    }

    THEN("Pretty printing works")
    {
      irept sub("sub_id");

      irep.id("our_id");
      irep.add("some_op", sub);
      irep.add("#comment", sub);
      irep.move_to_sub(sub);

      std::string pretty = irep.pretty();
      REQUIRE(
        pretty ==
        "our_id\n"
        "  * some_op: sub_id\n"
        "  * #comment: sub_id\n"
        "  0: sub_id");
    }

    THEN("Hashing works")
    {
      irep.id("some_id");
      irep.set("#a_comment", 42);

      REQUIRE(irep.hash() != 0);
      REQUIRE(irep.full_hash() != 0);
      REQUIRE(irep.hash() != irep.full_hash());
    }
  }

  GIVEN("Multiple ireps")
  {
    irept irep1, irep2;

    THEN("Comparison works")
    {
      REQUIRE(irep1 == irep2);
      REQUIRE(irep1.full_eq(irep2));

      irep1.id("id1");
      irep2.id("id2");
      REQUIRE(irep1 != irep2);
      const bool one_lt_two = irep1 < irep2;
      const bool two_lt_one = irep2 < irep1;
      REQUIRE(one_lt_two != two_lt_one);
      REQUIRE(irep1.ordering(irep2) != irep2.ordering(irep1));
      REQUIRE(irep1.compare(irep2) != 0);

      irep2.id("id1");
      REQUIRE(irep1 == irep2);
      REQUIRE(irep1.full_eq(irep2));

      irep2.set("#a_comment", 42);
      REQUIRE(irep1 == irep2);
      REQUIRE(!irep1.full_eq(irep2));
    }
  }
}

// This test is expected to fail so that we can test the error printing of the
// unit test framework for regressions. It is not included in the [core] or
// default set of tests, so that the usual output is not polluted with
// irrelevant error messages.
TEST_CASE(
  "Catch2 printing of `irept` for test failures.",
  "[irep_error_printing]" XFAIL)
{
  const irept foo{"foo", irept::named_subt{{"key", irept{"value"}}}, {}};
  const irept bar{"bar"};
  REQUIRE(foo == bar);
}
