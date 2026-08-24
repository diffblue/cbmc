/*******************************************************************\

Module: Lift nested dereferences unit tests

Author: Kiro

\*******************************************************************/

#include <util/prefix.h>

#include <goto-programs/lift_nested_dereferences.h>

#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

/// Number of temporaries introduced by the transformation (their base names
/// start with "deref_tmp").
static std::size_t count_deref_temporaries(const goto_modelt &goto_model)
{
  std::size_t count = 0;
  for(const auto &entry : goto_model.symbol_table.symbols)
  {
    if(has_prefix(id2string(entry.second.base_name), "deref_tmp"))
      ++count;
  }
  return count;
}

TEST_CASE("Lift nested dereferences", "[core][goto-programs]")
{
  SECTION("chained dereference is lifted into a temporary")
  {
    const std::string code = R"(
      struct node { int data; struct node *next; };

      int f(struct node *p)
      {
        if(p->next)
          return p->next->data;
        return 0;
      }

      void main() { (void)f(0); }
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    REQUIRE(count_deref_temporaries(goto_model) == 0);

    lift_nested_dereferences(goto_model);

    // The chained dereference p->next->data has its intermediate pointer
    // p->next hoisted into a temporary.
    REQUIRE(count_deref_temporaries(goto_model) >= 1);
  }

  SECTION("plain dereference is not lifted")
  {
    const std::string code = R"(
      int g(int *p) { return *p; }
      void main() { int x = 0; (void)g(&x); }
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    lift_nested_dereferences(goto_model);

    REQUIRE(count_deref_temporaries(goto_model) == 0);
  }

  SECTION("concurrent programs are left unchanged")
  {
    // The same chained dereference as above, but in a program that spawns a
    // thread: the transformation must be skipped to avoid collapsing two reads
    // of potentially-shared memory into one.
    const std::string code = R"(
      struct node { int data; struct node *next; };
      struct node *shared;

      void main()
      {
      __CPROVER_ASYNC_1:
        shared->next = 0;

        if(shared->next)
          (void)shared->next->data;
      }
    )";

    goto_modelt goto_model = get_goto_model_from_c(code);
    lift_nested_dereferences(goto_model);

    REQUIRE(count_deref_temporaries(goto_model) == 0);
  }
}
