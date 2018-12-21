/*******************************************************************\

Module: Unit tests for ai_domain_baset::ai_simplify_lhs

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for ai_domain_baset::ai_simplify_lhs

#include <testing-utils/catch.hpp>
#include <testing-utils/message.h>

#include <analyses/ai.h>

#include <ansi-c/ansi_c_language.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/ui_message.h>
#include <util/simplify_expr.h>

class constant_simplification_mockt:public ai_domain_baset
{
public:
  void transform(
    const irep_idt &,
    locationt,
    const irep_idt &,
    locationt,
    ai_baset &,
    const namespacet &) override
  {}
  void make_bottom() override
  {}
  void make_top() override
  {}
  void make_entry() override
  {}
  bool is_bottom() const override
  {
    UNREACHABLE;
    return true;
  }
  bool is_top() const override
  {
    UNREACHABLE;
    return true;
  }

  bool ai_simplify(exprt &condition, const namespacet &ns) const override;
};

bool constant_simplification_mockt::ai_simplify(
  exprt &condition, const namespacet &ns) const
{
  exprt simplified_expr=simplify_expr(condition, ns);
  // no simplification
  if(simplified_expr==condition)
  {
    return true;
  }
  // a simplification has occurred
  condition=simplified_expr;
  return false;
}

SCENARIO("ai_domain_baset::ai_simplify_lhs",
  "[core][analyses][ai][ai_simplify_lhs]")
{
  ui_message_handlert message_handler(null_message_handler);
  ansi_c_languaget language;
  language.set_message_handler(message_handler);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);

  constant_simplification_mockt mock_ai_domain;

  config.set_arch("none");

  GIVEN("A index_exprt")
  {
    // Construct an expression that the simplify_expr can simplify
    exprt simplifiable_expression;
    bool compile_failed=
      language.to_expr("1 + 1", "", simplifiable_expression, ns);

    const unsigned int array_size=5;
    array_typet array_type(
      signedbv_typet(32), from_integer(array_size, size_type()));

    // Verify the results of the setup
    REQUIRE_FALSE(compile_failed);
    REQUIRE(simplifiable_expression.id()==ID_plus);
    exprt simplified_version=simplify_expr(simplifiable_expression, ns);
    REQUIRE(simplified_version.id()==ID_constant);

    WHEN(
      "Simplifying an index expression with constant index but variable array")
    {
      const index_exprt &index_expr=
        index_exprt(symbol_exprt("a", array_type), simplifiable_expression);

      THEN("Then only the index of the part of the expression should be "
        "simplified")
      {
        exprt out_expr=index_expr;
        bool no_simplification=mock_ai_domain.ai_simplify_lhs(out_expr, ns);
        REQUIRE_FALSE(no_simplification);
        REQUIRE(index_expr.id()==ID_index);

        index_exprt simplified_index_expr=to_index_expr(out_expr);
        REQUIRE(simplified_index_expr.index().id()==ID_constant);

        constant_exprt constant_index=
          to_constant_expr(simplified_index_expr.index());

        mp_integer out_index;
        bool failed_to_integer=to_integer(constant_index, out_index);
        REQUIRE_FALSE(failed_to_integer);
        REQUIRE(out_index==2);
      }
    }
    WHEN("Simplifying an index expression with variable index and array")
    {
      // a[i]
      const index_exprt &index_expr=
        index_exprt(
          symbol_exprt("a", array_type), symbol_exprt("i", signedbv_typet(32)));

      THEN("Then no simplification should occur")
      {
        exprt out_expr=index_expr;
        bool no_simplification=mock_ai_domain.ai_simplify_lhs(out_expr, ns);
        REQUIRE(no_simplification);
        REQUIRE(index_expr.id()==ID_index);

        index_exprt simplified_index_expr=to_index_expr(out_expr);
        REQUIRE(simplified_index_expr.index().id()==ID_symbol);
      }
    }

    // This fails since the implementation does do a constant simplification
    // on the array part. It isn't clear to me if this is correct
#if 0
    WHEN(
      "Simplifying an index expression with constant index in a constant array")
    {
      array_exprt constant_array=array_exprt(array_type);
      for(unsigned int i=0; i<array_size; ++i)
      {
        REQUIRE(constant_array.operands().size()==i);
        constant_array.operands().push_back(
          from_integer(i, signedbv_typet(32)));
      }

      const index_exprt &index_expr=
        index_exprt(constant_array, simplifiable_expression);

      THEN("Then only the index of the part of the expression should be "
        "simplified")
      {
        exprt out_expr=index_expr;
        bool no_simplification=mock_ai_domain.ai_simplify_lhs(out_expr, ns);
        REQUIRE_FALSE(no_simplification);
        REQUIRE(out_expr.id()==ID_index);

        index_exprt simplified_index_expr=to_index_expr(out_expr);
        REQUIRE(simplified_index_expr.index().id()==ID_constant);

        constant_exprt constant_index=
          to_constant_expr(simplified_index_expr.index());

        mp_integer out_index;
        bool failed_to_integer=to_integer(constant_index, out_index);
        REQUIRE_FALSE(failed_to_integer);
        REQUIRE(out_index==2);
      }
    }
#endif
  }
}
