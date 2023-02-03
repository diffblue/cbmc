/*******************************************************************\

Module: Unit tests for goto_symex_is_constantt

Author: Diffblue Ltd.

\*******************************************************************/

#include <util/bitvector_types.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-symex/goto_symex_is_constant.h>
#include <testing-utils/use_catch.h>

SCENARIO("goto-symex-is-constant", "[core][goto-symex][is_constant]")
{
  symbol_tablet symbol_table;
  namespacet ns{symbol_table};

  signedbv_typet int_type(32);
  constant_exprt sizeof_constant("4", int_type);
  sizeof_constant.set(ID_C_c_sizeof_type, int_type);
  symbol_exprt non_constant("x", int_type);

  goto_symex_is_constantt is_constant(ns);

  GIVEN("Sizeof expression multiplied by a non-constant")
  {
    mult_exprt non_const_by_sizeof(non_constant, sizeof_constant);
    mult_exprt sizeof_by_non_const(sizeof_constant, non_constant);
    WHEN("We check whether goto-symex regards the expression as constant")
    {
      bool result1 = is_constant(non_const_by_sizeof);
      bool result2 = is_constant(sizeof_by_non_const);

      THEN("Should be constant")
      {
        REQUIRE(result1);
        REQUIRE(result2);
      }
    }
  }

  GIVEN("Non-multiply expression involving a sizeof expression")
  {
    plus_exprt non_const_plus_sizeof(non_constant, sizeof_constant);
    WHEN("We check whether goto-symex regards the expression as constant")
    {
      bool result = is_constant(non_const_plus_sizeof);

      THEN("Should not be constant")
      {
        REQUIRE(!result);
      }
    }
  }
}
