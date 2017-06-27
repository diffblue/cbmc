/*******************************************************************\

 Module: MODULE NAME

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

/// \file
/// Unit tests for util/simplify_expr.cpp

#include <catch.hpp>
#include <util/config.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/ui_message.h>

#include <ansi-c/ansi_c_language.h>


#include <unit-src/unit_util.h>

SCENARIO("Simplifying an expression", "[core][util][simplify_expr]"
    "[simplify_typecast]")
{
  ui_message_handlert message_handler;
  ansi_c_languaget language;
  language.set_message_handler(message_handler);

  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  GIVEN("A namespace with some symbols in on a default architecture")
  {
    array_typet array_type(
      signedbv_typet(32), constant_exprt::integer_constant(5));

    symbolt a_symbol;
    a_symbol.base_name="a";
    a_symbol.name="a";
    a_symbol.type=array_type;
    a_symbol.is_lvalue=true;
    symbol_table.add(a_symbol);

    symbolt i_symbol;
    i_symbol.base_name="i";
    i_symbol.name="i";
    i_symbol.type=signedbv_typet(32);
    i_symbol.is_lvalue=true;
    symbol_table.add(i_symbol);

    config.set_arch("none");

    WHEN("Simplifying a[(signed long int)0]")
    {
      exprt out_expr;
      bool success=language.to_expr("a[(signed long int)0]", "", out_expr, ns);

      // Validate the conversion to expr
      REQUIRE_FALSE(success);
      THEN("Should get a[0]")
      {
        exprt simplified_expr=simplify_expr(out_expr, ns);
        REQUIRE(simplified_expr.id()==ID_index);

        index_exprt index=to_index_expr(simplified_expr);

        const exprt &index_part=index.index();
        REQUIRE(index_part.id()==ID_constant);
      }
    }
    WHEN("Simplifying a[(signed long int)i]")
    {
      exprt out_expr;
      bool success=language.to_expr("a[(signed long int)i]", "", out_expr, ns);

      // Validate the conversion to expr
      REQUIRE_FALSE(success);
      THEN("Should get a[i]")
      {
        exprt simplified_expr=simplify_expr(out_expr, ns);
        REQUIRE(simplified_expr.id()==ID_index);

        index_exprt index=to_index_expr(simplified_expr);

        const exprt &index_part=index.index();
        REQUIRE(index_part.id()==ID_symbol);
        const symbol_exprt symbol_expr=to_symbol_expr(index_part);
        REQUIRE(symbol_expr.get_identifier()=="i");
      }
    }
    WHEN("Simplifying a[(signed int)i]")
    {
      exprt out_expr;
      bool success=language.to_expr("a[(signed int)i]", "", out_expr, ns);

      // Validate the conversion to expr
      REQUIRE_FALSE(success);
      THEN("Should get a[i]")
      {
        exprt simplified_expr=simplify_expr(out_expr, ns);
        REQUIRE(simplified_expr.id()==ID_index);

        index_exprt index=to_index_expr(simplified_expr);

        const exprt &index_part=index.index();
        REQUIRE(index_part.id()==ID_symbol);
        const symbol_exprt symbol_expr=to_symbol_expr(index_part);
        REQUIRE(symbol_expr.get_identifier()=="i");
      }
    }
    WHEN("Simplifying a[(signed short)i]")
    {
      exprt out_expr;
      bool success=language.to_expr("a[(signed short)i]", "", out_expr, ns);

      // Validate the conversion to expr
      REQUIRE_FALSE(success);

      // Since this is cast could go wrong (if i has a value greater than
      // SHRT_MAX for example) it should not be removed by the simplify
      THEN("Should get a[(signed short)i]")
      {
        exprt simplified_expr=simplify_expr(out_expr, ns);
        REQUIRE(simplified_expr.id()==ID_index);

        index_exprt index=to_index_expr(simplified_expr);

        const exprt &index_part=index.index();

        // The expression will have changed as we are still able to remove
        // one type cast (the cast from short to long)
        REQUIRE(index_part.id()==ID_typecast);
        REQUIRE(index_part.type().id()==ID_signedbv);
        signedbv_typet signed_bv_type=to_signedbv_type(index_part.type());
        REQUIRE(signed_bv_type.get_width()==config.ansi_c.short_int_width);
      }
    }
  }
}
