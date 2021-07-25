/*******************************************************************\

Module: Unit test for expr2c

Author: Diffblue

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <testing-utils/use_catch.h>
#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

TEST_CASE("rol_2_c_conversion_unsigned", "[core][ansi-c][expr2c]")
{
  auto lhs = from_integer(31, unsignedbv_typet(32));
  auto rhs = from_integer(3, unsignedbv_typet(32));
  auto rol = shift_exprt(lhs, ID_rol, rhs);
  CHECK(
    expr2c(rol, namespacet{symbol_tablet{}}) ==
    "31 << 3 % 32 | 31 >> 32 - 3 % 32");
}

TEST_CASE("rol_2_c_conversion_signed", "[core][ansi-c][expr2c]")
{
  // The config lines are necessary since when we do casting from signed
  // to unsigned in the rol/ror bit twiddling we need to output a
  // suitable cast type (e.g. "unsigned int" and not
  // "unsigned __CPROVER_bitvector").
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_i386();
  auto lhs = from_integer(31, signedbv_typet(8));
  auto rhs = from_integer(3, signedbv_typet(8));
  auto rol = shift_exprt(lhs, ID_rol, rhs);
  CHECK(
    expr2c(rol, namespacet{symbol_tablet{}}) ==
    "(unsigned char)31 << 3 % 8 | (unsigned char)31 >> 8 - 3 % 8");
}

TEST_CASE("ror_2_c_conversion_unsigned", "[core][ansi-c][expr2c]")
{
  auto lhs = from_integer(31, unsignedbv_typet(32));
  auto rhs = from_integer(3, unsignedbv_typet(32));
  auto ror = shift_exprt(lhs, ID_ror, rhs);
  CHECK(
    expr2c(ror, namespacet{symbol_tablet{}}) ==
    "31 >> 3 % 32 | 31 << 32 - 3 % 32");
}

TEST_CASE("ror_2_c_conversion_signed", "[core][ansi-c][expr2c]")
{
  // The config lines are necessary since when we do casting from signed
  // to unsigned in the rol/ror bit twiddling we need to output a
  // suitable cast type (e.g. "unsigned int" and not
  // "unsigned __CPROVER_bitvector").
  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;
  config.ansi_c.set_arch_spec_i386();
  auto lhs = from_integer(31, integer_bitvector_typet(ID_signedbv, 32));
  auto rhs = from_integer(3, integer_bitvector_typet(ID_signedbv, 32));
  auto ror = shift_exprt(lhs, ID_ror, rhs);
  CHECK(
    expr2c(ror, namespacet{symbol_tablet{}}) ==
    "(unsigned int)31 >> 3 % 32 | (unsigned int)31 << 32 - 3 % 32");
}
