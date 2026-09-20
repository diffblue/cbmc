/*******************************************************************\

Module: Unit test for restoring configt::ansi_ct::argument_evaluation_order
        from goto binaries

Author: Michael Tautschnig

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_model.h>

#include <testing-utils/config_restore.h>
#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

TEST_CASE(
  "argument evaluation order is restored from goto binaries",
  "[core][util][config]")
{
  config_restoret restore_config;

  using aeot = configt::ansi_ct::argument_evaluation_ordert;

  // get_goto_model_from_c resets the configuration to host defaults, so pin
  // the recorded architecture and the loading tool's compiler flavour
  // afterwards to make this test independent of the host
  goto_modelt goto_model = get_goto_model_from_c("int main() { return 0; }");

  symbolt &arch_symbol = goto_model.symbol_table.get_writeable_ref(
    CPROVER_PREFIX "architecture_arch");
  arch_symbol.value = address_of_exprt{
    index_exprt{string_constantt{"x86_64"}, from_integer(0, c_index_type())}};

  config.ansi_c.mode = configt::ansi_ct::flavourt::GCC;

  SECTION("the recorded value overrides the architecture default")
  {
    // record left-to-right, which differs from the x86_64/GCC default of
    // right-to-left, to show that the recorded value takes precedence
    symbolt &aeo_symbol = goto_model.symbol_table.get_writeable_ref(
      CPROVER_PREFIX "architecture_argument_evaluation_order");
    aeo_symbol.value =
      from_integer(static_cast<int>(aeot::LEFT_TO_RIGHT), aeo_symbol.type);

    config.set_from_symbol_table(goto_model.symbol_table);
    REQUIRE(config.ansi_c.argument_evaluation_order == aeot::LEFT_TO_RIGHT);
  }

  SECTION("without the symbol the architecture default is used")
  {
    // model a goto binary created before the architecture parameter existed
    goto_model.symbol_table.remove(CPROVER_PREFIX
                                   "architecture_argument_evaluation_order");

    config.set_from_symbol_table(goto_model.symbol_table);
    REQUIRE(config.ansi_c.argument_evaluation_order == aeot::RIGHT_TO_LEFT);
  }
}
