/*******************************************************************\

Module: Unit tests for mm_io per-region MMIO instrumentation

Author: Michael Tautschnig

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_function.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/mm_io.h>

#include <testing-utils/use_catch.h>

/// Build a minimal goto_modelt with a single function containing
/// an assignment `*ptr = rhs` where ptr is a cast from an integer constant.
static goto_modelt
build_model_with_deref_write(const mp_integer &address, const exprt &rhs)
{
  goto_modelt model;

  // pointer type: char*
  const typet char_type = signedbv_typet(8);
  const auto ptr_type = pointer_type(char_type);

  // ptr = (char*)<address>
  const constant_exprt addr_const = from_integer(address, signedbv_typet(64));
  const typecast_exprt ptr_val(addr_const, ptr_type);

  // *ptr
  const dereference_exprt deref(ptr_val);

  // Build function body: ASSIGN *ptr = rhs
  goto_programt body;
  body.add(goto_programt::make_assignment(deref, rhs));
  body.add(goto_programt::make_end_function());

  // Add function to model
  symbolt fun_sym;
  fun_sym.name = "test_fun";
  fun_sym.type = code_typet({}, empty_typet());
  fun_sym.mode = ID_C;
  model.symbol_table.add(fun_sym);

  goto_functionst::goto_functiont &gf =
    model.goto_functions.function_map["test_fun"];
  gf.body.swap(body);

  return model;
}

TEST_CASE("mm_io per-region creates symbols", "[core][goto-programs][mm_io]")
{
  std::vector<mmio_regiont> regions;
  regions.emplace_back(
    mp_integer(0x1000), mp_integer(256), CPROVER_PREFIX "mmio_region_0x1000");

  goto_modelt model = build_model_with_deref_write(
    mp_integer(0x1000), from_integer(0x42, signedbv_typet(8)));

  null_message_handlert msg;
  mm_io(model, regions, msg);

  // The region symbol should exist in the symbol table
  const symbolt *sym =
    model.symbol_table.lookup(CPROVER_PREFIX "mmio_region_0x1000");
  REQUIRE(sym != nullptr);
  REQUIRE(sym->type.id() == ID_array);
}

TEST_CASE("mm_io per-region instruments writes", "[core][goto-programs][mm_io]")
{
  std::vector<mmio_regiont> regions;
  regions.emplace_back(
    mp_integer(0x1000), mp_integer(256), CPROVER_PREFIX "mmio_region_0x1000");

  goto_modelt model = build_model_with_deref_write(
    mp_integer(0x1000), from_integer(0x42, signedbv_typet(8)));

  // Count instructions before
  const auto &body_before =
    model.goto_functions.function_map.at("test_fun").body;
  const std::size_t count_before = body_before.instructions.size();

  null_message_handlert msg;
  mm_io(model, regions, msg);

  // After instrumentation, the function should have more instructions
  // (the write dispatch replaces the single assignment)
  const auto &body_after =
    model.goto_functions.function_map.at("test_fun").body;
  REQUIRE(body_after.instructions.size() > count_before);

  // The original dereference assignment should be gone; instead we
  // should find an assignment to the region array symbol
  bool found_region_write = false;
  for(const auto &inst : body_after.instructions)
  {
    if(inst.is_assign())
    {
      const auto &lhs = inst.assign_lhs();
      if(lhs.id() == ID_index)
      {
        const auto &array = to_index_expr(lhs).array();
        if(
          array.id() == ID_symbol && to_symbol_expr(array).get_identifier() ==
                                       CPROVER_PREFIX "mmio_region_0x1000")
        {
          found_region_write = true;
        }
      }
    }
  }
  REQUIRE(found_region_write);
}
