/*******************************************************************\

Module: Unit test for local_bitvector_analysis

Author: Diffblue Ltd

\*******************************************************************/

#include <util/c_types.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <goto-programs/goto_instruction_code.h>
#include <goto-programs/goto_model.h>

#include <analyses/local_bitvector_analysis.h>
#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

/// Build `void f() { void *p; p = <allocator>(); }`, run
/// local_bitvector_analysis, and return the flags computed for `p` at the
/// instruction following the allocation call.
static local_bitvector_analysist::flagst
classify_allocation_result(const irep_idt &allocator)
{
  goto_modelt goto_model;

  const typet void_ptr = pointer_type(empty_typet{});

  // a (bodyless) allocator function returning void*
  symbolt allocator_symbol{allocator, code_typet({}, void_ptr), ID_C};
  // the local pointer that receives the result
  symbolt p{"f::p", void_ptr, ID_C};

  code_blockt code{
    {code_frontend_declt{p.symbol_expr()},
     code_function_callt{p.symbol_expr(), allocator_symbol.symbol_expr(), {}},
     code_skipt{}}};

  symbolt f{"f", code_typet({}, empty_typet{}), ID_C};
  f.value = code;

  goto_model.symbol_table.add(allocator_symbol);
  goto_model.symbol_table.add(p);
  goto_model.symbol_table.add(f);

  goto_convert(goto_model, null_message_handler);

  const namespacet ns{goto_model.symbol_table};
  const goto_functiont &fn = goto_model.get_goto_function("f");
  local_bitvector_analysist analysis{fn, ns};

  for(auto it = fn.body.instructions.begin(); it != fn.body.instructions.end();
      ++it)
  {
    if(it->is_function_call())
      return analysis.get(std::next(it), p.symbol_expr());
  }

  UNREACHABLE;
}

SCENARIO(
  "local_bitvector_analysis recognises heap allocators",
  "[core][analyses][local_bitvector_analysis]")
{
  // malloc/calloc/realloc/valloc return a dynamic heap pointer or NULL.
  // This is what lets goto_check_c generate dynamic-object-bounds checks
  // rather than generic object-bounds checks; keep build() honest.
  for(const char *allocator : {"malloc", "calloc", "realloc", "valloc"})
  {
    GIVEN(std::string{"a call to "} + allocator)
    {
      const auto flags = classify_allocation_result(allocator);

      THEN("the result is classified as dynamic-heap-or-null")
      {
        REQUIRE(flags.is_dynamic_heap());
        REQUIRE(flags.is_null());
        REQUIRE_FALSE(flags.is_unknown());
        REQUIRE_FALSE(flags.is_static_lifetime());
      }
    }
  }
}
