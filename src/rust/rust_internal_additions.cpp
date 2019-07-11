/*******************************************************************\

Module: Rust Language

Author: Brett Schiff, bschiff@amazon.com

\*******************************************************************/
// Adapted from the similarly named file in the jsil directory

/// \file
/// Rust Language

#include "rust_internal_additions.h"

#include <util/cprover_prefix.h>
#include <util/std_types.h>
#include <util/symbol_table.h>

#include <util/c_types.h>

void rust_internal_additions(symbol_tablet &dest)
{
  // add __CPROVER_rounding_mode

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "rounding_mode";
    symbol.name = CPROVER_PREFIX "rounding_mode";
    symbol.type = signed_int_type();
    symbol.mode = ID_C;
    symbol.is_lvalue = true;
    symbol.is_state_var = true;
    symbol.is_thread_local = true;
    // mark as already typechecked
    symbol.is_extern = true;
    dest.add(symbol);
  }

  // add __CPROVER_malloc_object

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "malloc_object";
    symbol.name = CPROVER_PREFIX "malloc_object";
    symbol.type = pointer_type(empty_typet());
    symbol.mode = ID_C;
    symbol.is_lvalue = true;
    symbol.is_state_var = true;
    symbol.is_thread_local = true;
    // mark as already typechecked
    symbol.is_extern = true;
    dest.add(symbol);
  }

  // add __CPROVER_dead_object

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "dead_object";
    symbol.name = CPROVER_PREFIX "dead_object";
    symbol.type = pointer_type(empty_typet());
    symbol.mode = ID_C;
    symbol.is_lvalue = true;
    symbol.is_state_var = true;
    symbol.is_thread_local = true;
    // mark as already typechecked
    symbol.is_extern = true;
    dest.add(symbol);
  }

  // add __CPROVER_deallocated

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "deallocated";
    symbol.name = CPROVER_PREFIX "deallocated";
    symbol.type = pointer_type(empty_typet());
    symbol.mode = ID_C;
    symbol.is_lvalue = true;
    symbol.is_state_var = true;
    symbol.is_thread_local = true;
    // mark as already typechecked
    symbol.is_extern = true;
    dest.add(symbol);
  }

  // add __CPROVER_malloc_size

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "malloc_size";
    symbol.name = CPROVER_PREFIX "malloc_size";
    symbol.type = size_type();
    symbol.mode = ID_C;
    symbol.is_lvalue = true;
    symbol.is_state_var = true;
    symbol.is_thread_local = true;
    // mark as already typechecked
    symbol.is_extern = true;
    dest.add(symbol);
  }
}
