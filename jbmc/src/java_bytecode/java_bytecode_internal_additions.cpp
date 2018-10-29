/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_internal_additions.h"

// For INFLIGHT_EXCEPTION_VARIABLE_NAME
#include "remove_exceptions.h"

#include <util/std_types.h>
#include <util/cprover_prefix.h>
#include <util/c_types.h>

void java_internal_additions(symbol_table_baset &dest)
{
  // add __CPROVER_rounding_mode

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "rounding_mode";
    symbol.name=CPROVER_PREFIX "rounding_mode";
    symbol.type=signed_int_type();
    symbol.mode=ID_C;
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    dest.add(symbol);
  }

  // add __CPROVER_malloc_object

  {
    symbolt symbol;
    symbol.base_name = CPROVER_PREFIX "malloc_object";
    symbol.name=CPROVER_PREFIX "malloc_object";
    symbol.type=pointer_type(empty_typet());
    symbol.mode=ID_C;
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    dest.add(symbol);
  }

  {
    auxiliary_symbolt symbol;
    symbol.base_name = INFLIGHT_EXCEPTION_VARIABLE_BASENAME;
    symbol.name = INFLIGHT_EXCEPTION_VARIABLE_NAME;
    symbol.mode = ID_java;
    symbol.type = pointer_type(empty_typet());
    symbol.type.set(ID_C_no_nondet_initialization, true);
    symbol.value = null_pointer_exprt(to_pointer_type(symbol.type));
    symbol.is_file_local = false;
    symbol.is_static_lifetime = true;
    dest.add(symbol);
  }
}
