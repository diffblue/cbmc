/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_bytecode_internal_additions.h"

// For INFLIGHT_EXCEPTION_VARIABLE_NAME
#include "java_types.h"
#include "remove_exceptions.h"

#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_types.h>
#include <util/symbol_table_base.h>

#include <goto-programs/adjust_float_expressions.h>

void java_internal_additions(symbol_table_baset &dest)
{
  // add __CPROVER_rounding_mode

  {
    symbolt symbol{rounding_mode_identifier(), signed_int_type(), ID_C};
    symbol.base_name = symbol.name;
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    dest.add(symbol);
  }

  {
    auxiliary_symbolt symbol{
      INFLIGHT_EXCEPTION_VARIABLE_NAME,
      pointer_type(java_void_type()),
      ID_java};
    symbol.base_name = INFLIGHT_EXCEPTION_VARIABLE_BASENAME;
    symbol.type.set(ID_C_no_nondet_initialization, true);
    symbol.value = null_pointer_exprt(to_pointer_type(symbol.type));
    symbol.is_static_lifetime = true;
    dest.add(symbol);
  }
}
