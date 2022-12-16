/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_internal_additions.h"

#include <util/c_types.h>
#include <util/std_types.h>
#include <util/symbol_table_base.h>

#include <goto-programs/adjust_float_expressions.h>

#include "jsil_types.h"

void jsil_internal_additions(symbol_table_baset &dest)
{
  // add __CPROVER_rounding_mode

  {
    symbolt symbol{rounding_mode_identifier(), signed_int_type(), ID_C};
    symbol.base_name = symbol.name;
    symbol.is_lvalue=true;
    symbol.is_state_var=true;
    symbol.is_thread_local=true;
    // mark as already typechecked
    symbol.is_extern=true;
    dest.add(symbol);
  }

  // add eval

  {
    code_typet eval_type({code_typet::parametert(typet())}, empty_typet());

    symbolt symbol{"eval", eval_type, "jsil"};
    symbol.base_name="eval";
    dest.add(symbol);
  }

  // add nan

  {
    symbolt symbol{"nan", floatbv_typet(), "jsil"};
    symbol.base_name="nan";
    // mark as already typechecked
    symbol.is_extern=true;
    dest.add(symbol);
  }

  // add empty symbol used for decl statements

  {
    symbolt symbol{"decl_symbol", empty_typet(), "jsil"};
    symbol.base_name="decl_symbol";
    // mark as already typechecked
    symbol.is_extern=true;
    dest.add(symbol);
  }

  // add builtin objects
  const std::vector<std::string> builtin_objects=
  {
    "#lg", "#lg_isNan", "#lg_isFinite", "#lop", "#lop_toString",
    "#lop_valueOf", "#lop_isPrototypeOf", "#lfunction", "#lfp",
    "#leval", "#lerror", "#lep", "#lrerror", "#lrep", "#lterror",
    "#ltep", "#lserror", "#lsep", "#levalerror", "#levalerrorp",
    "#lrangeerror", "#lrangeerrorp", "#lurierror", "#lurierrorp",
    "#lobject", "#lobject_get_prototype_of", "#lboolean", "#lbp",
    "#lbp_toString", "#lbp_valueOf", "#lnumber", "#lnp",
    "#lnp_toString", "#lnp_valueOf", "#lmath", "#lstring", "#lsp",
    "#lsp_toString", "#lsp_valueOf", "#larray", "#lap", "#ljson"
  };

  for(const auto &identifier : builtin_objects)
  {
    symbolt new_symbol{identifier, jsil_builtin_object_type(), "jsil"};
    new_symbol.base_name=identifier;
    // mark as already typechecked
    new_symbol.is_extern=true;
    dest.add(new_symbol);
  }
}
