/*******************************************************************\

Module: Jsil Language

Author: Michael Tautschnig, tautschn@amazon.com

\*******************************************************************/

/// \file
/// Jsil Language

#include "jsil_internal_additions.h"

#include <util/std_types.h>
#include <util/cprover_prefix.h>
#include <util/symbol_table.h>

#include <util/c_types.h>

#include "jsil_types.h"

void jsil_internal_additions(symbol_tablet &dest)
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
    // mark as already typechecked
    symbol.is_extern=true;
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
    // mark as already typechecked
    symbol.is_extern=true;
    dest.add(symbol);
  }

  // add eval

  {
    code_typet eval_type;
    code_typet::parametert p;
    eval_type.parameters().push_back(p);

    symbolt symbol;
    symbol.base_name="eval";
    symbol.name="eval";
    symbol.type=eval_type;
    symbol.mode="jsil";
    dest.add(symbol);
  }

  // add nan

  {
    symbolt symbol;
    symbol.base_name="nan";
    symbol.name="nan";
    symbol.type=floatbv_typet();
    symbol.mode="jsil";
    // mark as already typechecked
    symbol.is_extern=true;
    dest.add(symbol);
  }

  // add empty symbol used for decl statements

  {
    symbolt symbol;
    symbol.base_name="decl_symbol";
    symbol.name="decl_symbol";
    symbol.type=empty_typet();
    symbol.mode="jsil";
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
    symbolt new_symbol;
    new_symbol.name=identifier;
    new_symbol.type=jsil_builtin_object_type();
    new_symbol.base_name=identifier;
    new_symbol.mode="jsil";
    new_symbol.is_type=false;
    new_symbol.is_lvalue=false;
    // mark as already typechecked
    new_symbol.is_extern=true;
    dest.add(new_symbol);
  }
}
