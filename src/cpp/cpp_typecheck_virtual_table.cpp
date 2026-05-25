/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include <util/c_types.h>
#include <util/pointer_expr.h>
#include <util/std_expr.h>
#include <util/symbol_table_base.h>

#include "cpp_typecheck.h"

void cpp_typecheckt::do_virtual_table(const symbolt &symbol)
{
  PRECONDITION(symbol.type.id() == ID_struct);

  // builds virtual-table value maps: (class x virtual_name x value)
  std::map<irep_idt, std::map<irep_idt, exprt> > vt_value_maps;

  const struct_typet &struct_type=to_struct_type(symbol.type);

  for(std::size_t i=0; i < struct_type.components().size(); i++)
  {
    const struct_typet::componentt &compo=struct_type.components()[i];
    if(!compo.get_bool(ID_is_virtual))
      continue;

    const code_typet &code_type=to_code_type(compo.type());
    DATA_INVARIANT(code_type.parameters().size() > 0, "parameters expected");

    const pointer_typet &parameter_pointer_type=
      to_pointer_type(code_type.parameters()[0].type());

    const irep_idt &class_id =
      parameter_pointer_type.base_type().get(ID_identifier);

    std::map<irep_idt, exprt> &value_map =
      vt_value_maps[class_id];

    exprt e=symbol_exprt(compo.get_name(), code_type);

    if(compo.get_bool(ID_is_pure_virtual))
    {
      pointer_typet code_pointer_type=pointer_type(code_type);
      e=null_pointer_exprt(code_pointer_type);
      value_map[compo.get(ID_virtual_name)] = e;
    }
    else
    {
      address_of_exprt address(e);
      value_map[compo.get(ID_virtual_name)] = address;
    }
  }

  // create virtual-table symbol variables
  for(std::map<irep_idt, std::map<irep_idt, exprt> >::const_iterator cit =
      vt_value_maps.begin(); cit!=vt_value_maps.end(); cit++)
  {
    const std::map<irep_idt, exprt> &value_map=cit->second;

    const symbolt &late_cast_symb = lookup(cit->first);
    const symbolt &vt_symb_type =
      lookup("virtual_table::" + id2string(late_cast_symb.name));

    symbolt vt_symb_var{
      id2string(vt_symb_type.name) + "@" + id2string(symbol.name),
      struct_tag_typet(vt_symb_type.name),
      symbol.mode};
    vt_symb_var.base_name=
      id2string(vt_symb_type.base_name) + "@" + id2string(symbol.base_name);
    vt_symb_var.module=module;
    vt_symb_var.location=vt_symb_type.location;
    vt_symb_var.is_lvalue=true;
    vt_symb_var.is_static_lifetime=true;

    // do the values
    const struct_typet &vt_type=to_struct_type(vt_symb_type.type);

    struct_exprt values({}, struct_tag_typet(vt_symb_type.name));

    bool type_mismatch = false;
    for(const auto &compo : vt_type.components())
    {
      std::map<irep_idt, exprt>::const_iterator cit2 =
        value_map.find(compo.get_base_name());
      CHECK_RETURN(cit2 != value_map.end());
      const exprt &value=cit2->second;
      if(value.type() != compo.type())
      {
        // Type mismatch between a vtable slot's component and the
        // function value inserted there.  This can occur when an
        // earlier front-end error (e.g., a failed implicit
        // conversion in a base-class constructor invocation) left
        // the class partially elaborated.  Skip vtable
        // construction rather than aborting via DATA_INVARIANT.
        type_mismatch = true;
        break;
      }
      values.operands().push_back(value);
    }
    if(type_mismatch)
      continue;
    vt_symb_var.value=values;

    bool failed=!symbol_table.insert(std::move(vt_symb_var)).second;
    CHECK_RETURN(!failed);
  }
}
