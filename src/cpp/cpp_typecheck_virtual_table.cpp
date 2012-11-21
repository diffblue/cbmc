/*******************************************************************\

Function: cpp_typecheckt::do_virtual_table

Inputs:

Outputs:

Purpose:

\*******************************************************************/

#include <std_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include "cpp_typecheck.h"

void cpp_typecheckt::do_virtual_table(const symbolt &symbol)
{
  assert(symbol.type.id()==ID_struct);

  // builds virtual-table value maps: (class x virtual_name x value)
  std::map<irep_idt, std::map<irep_idt,exprt> > vt_value_maps; 

  const struct_typet &struct_type = to_struct_type(symbol.type);

  for(unsigned i = 0; i < struct_type.components().size(); i++)
  {
    const struct_typet::componentt& compo = struct_type.components()[i];
    if(!compo.get_bool("is_virtual"))
      continue;

    const code_typet& code_type = to_code_type(compo.type());
    assert(code_type.arguments().size() > 0);

    const pointer_typet& pointer_type =
      static_cast<const pointer_typet&>(code_type.arguments()[0].type());

    irep_idt class_id = pointer_type.subtype().get("identifier");

    std::map<irep_idt,exprt>& value_map =
      vt_value_maps[class_id];


    exprt e = symbol_exprt(compo.get_name(),code_type);

    if(compo.get_bool("is_pure_virtual"))
    {
      pointer_typet pointer_type(code_type);
      e = gen_zero(pointer_type);
      assert(e.is_not_nil());
      value_map[compo.get("virtual_name")] = e;
    }
    else
    {
      address_of_exprt address(e);
      value_map[compo.get("virtual_name")] = address;
    }
  }

  // create virtual-table symbol variables
  for(std::map<irep_idt, std::map<irep_idt,exprt> >::const_iterator cit =
      vt_value_maps.begin(); cit != vt_value_maps.end(); cit++)
  {
    const std::map<irep_idt,exprt>& value_map = cit->second;

    const symbolt& late_cast_symb = namespacet(context).lookup(cit->first); 
    const symbolt& vt_symb_type = namespacet(context).lookup("virtual_table::"+id2string(late_cast_symb.name));

    symbolt vt_symb_var;
    vt_symb_var.name=  id2string(vt_symb_type.name) + "@"+ id2string(symbol.name);
    vt_symb_var.base_name= id2string(vt_symb_type.base_name) + "@" + id2string(symbol.base_name);
    vt_symb_var.mode=ID_cpp;
    vt_symb_var.module=module;
    vt_symb_var.location=vt_symb_type.location;
    vt_symb_var.type = symbol_typet(vt_symb_type.name);
    vt_symb_var.is_lvalue = true;
    vt_symb_var.is_static_lifetime = true;

    // do the values
    const struct_typet &vt_type = to_struct_type(vt_symb_type.type);

    exprt values(ID_struct, symbol_typet(vt_symb_type.name));

    for(unsigned i=0; i < vt_type.components().size(); i++)
    {
      const struct_typet::componentt& compo = vt_type.components()[i];
      std::map<irep_idt,exprt>::const_iterator cit2 =
        value_map.find( compo.get("base_name"));
      assert(cit2 != value_map.end());
      const exprt& value = cit2->second;
      assert(value.type() == compo.type());
      values.operands().push_back(value);
    }
    vt_symb_var.value = values;

    bool failed = context.move(vt_symb_var);
    assert(!failed);
  }
}
