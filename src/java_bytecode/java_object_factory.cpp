/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/namespace.h>
#include <util/expr_util.h>

#include "java_object_factory.h"

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  const namespacet &ns,
  std::set<irep_idt> &recursion_set,
  bool is_sub,
  irep_idt class_identifier)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    #if 0
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    if(subtype.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(subtype);
      const irep_idt struct_tag=struct_type.get_tag();

      if(recursion_set.find(struct_tag)!=recursion_set.end())
      {
        // make null
        null_pointer_exprt null_pointer_expr(pointer_type);
        code_assignt code(expr, null_pointer_expr);
        init_code.copy_to_operands(code);

        return;
      }
    }

    // build size expression
    exprt object_size=size_of_expr(subtype, ns);

    if(subtype.id()!=ID_empty && !object_size.is_nil())
    {
      // malloc expression
      side_effect_exprt malloc_expr(ID_malloc);
      malloc_expr.copy_to_operands(object_size);
      malloc_expr.type()=pointer_type;

      code_assignt code(expr, malloc_expr);
      init_code.copy_to_operands(code);

      // dereference expression
      dereference_exprt deref_expr(expr, subtype);

      gen_nondet_init(deref_expr, init_code, ns, recursion_set, false, "");
    }
    else
    {
      // make null
      null_pointer_exprt null_pointer_expr(pointer_type);
      code_assignt code(expr, null_pointer_expr);
      init_code.copy_to_operands(code);
    }
    #endif
  }
  else if(type.id()==ID_struct)
  {
    typedef struct_typet::componentst componentst;

    const struct_typet &struct_type=to_struct_type(type);
    const irep_idt struct_tag=struct_type.get_tag();

    const componentst &components=struct_type.components();

    recursion_set.insert(struct_tag);
    assert(!recursion_set.empty());

    for(const auto & component : components)
    {
      const typet &component_type=component.type();
      irep_idt name=component.get_name();

      member_exprt me(expr, name, component_type);

      if(name=="@class_identifier")
      {
        irep_idt qualified_clsid="java::"+as_string(class_identifier);
        constant_exprt ci(qualified_clsid, string_typet());

        code_assignt code(me, ci);
        init_code.copy_to_operands(code);
      }
      else if(name=="@lock")
      {
        code_assignt code(me, gen_zero(me.type()));
        init_code.copy_to_operands(code);
      }
      else
      {
        assert(!name.empty());

        bool _is_sub = name[0]=='@';
        irep_idt _class_identifier=
          _is_sub?(class_identifier.empty()?struct_tag:class_identifier):"";

        gen_nondet_init(
          me, init_code, ns, recursion_set, _is_sub, _class_identifier);
      }
    }

    recursion_set.erase(struct_tag);
  }
  else
  {
    side_effect_expr_nondett se=side_effect_expr_nondett(type);

    code_assignt code(expr, se);
    init_code.copy_to_operands(code);
  }
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  const namespacet &ns)
{
  std::set<irep_idt> recursion_set;
  gen_nondet_init(expr, init_code, ns, recursion_set, false, "");
}
}

/*******************************************************************\

Function: new_tmp_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
symbolt &new_tmp_symbol(symbol_tablet &symbol_table)
{
  static int temporary_counter=0;

  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.name="tmp_object_factory$"+i2string(++temporary_counter);
    new_symbol.base_name=new_symbol.name;
    new_symbol.mode=ID_java;
  } while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
}
}

/*******************************************************************\

Function: object_factory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt object_factory(
  const typet &type,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table)
{
  if(type.id()==ID_pointer)
  {
    symbolt &aux_symbol=new_tmp_symbol(symbol_table);
    aux_symbol.type=type.subtype();
    aux_symbol.is_static_lifetime=true;

    exprt object=aux_symbol.symbol_expr();

    const namespacet ns(symbol_table);
    gen_nondet_init(object, init_code, ns);

    // todo: need to pass null, possibly
    return address_of_exprt(object);
  }
  else if(type.id()==ID_c_bool)
  {
    // We force this to 0 and 1 and won't consider
    // other values.
    return typecast_exprt(side_effect_expr_nondett(bool_typet()), type);
  }
  else
    return side_effect_expr_nondett(type);
}
