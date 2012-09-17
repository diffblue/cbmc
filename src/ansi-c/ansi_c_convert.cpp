/*******************************************************************\

Module: ANSI-C Conversion

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>
#include <config.h>

#include "ansi_c_convert.h"
#include "ansi_c_convert_type.h"
#include "ansi_c_declaration.h"

/*******************************************************************\

Function: ansi_c_convertt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convertt::convert(ansi_c_parse_treet &ansi_c_parse_tree)
{
  for(ansi_c_parse_treet::itemst::iterator
      it=ansi_c_parse_tree.items.begin();
      it!=ansi_c_parse_tree.items.end();
      it++)
  {
    assert(it->id()==ID_declaration);
    convert_declaration(*it);
  }
}

/*******************************************************************\

Function: ansi_c_convertt::convert_declaration

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convertt::convert_declaration(ansi_c_declarationt &declaration)
{
  c_storage_spect c_storage_spec;

  convert_type(declaration.type(), c_storage_spec);

  declaration.set_is_inline(c_storage_spec.is_inline);
  declaration.set_is_static(c_storage_spec.is_static);
  declaration.set_is_extern(c_storage_spec.is_extern);
  declaration.set_is_thread_local(c_storage_spec.is_thread_local);
  declaration.set_is_register(c_storage_spec.is_register);

  // do not overwrite is_typedef -- it's done by the parser
  // typedefs are macros
  if(declaration.get_is_typedef())
    declaration.set_is_macro(true);

  if(declaration.value().is_not_nil())
  {
    if(declaration.type().id()==ID_code)
      convert_code(to_code(declaration.value()));
    else
      convert_expr(declaration.value());
  }
}

/*******************************************************************\

Function: ansi_c_convertt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convertt::convert_expr(exprt &expr)
{
  if(expr.id()==ID_sideeffect)
  {
    const irep_idt &statement=expr.get(ID_statement);

    if(statement==ID_statement_expression)
    {
      assert(expr.operands().size()==1);
      convert_code(to_code(expr.op0()));
      return;
      // done
    }
  }

  Forall_operands(it, expr)
    convert_expr(*it);

  if(expr.id()==ID_symbol)
  {
    expr.remove(ID_C_id_class);
    expr.remove(ID_C_base_name);
  }
  else if(expr.id()==ID_sizeof)
  {
    if(expr.operands().size()==0)
    {
      typet &type=static_cast<typet &>(expr.add(ID_type_arg));
      convert_type(type);
    }
  }
  else if(expr.id()==ID_designated_initializer)
  {
    exprt &designator=static_cast<exprt &>(expr.add(ID_designator));
    convert_expr(designator);
  }
  else if(expr.id()==ID_alignof)
  {
    if(expr.operands().size()==0)
    {
      typet &type=static_cast<typet &>(expr.add(ID_type_arg));
      convert_type(type);
    }
  }
  else if(expr.id()==ID_gcc_builtin_va_arg)
  {
    convert_type(expr.type());
  }
  else if(expr.id()==ID_generic_selection)
  {
    assert(expr.operands().size()==1);

    irept::subt &generic_associations=
      expr.add(ID_generic_associations).get_sub();

    Forall_irep(it, generic_associations)
    {
      convert_expr(static_cast<exprt &>(it->add(ID_value)));
      convert_type(static_cast<typet &>(it->add(ID_type_arg)));
    }
  }
  else if(expr.id()==ID_gcc_builtin_types_compatible_p)
  {
    typet &type=(typet &)expr;
    assert(type.subtypes().size()==2);
    convert_type(type.subtypes()[0]);
    convert_type(type.subtypes()[1]);
  }
  else if(expr.id()==ID_builtin_offsetof)
  {
    typet &type=static_cast<typet &>(expr.add(ID_type_arg));
    convert_type(type);
    exprt &designator=static_cast<exprt &>(expr.add(ID_designator));
    convert_expr(designator);
  }
  else if(expr.id()==ID_cw_va_arg_typeof)
  {
    typet &type=static_cast<typet &>(expr.add(ID_type_arg));
    convert_type(type);
  }
  else if(expr.id()==ID_typecast)
  {
    convert_type(expr.type());
  }
}

/*******************************************************************\

Function: ansi_c_convertt::convert_code

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convertt::convert_code(codet &code)
{
  const irep_idt &statement=code.get_statement();

  if(statement==ID_expression)
  {
    assert(code.operands().size()==1);
    convert_expr(code.op0());
  }
  else if(statement==ID_decl_type)
  {
    // type only
    assert(code.operands().size()==0);
    convert_type(static_cast<typet &>(code.add(ID_type_arg)));
  }
  else if(statement==ID_decl)
  {
    // 1 or 2 operands
    if(code.operands().size()==1)
      convert_expr(code.op0());
    else if(code.operands().size()==2)
    {
      convert_expr(code.op0());
      convert_expr(code.op1());
    }
    else
      assert(false);
  }
  else if(statement==ID_label)
  {
    assert(code.operands().size()==1);
    convert_code(to_code(code.op0()));

    if(code.find(ID_case).is_not_nil())
      convert_expr(static_cast<exprt &>(code.add(ID_case)));
  }
  else if(statement==ID_block ||
          statement==ID_decl_block)
  {
    Forall_operands(it, code)
      convert_code(to_code(*it));
  }
  else if(statement==ID_ifthenelse)
  {
    assert(code.operands().size()==2 ||
           code.operands().size()==3);

    convert_expr(code.op0());
    convert_code(to_code(code.op1()));

    if(code.operands().size()==3)
      convert_code(to_code(code.op2()));
  }
  else if(statement==ID_while ||
          statement==ID_dowhile)
  {
    assert(code.operands().size()==2);

    convert_expr(code.op0());
    convert_code(to_code(code.op1()));
  }
  else if(statement==ID_for)
  {
    assert(code.operands().size()==4);

    if(code.op0().is_not_nil())
      convert_code(to_code(code.op0()));

    if(code.op1().is_not_nil())
      convert_expr(code.op1());

    if(code.op2().is_not_nil())
      convert_expr(code.op2());

    convert_code(to_code(code.op3()));
  }
  else if(statement==ID_msc_try_except)
  {
    assert(code.operands().size()==3);
    convert_code(to_code(code.op0()));
    convert_expr(code.op1());
    convert_code(to_code(code.op2()));
  }
  else if(statement==ID_msc_try_finally)
  {
    assert(code.operands().size()==2);
    convert_code(to_code(code.op0()));
    convert_code(to_code(code.op1()));
  }
  else if(statement==ID_switch)
  {
    assert(code.operands().size()==2);

    convert_expr(code.op0());
    convert_code(to_code(code.op1()));
  }
  else if(statement==ID_break)
  {
  }
  else if(statement==ID_goto)
  {
  }
  else if(statement=="computed-goto")
  {
    assert(code.operands().size()==1);

    convert_expr(code.op0());
  }
  else if(statement==ID_continue)
  {
  }
  else if(statement==ID_return)
  {
    if(code.operands().size()==1)
      convert_expr(code.op0());
  }
  else if(statement==ID_static_assert)
  {
    assert(code.operands().size()==2);
    convert_expr(code.op0());
    convert_expr(code.op1());
  }
  else if(statement==ID_decl)
  {
    assert(code.operands().size()==1 ||
           code.operands().size()==2);

    convert_type(code.op0().type());

    if(code.operands().size()==2)
      convert_expr(code.op1());
  }
  else if(statement==ID_skip)
  {
  }
  else if(statement==ID_asm || statement==ID_msc)
  {
  }
  else if(statement==ID_gcc_local_label)
  {
  }
  else
  {
    err_location(code);
    str << "unexpected statement during conversion: " << statement;
    throw 0;
  }
}

/*******************************************************************\

Function: ansi_c_convertt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convertt::convert_type(typet &type)
{
  c_storage_spect c_storage_spec;
  convert_type(type, c_storage_spec);
}

/*******************************************************************\

Function: ansi_c_convertt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_convertt::convert_type(
  typet &type,
  c_storage_spect &c_storage_spec)
{
  {
    ansi_c_convert_typet ansi_c_convert_type(get_message_handler());

    ansi_c_convert_type.read(type);
    ansi_c_convert_type.write(type);
    c_storage_spec=ansi_c_convert_type.c_storage_spec;
  }

  // do we have alignment?
  if(type.find(ID_C_alignment).is_not_nil())
    convert_expr(static_cast<exprt &>(type.add(ID_C_alignment)));

  if(type.id()==ID_pointer)
  {
    c_storage_spect sub_storage_spec;

    convert_type(type.subtype(), sub_storage_spec);
    c_storage_spec|=sub_storage_spec;
  }
  else if(type.id()==ID_c_bitfield)
  {
    convert_type(type.subtype());
    convert_expr(static_cast<exprt &>(type.add(ID_size)));
  }
  else if(type.id()==ID_symbol)
  {
    type.remove(ID_C_id_class);
    type.remove(ID_C_base_name);
  }
  else if(type.id()==ID_code)
  {
    c_storage_spect sub_storage_spec;

    convert_type(type.subtype(), sub_storage_spec);
    c_storage_spec|=sub_storage_spec;

    code_typet &code_type=to_code_type(type);

    // change subtype to return_type
    code_type.return_type().swap(type.subtype());
    type.remove(ID_subtype);

    // take care of argument types
    code_typet::argumentst &arguments=code_type.arguments();

    // see if we have an ellipsis
    if(!arguments.empty() &&
       arguments.back().id()==ID_ellipsis)
    {
      code_type.make_ellipsis();
      arguments.pop_back();
    }

    for(code_typet::argumentst::iterator
        it=arguments.begin();
        it!=arguments.end();
        it++)
    {
      if(it->id()==ID_declaration)
      {
        code_typet::argumentt argument;

        ansi_c_declarationt &declaration=
          to_ansi_c_declaration(*it);

        convert_type(declaration.type());

        irep_idt base_name=declaration.get_base_name();

        argument.type().swap(declaration.type());
        argument.set_base_name(base_name);
        argument.location()=declaration.location();
        argument.set_identifier(declaration.get_name());

        it->swap(argument);
      }
      else if(it->id()==ID_ellipsis)
        throw "ellipsis only allowed as last argument";
      else
        throw "unexpected argument: "+it->id_string();
    }
  }
  else if(type.id()==ID_array)
  {
    array_typet &array_type=to_array_type(type);

    c_storage_spect sub_storage_spec;

    convert_type(array_type.subtype(), sub_storage_spec);
    c_storage_spec|=sub_storage_spec;

    if(array_type.size().is_not_nil())
      convert_expr(array_type.size());
  }
  else if(type.id()==ID_bv)
  {
    exprt &size=static_cast<exprt &>(type.add(ID_size));
    convert_expr(size);
  }
  else if(type.id()==ID_struct ||
          type.id()==ID_union)
  {
    irept::subt &components=type.add(ID_components).get_sub();

    Forall_irep(it, components)
    {
      // the arguments are declarations or static assertions
      if(it->id()==ID_declaration)
      {
        ansi_c_declarationt &component=
          to_ansi_c_declaration(static_cast<exprt &>(*it));
  
        exprt new_component(ID_component);

        new_component.location()=component.location();
        new_component.set(ID_name, component.get_base_name());
        new_component.set(ID_pretty_name, component.get_base_name());
        new_component.type().swap(component.type());

        convert_type(new_component.type());

        it->swap(new_component);
      }
      else if(it->id()==ID_code && it->get(ID_statement)==ID_static_assert)
      {
        codet &assertion=static_cast<codet &>(*it);
        assert(assertion.operands().size()==2);
        convert_expr(assertion.op0());
        convert_expr(assertion.op1());
      }
      else
        assert(0);
    }
  }
  else if(type.id()==ID_typeof)
  {
    if(type.find(ID_operands).is_nil())
    {
      convert_type(static_cast<typet &>(type.add(ID_type_arg)));
    }
    else
    {
      exprt &expr=(exprt &)type;
      assert(expr.operands().size()==1);
      convert_expr(expr.op0());
    }
  }
  else if(type.id()==ID_c_enum ||
          type.id()==ID_incomplete_c_enum)
  {
    // add width
    type.set(ID_width, config.ansi_c.int_width);
  }
  else if(type.id()==ID_expression)
  {
    convert_expr((exprt &)(type.subtype()));
  }
  else if(type.id()==ID_vector)
  {
    vector_typet &vector_type=to_vector_type(type);
    convert_expr(vector_type.size());

    c_storage_spect sub_storage_spec;

    convert_type(vector_type.subtype(), sub_storage_spec);
    c_storage_spec|=sub_storage_spec;
  }
  
}

/*******************************************************************\

Function: ansi_c_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_convert(
  ansi_c_parse_treet &ansi_c_parse_tree,
  const std::string &module,
  message_handlert &message_handler)
{
  ansi_c_convertt ansi_c_convert(module, message_handler);

  try
  {
    ansi_c_convert.convert(ansi_c_parse_tree);
  }

  catch(int e)
  {
    ansi_c_convert.error();
    return true;
  }

  catch(const char *e)
  {
    ansi_c_convert.error(e);
    return true;
  }

  catch(const std::string &e)
  {
    ansi_c_convert.error(e);
    return true;
  }

  return false;
}

/*******************************************************************\

Function: ansi_c_convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_convert(
  exprt &expr,
  const std::string &module,
  message_handlert &message_handler)
{
  ansi_c_convertt ansi_c_convert(module, message_handler);

  try
  {
    ansi_c_convert.convert_expr(expr);
  }

  catch(int e)
  {
    ansi_c_convert.error();
  }

  catch(const char *e)
  {
    ansi_c_convert.error(e);
  }

  catch(const std::string &e)
  {
    ansi_c_convert.error(e);
  }

  return ansi_c_convert.get_error_found();
}
