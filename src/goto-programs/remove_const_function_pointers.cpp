/*******************************************************************\

Module: Goto Programs

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#include <ansi-c/c_qualifiers.h>
#include <util/simplify_expr.h>
#include <util/arith_tools.h>

#include "remove_const_function_pointers.h"

remove_const_function_pointerst::remove_const_function_pointerst(
  message_handlert &message_handler,
  const exprt &base_expression,
  const namespacet &ns,
  const symbol_tablet &symbol_table):
    messaget(message_handler),
    original_expression(base_expression),
    ns(ns),
    symbol_table(symbol_table)
{}

bool remove_const_function_pointerst::operator()(
  functionst &out_functions)
{
  // Replace all const symbols with their values
  exprt non_symbol_expression=replace_const_symbols(original_expression);
  return try_resolve_function_call(non_symbol_expression, out_functions);
}

/*******************************************************************\

Function: remove_const_function_pointerst::replace_const_symbols

  Inputs:
   expression - The expression to resolve symbols in

 Outputs: Returns a modified version of the expression, with all
          const symbols resolved to their actual values.

 Purpose: To collapse the symbols down to their values where possible
          This takes a very general approach, recreating the expr tree
          exactly as it was and ignoring what type of expressions are found
          and instead recurses over all the operands.

\*******************************************************************/

exprt remove_const_function_pointerst::replace_const_symbols(
  const exprt &expression) const
{
  if(expression.id()==ID_symbol)
  {
    if(is_expression_const(expression))
    {
      const symbolt &symbol=
        symbol_table.lookup(expression.get(ID_identifier));
      if(symbol.type.id()!=ID_code)
      {
        const exprt &symbol_value=symbol.value;
        return replace_const_symbols(symbol_value);
      }
      else
      {
        return expression;
      }
    }
    else
    {
      return expression;
    }
  }
  else
  {
    exprt const_symbol_cleared_expr=expression;
    const_symbol_cleared_expr.operands().clear();
    for(const exprt &op : expression.operands())
    {
      exprt const_symbol_cleared_op=replace_const_symbols(op);
      const_symbol_cleared_expr.operands().push_back(const_symbol_cleared_op);
    }

    return const_symbol_cleared_expr;
  }
}

exprt remove_const_function_pointerst::resolve_symbol(
  const symbol_exprt &symbol_expr) const
{
  const symbolt &symbol=
    symbol_table.lookup(symbol_expr.get_identifier());
  return symbol.value;
}

bool remove_const_function_pointerst::try_resolve_function_call(
  const exprt &expr, remove_const_function_pointerst::functionst &out_functions)
{
  const exprt &simplified_expr=simplify_expr(expr, ns);
  if(simplified_expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(simplified_expr);
    return try_resolve_index_of_function_call(index_expr, out_functions);
  }
  else if(simplified_expr.id()==ID_member)
  {
    const member_exprt &member_expr=to_member_expr(simplified_expr);
    const exprt &owner_expr=member_expr.compound();
    // Squash the struct
    expressionst out_expressions;
    bool struct_is_const=false;
    bool resolved=
      try_resolve_expression(owner_expr, out_expressions, struct_is_const);
    if(resolved)
    {
      for(const exprt &expression:out_expressions)
      {
        if(expression.id()!=ID_struct)
        {
          return false;
        }
        else
        {
          const struct_exprt &struct_expr=to_struct_expr(expression);
          const exprt &component_value=
            get_component_value(struct_expr, member_expr);

          const typet &component_type=
            get_component_type(struct_expr, member_expr);
          bool component_const=is_type_const(component_type);

          if(component_const || struct_is_const)
          {
            functionst component_functions;
            bool resolved=
              try_resolve_function_call(component_value, component_functions);
            if(resolved)
            {
              out_functions.insert(
                component_functions.begin(), component_functions.end());
            }
            else
            {
              return false;
            }
          }
          else
          {
            return false;
          }
        }
      }

      return true;

    }
    else
    {
      return false;
    }
  }
  else if(simplified_expr.id()==ID_address_of)
  {
    address_of_exprt address_expr=to_address_of_expr(simplified_expr);
    return try_resolve_function_call(address_expr.object(), out_functions);
  }
  else if(simplified_expr.id()==ID_dereference)
  {
    // We had a pointer, we need to check both the pointer
    // type can't be changed, and what it what pointing to
    // can't be changed
    const dereference_exprt &deref=to_dereference_expr(simplified_expr);
    expressionst pointer_values;
    bool pointer_const;
    bool resolved=
      try_resolve_expression(deref.pointer(), pointer_values, pointer_const);

    // Here we require that the value we are dereferencing is const
    // The actual type doesn't matter since we are on the RHS so what matters
    // is where this gets stored, but the value stored matters
    if(resolved && pointer_const)
    {
      for(const exprt &pointer_val : pointer_values)
      {
        if(pointer_val.id()==ID_address_of)
        {
          address_of_exprt address_expr=to_address_of_expr(pointer_val);
          functionst out_object_values;
          bool resolved=
            try_resolve_function_call(
              address_expr.object(), out_object_values);

          if(resolved)
          {
            out_functions.insert(
              out_object_values.begin(),
              out_object_values.end());
          }
          else
          {
            return false;
          }
        }
        else
        {
          return false;
        }
      }
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(simplified_expr.id()==ID_typecast)
  {
    // We simply ignore typecasts and assume they are valid
    // I thought simplify_expr would deal with this, but for example
    // a cast from a 32 bit width int to a 64bit width int it doesn't seem
    // to allow
    typecast_exprt typecast_expr=to_typecast_expr(simplified_expr);
    functionst typecast_values;
    bool resolved=
      try_resolve_function_call(typecast_expr.op(), typecast_values);

    if(resolved)
    {
      out_functions.insert(typecast_values.begin(), typecast_values.end());
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(simplified_expr.id()==ID_symbol)
  {
    if(simplified_expr.type().id()==ID_code)
    {
      out_functions.insert(simplified_expr);
      return true;
    }
    else
    {
      const c_qualifierst pointer_qualifers(simplified_expr.type());
      if(!pointer_qualifers.is_constant)
      {
        debug() << "Can't optimize FP since symbol "
                << simplified_expr.get(ID_identifier) << " is not const" << eom;
        return false;
      }

      const exprt &symbol_value=resolve_symbol(to_symbol_expr(simplified_expr));
      return try_resolve_function_call(symbol_value, out_functions);
    }
  }
  else
  {
    return false;
  }
}

// Take an index of, squash its array and squash its index
// If we can get a precise number, try_resolve_function_call on its value
// otherwise try_resolve_function_call on each and return the union of them all
bool remove_const_function_pointerst::try_resolve_index_of_function_call(
  const index_exprt &index_expr, functionst &out_functions)
{
  // Get the array(s) it belongs to
  expressionst potential_array_exprs;
  bool is_const=false;
  bool resolved_array=
    try_resolve_expression(index_expr.array(), potential_array_exprs, is_const);
  if(resolved_array)
  {
    for(const exprt &potential_array_expr : potential_array_exprs)
    {
      if(potential_array_expr.id()==ID_array)
      {
        // We require either the type of the values of the array or
        // the array itself to be constant.
        const typet &array_type=potential_array_expr.type();
        const typet &array_contents_type=array_type.subtype();
        c_qualifierst array_qaulifiers;
        array_qaulifiers.read(array_contents_type);

        if(array_qaulifiers.is_constant || is_const)
        {
          // Get the index if we can
          mp_integer value;
          if(try_resolve_index_value(index_expr.index(), value))
          {
            functionst array_out_functions;
            const exprt &func_expr=
              potential_array_expr.operands()[integer2size_t(value)];
            bool resolved_value=
              try_resolve_function_call(func_expr, array_out_functions);

            if(resolved_value)
            {
              out_functions.insert(
                array_out_functions.begin(),
                array_out_functions.end());
            }
            else
            {
              return false;
            }
          }
          else
          {
            // We don't know what index it is,
            // but we know the value is from the array
            for(const exprt &array_entry : potential_array_expr.operands())
            {
              if(array_entry.is_zero())
              {
                continue;
              }
              functionst potential_functions;
              bool resolved_value=
                try_resolve_function_call(array_entry, potential_functions);

              if(resolved_value)
              {
                out_functions.insert(
                  potential_functions.begin(), potential_functions.end());
              }
              else
              {
                return false;
              }
            }
          }
        }
        else
        {
          return false;
        }
      }
      else
      {
        return false;
      }
    }

    return true;
  }
  else
  {
    return false;
  }
}

bool remove_const_function_pointerst::try_resolve_expression(
  const exprt &expr, expressionst &out_resolved_expression, bool &out_is_const)
{
  const exprt &simplified_expr=simplify_expr(expr, ns);
  if(simplified_expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(simplified_expr);
    expressionst out_array_expressions;
    bool resolved_array=
      try_resolve_index_of(index_expr, out_array_expressions, out_is_const);
    if(resolved_array)
    {
      out_resolved_expression.insert(
        out_resolved_expression.end(),
        out_array_expressions.begin(),
        out_array_expressions.end());
    }

    return resolved_array;
  }
  else if(simplified_expr.id()==ID_member)
  {
    // Get the component it belongs to
    const member_exprt &member_expr=to_member_expr(simplified_expr);

    expressionst potential_structs;
    bool is_struct_const;
    bool resolved_struct=
      try_resolve_expression(
        member_expr.compound(), potential_structs, is_struct_const);

    if(resolved_struct)
    {
      bool all_components_const=true;
      for(const exprt &potential_struct : potential_structs)
      {
        if(potential_struct.id()==ID_struct)
        {
          struct_exprt struct_expr=to_struct_expr(potential_struct);
          const exprt &component_value=
            get_component_value(struct_expr, member_expr);
          const typet &component_type=
            get_component_type(struct_expr, member_expr);

          all_components_const&=is_type_const(component_type);

          expressionst out_expressions;
          bool component_const=false;
          bool resolved=
            try_resolve_expression(
              component_value, out_expressions, component_const);
          if(resolved)
          {
            out_resolved_expression.insert(
              out_resolved_expression.end(),
              out_expressions.begin(),
              out_expressions.end());
          }
          else
          {
            return false;
          }
        }
        else
        {
          return false;
        }
      }
      out_is_const=all_components_const||is_struct_const;
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(simplified_expr.id()==ID_dereference)
  {
    // We had a pointer, we need to check both the pointer
    // type can't be changed, and what it what pointing to
    // can't be changed
    const dereference_exprt &deref=to_dereference_expr(simplified_expr);
    expressionst pointer_values;
    bool pointer_const;
    bool resolved=
      try_resolve_expression(deref.pointer(), pointer_values, pointer_const);
    if(resolved && pointer_const)
    {
      bool all_objects_const=true;
      for(const exprt &pointer_val : pointer_values)
      {
        if(pointer_val.id()==ID_address_of)
        {
          address_of_exprt address_expr=to_address_of_expr(pointer_val);
          bool object_const=false;
          expressionst out_object_values;
          bool resolved=
            try_resolve_expression(
              address_expr.object(), out_object_values, object_const);

          if(resolved)
          {
            out_resolved_expression.insert(
              out_resolved_expression.end(),
              out_object_values.begin(),
              out_object_values.end());

            all_objects_const&=object_const;
          }
        }
        else
        {
          return false;
        }
      }
      out_is_const=all_objects_const;
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(simplified_expr.id()==ID_typecast)
  {
    // We simply ignore typecasts and assume they are valid
    // I thought simplify_expr would deal with this, but for example
    // a cast from a 32 bit width int to a 64bit width int it doesn't seem
    // to allow
    typecast_exprt typecast_expr=to_typecast_expr(simplified_expr);
    expressionst typecast_values;
    bool typecast_const;
    bool resolved=
      try_resolve_expression(
        typecast_expr.op(), typecast_values, typecast_const);

    if(resolved)
    {
      out_resolved_expression.insert(
        out_resolved_expression.end(),
        typecast_values.begin(),
        typecast_values.end());
      out_is_const=typecast_const;
      return true;
    }
    else
    {
      return false;
    }
  }
  else if(simplified_expr.id()==ID_symbol)
  {
    const exprt &symbol_value=resolve_symbol(to_symbol_expr(simplified_expr));
    bool is_symbol_const=is_expression_const(simplified_expr);
    bool is_symbol_value_const=false;
    bool resolved_expression=
      try_resolve_expression(
        symbol_value,
        out_resolved_expression,
        is_symbol_value_const);

    // If we have a symbol, it is only const if the value it is assigned
    // is const and it is in fact const.
    out_is_const=is_symbol_const;
    return resolved_expression;
  }
  // TOOD: probably need to do something with pointers or address_of
  // and const since a const pointer to a non-const value is useless
  else
  {
    out_is_const=is_expression_const(simplified_expr);
    out_resolved_expression.push_back(simplified_expr);
    return true;
  }
}

bool remove_const_function_pointerst::try_resolve_index_value(
  const exprt &expr, mp_integer &out_array_index)
{
  expressionst index_value_expressions;
  bool is_const=false;
  bool resolved=try_resolve_expression(expr, index_value_expressions, is_const);
  if(resolved)
  {
    if(index_value_expressions.size()==1 &&
       index_value_expressions.front().id()==ID_constant)
    {
      const constant_exprt &constant_expr=
        to_constant_expr(index_value_expressions.front());
      mp_integer array_index;
      bool errors=to_integer(constant_expr, array_index);
      if(!errors)
      {
        out_array_index=array_index;
      }
      return !errors;
    }
    else
    {
      return false;
    }
  }
  else
  {
    return false;
  }
}


// Takes an index of, squashes its array and index
// if index is resolvable
bool remove_const_function_pointerst::try_resolve_index_of(
  const index_exprt &index_expr,
  expressionst &out_expressions,
  bool &out_is_const)
{
  // Get the array(s) it belongs to
  expressionst potential_array_exprs;
  bool array_const=false;
  bool resolved_array=
    try_resolve_expression(
      index_expr.array(),
      potential_array_exprs,
      array_const);

  if(resolved_array)
  {
    bool all_possible_const=true;
    for(const exprt &potential_array_expr : potential_array_exprs)
    {
      all_possible_const=
        all_possible_const &&
        is_type_const(potential_array_expr.type().subtype());

      if(potential_array_expr.id()==ID_array)
      {
        // Get the index if we can
        mp_integer value;
        if(try_resolve_index_value(index_expr.index(), value))
        {
          expressionst array_out_functions;
          const exprt &func_expr=
            potential_array_expr.operands()[integer2size_t(value)];
          bool value_const=false;
          bool resolved_value=
            try_resolve_expression(func_expr, array_out_functions, value_const);

          if(resolved_value)
          {
            out_expressions.insert(
              out_expressions.end(),
              array_out_functions.begin(),
              array_out_functions.end());
          }
          else
          {
            return false;
          }
        }
        else
        {
          // We don't know what index it is,
          // but we know the value is from the array
          for(const exprt &array_entry : potential_array_expr.operands())
          {
            expressionst array_contents;
            bool is_entry_const;
            bool resolved_value=
              try_resolve_expression(
                array_entry, array_contents, is_entry_const);

            if(resolved_value)
            {
              for(const exprt &resolved_array_entry : array_contents)
              {
                if(resolved_array_entry .is_zero())
                {
                  continue;
                }
                else
                {
                  out_expressions.push_back(resolved_array_entry);
                }
              }
            }
            else
            {
              return false;
            }
          }
        }
      }
      else
      {
        return false;
      }
    }

    out_is_const=all_possible_const || array_const;
    return true;
  }
  else
  {
    return false;
  }
}

bool remove_const_function_pointerst::is_expression_const(
  const exprt &expression) const
{
  return is_type_const(expression.type());
}

bool remove_const_function_pointerst::is_type_const(const typet &type) const
{
  c_qualifierst qualifers(type);
  if(type.id()==ID_array)
  {
    c_qualifierst array_type_qualifers(type.subtype());
    return qualifers.is_constant || array_type_qualifers.is_constant;
  }
  else
  {
    return qualifers.is_constant;
  }
}

/*******************************************************************\

Function: remove_const_function_pointerst::get_component_value

  Inputs:
   struct_expr - The expression of the structure being accessed
   member_expr - The expression saying which component is being accessed

 Outputs: Returns the value of a specific component for a given struct
          expression.

 Purpose: To extract the value of the specific component within a struct

\*******************************************************************/

exprt remove_const_function_pointerst::get_component_value(
  const struct_exprt &struct_expr, const member_exprt &member_expr)
{
  const struct_typet &struct_type=to_struct_type(ns.follow(struct_expr.type()));
  size_t component_number=
    struct_type.component_number(member_expr.get_component_name());

  return struct_expr.operands()[component_number];
}

/*******************************************************************\

Function: remove_const_function_pointerst::get_component_type

  Inputs:
   struct_expr - The expression of the structure being accessed
   member_expr - The expression saying which component is being accessed

 Outputs: Returns the type of the component. Note this may be differenent to
          the type of its value (e.g. it may be a const pointer but its value
          could just be a pointer).

 Purpose: To extract the type of the specific component within a struct

\*******************************************************************/

typet remove_const_function_pointerst::get_component_type(
  const struct_exprt &struct_expr, const member_exprt &member_expr)
{
  const struct_typet &struct_type=to_struct_type(ns.follow(struct_expr.type()));
  size_t component_number=
    struct_type.component_number(member_expr.get_component_name());
  struct_union_typet::componentt component=
    struct_type.components()[component_number];

  return component.type();
}
