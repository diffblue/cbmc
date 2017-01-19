/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/replace_expr.h>
#include <util/expr_util.h>
#include <util/source_location.h>
#include <util/std_expr.h>
#include <util/config.h>
#include <util/std_expr.h>
#include <util/type_eq.h>

#include <ansi-c/c_types.h>
#include <ansi-c/c_qualifiers.h>

#include "remove_skip.h"
#include "remove_function_pointers.h"
#include "compute_called_functions.h"

/*******************************************************************\

   Class: remove_function_pointerst

 Purpose:

\*******************************************************************/

class remove_function_pointerst
{
public:
  remove_function_pointerst(
    symbol_tablet &_symbol_table,
    bool _add_safety_assertion,
    const goto_functionst &goto_functions);

  void operator()(goto_functionst &goto_functions);

  bool remove_function_pointers(goto_programt &goto_program);

protected:
  const namespacet ns;
  symbol_tablet &symbol_table;
  bool add_safety_assertion;

  void remove_function_pointer(
    goto_programt &goto_program,
    goto_programt::targett target);

  std::set<irep_idt> address_taken;

  typedef std::map<irep_idt, code_typet> type_mapt;
  type_mapt type_map;

  bool is_type_compatible(
    bool return_value_used,
    const code_typet &call_type,
    const code_typet &function_type);

  bool arg_is_type_compatible(
    const typet &call_type,
    const typet &function_type);

  void fix_argument_types(code_function_callt &function_call);
  void fix_return_type(code_function_callt &function_call,
                       goto_programt &dest);

  symbolt &new_tmp_symbol();

  void compute_address_taken_in_symbols(
    std::set<irep_idt> &address_taken)
  {
    const symbol_tablet &symbol_table=ns.get_symbol_table();

    for(const auto &s : symbol_table.symbols)
      compute_address_taken_functions(s.second.value, address_taken);
  }

private:
  typedef std::list<exprt> functionst;

  bool try_get_precise_call(
    const exprt &expr, exprt &out_function);

  bool try_get_from_address_of(
    const exprt &expr, functionst &out_functions);

  bool try_get_call_from_symbol(
    const exprt &symbol_expr, functionst &out_functions);

  bool try_get_call_from_index(
    const exprt &index_expr, functionst &out_functions);

  bool try_evaluate_index_value(
    const exprt &index_value_expr, mp_integer &out_array_index);

  bool try_get_array_from_index(
    const index_exprt &index_expr, array_exprt &out_array_expr);

};

/*******************************************************************\

Function: remove_function_pointerst::remove_function_pointerst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

remove_function_pointerst::remove_function_pointerst(
  symbol_tablet &_symbol_table,
  bool _add_safety_assertion,
  const goto_functionst &goto_functions):
  ns(_symbol_table),
  symbol_table(_symbol_table),
  add_safety_assertion(_add_safety_assertion)
{
  compute_address_taken_in_symbols(address_taken);
  compute_address_taken_functions(goto_functions, address_taken);

  // build type map
  forall_goto_functions(f_it, goto_functions)
    type_map[f_it->first]=f_it->second.type;
}

/*******************************************************************\

Function: remove_function_pointerst::new_tmp_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &remove_function_pointerst::new_tmp_symbol()
{
  static int temporary_counter;

  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.base_name="tmp_return_val$"+std::to_string(++temporary_counter);
    new_symbol.name="remove_function_pointers::"+id2string(new_symbol.base_name);
  } while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
}

/*******************************************************************\

Function: remove_function_pointerst::try_get_precise_call

  Inputs:
   expr - The expression that is the value of the function pointer.

 Outputs: Returns true if the expression is a symbol and its value was code.
          In this case out_function will be the function this is a symbol for.

 Purpose: Find if a symbol is in fact a function that can be used in place
          of the function pointer

\*******************************************************************/

bool remove_function_pointerst::try_get_precise_call(
  const exprt &expr,
  exprt &out_function)
{
  if(expr.id()==ID_symbol && expr.type().id()==ID_code)
  {
    out_function=to_symbol_expr(expr);
    return true;
  }
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: remove_function_pointerst::try_get_from_address_of

  Inputs:
   expr - The expression that is the value of the function pointer.

 Outputs: Returns true if the expression is a address_of_exprt and it was able
          to either pointing to a function or a sybmol. In either of
          the true cases the out_functions will contain all the functions the
          address of could be.

 Purpose: Resolve a address of to its real value.

\*******************************************************************/

bool remove_function_pointerst::try_get_from_address_of(
  const exprt &expr, functionst &out_functions)
{
  if(expr.id()==ID_address_of)
  {
    const address_of_exprt &address_of_expr=to_address_of_expr(expr);

    exprt precise_expr;
    if(try_get_precise_call(address_of_expr.object(), precise_expr))
    {
      out_functions.push_back(precise_expr);
      return true;
    }
    else
    {
      return try_get_call_from_symbol(address_of_expr.object(), out_functions);
    }
  }
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: remove_function_pointerst::try_get_call_from_symbol

  Inputs:
   symbol_expr - The expression that is the value of the function pointer.

 Outputs: Returns true if the expression is a symbol_exprt and it was able
          to either find a explict function that this points to (in the case
          where the symbol is a function) or all a set of functions that it
          could be by following the valu the symbol represents. In either of
          the true cases the out_functions will contain all the functions the
          function pointer could point to.

 Purpose: Resolve a symbol to its real value and recursively try and find
          all posible functions that could be at that position in the array.

\*******************************************************************/

bool remove_function_pointerst::try_get_call_from_symbol(
  const exprt &symbol_expr, functionst &out_functions)
{
  if(symbol_expr.id()==ID_symbol)
  {
    const symbolt &symbol=
      symbol_table.lookup(symbol_expr.get(ID_identifier));
    const exprt &looked_up_val=symbol.value;
    exprt precise_expr;
    if(try_get_precise_call(looked_up_val, precise_expr))
    {
      out_functions.push_back(precise_expr);
      return true;
    }
    bool found_functions=false;
    found_functions=
      found_functions||try_get_from_address_of(looked_up_val, out_functions);
    found_functions=
      found_functions||try_get_call_from_index(looked_up_val, out_functions);
    found_functions=
      found_functions||try_get_call_from_symbol(looked_up_val, out_functions);
    return found_functions;
  }
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: remove_function_pointerst::try_get_call_from_index

  Inputs:
   expr - The expression that is the value of the function pointer.

 Outputs: Returns true if the expression is a index_exprt and it was able
          to either find a explict function that this points to (in the case
          where the index is constant) or all the functions within the array
          that the index is indexing. In either of the true cases the
          out_functions will contain all the functions the function pointer
          could point to.

 Purpose: Resolve the index of an array to find all posible functions
          that could be at that position in the array.

\*******************************************************************/

bool remove_function_pointerst::try_get_call_from_index(
  const exprt &expr, functionst &out_functions)
{
  if(expr.id()==ID_index)
  {
    const index_exprt &index_expr=to_index_expr(expr);

    array_exprt array_expr;
    if(try_get_array_from_index(index_expr, array_expr))
    {
      // Here we require an array of constant pointers to
      // code (i.e. the pointers cannot be reassigned).
      // Since it is an array
      const typet &array_type=array_expr.type();
      const typet &array_contents_type=array_type.subtype();
      c_qualifierst array_qaulifiers;
      array_qaulifiers.read(array_contents_type);
      if(array_qaulifiers.is_constant)
      {
        mp_integer value;
        if(try_evaluate_index_value(index_expr.index(), value))
        {
          const exprt &func_expr=array_expr.operands()[integer2size_t(value)];
          exprt precise_match;

          if(try_get_precise_call(func_expr, precise_match))
          {
            out_functions.push_back(precise_match);
            return true;
          }
          bool found_functions=false;
          found_functions=
            found_functions||try_get_from_address_of(func_expr, out_functions);
          found_functions=
            found_functions||try_get_call_from_symbol(func_expr, out_functions);

          return found_functions;
        }
        else
        {
          // We don't know what index it is,
          // but we know the value is from the array
          for(const exprt &op : array_expr.operands())
          {
            exprt precise_match;
            if(try_get_precise_call(op, precise_match))
            {
              out_functions.push_back(precise_match);
            }
            bool found_functions=false;
            found_functions=
              found_functions||try_get_from_address_of(op, out_functions);
            found_functions=
              found_functions||try_get_call_from_symbol(op, out_functions);
          }
          return out_functions.size() > 0;
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
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: remove_function_pointerst::try_evaluate_index_value

  Inputs:
   index_expr - The expression of the index of the index expression (e.g.
                index_exprt::index())

 Outputs: Returns true if was able to find a constant value for the index
          expression. If true, then out_array_index will be the index within
          the array that the function pointer is pointing to.

 Purpose: Given an index into an array, resolve, if possible, the index
          that is being accessed. This deals with symbols and typecasts to
          constant values.

\*******************************************************************/

bool remove_function_pointerst::try_evaluate_index_value(
  const exprt &index_value_expr, mp_integer &out_array_index)
{
  if(index_value_expr.id()==ID_constant)
  {
    const constant_exprt &constant_expr=to_constant_expr(index_value_expr);
    mp_integer array_index;
    bool errors=to_integer(constant_expr, array_index);
    if(!errors)
    {
      out_array_index=array_index;
    }
    return !errors;
  }
  else if(index_value_expr.id()==ID_symbol)
  {
    // Resolve symbol and try again
    const symbolt &index_symbol=
      symbol_table.lookup(index_value_expr.get(ID_identifier));

    return try_evaluate_index_value(index_symbol.value, out_array_index);
  }
  else if(index_value_expr.id()==ID_typecast)
  {
    // Follow the typecast
    return try_evaluate_index_value(index_value_expr.op0(), out_array_index);
  }
  else
  {
    return false;
  }
}

/*******************************************************************\

Function: remove_function_pointerst::try_get_array_from_index

  Inputs:
   index_expr - The expression of the index in the array

 Outputs: Returns true if was able to find the array associated
          with the index. If true, then out_array_expr will contain
          the expression representing the array.

 Purpose: Given an index into an array, resolve the array expression,
          following symbol expressions through to the actual array
          expression.

\*******************************************************************/

bool remove_function_pointerst::try_get_array_from_index(
  const index_exprt &index_expr, array_exprt &out_array_expr)
{
  const exprt &array_expr=index_expr.array();
  if(array_expr.id()==ID_array)
  {
    out_array_expr=to_array_expr(array_expr);
    return true;
  }
  else if(array_expr.id()==ID_symbol)
  {
    // Is there some existing code to follow symbols to the real value?
    const symbolt &array_symbol=
      symbol_table.lookup(array_expr.get(ID_identifier));

    const exprt &array_value=array_symbol.value;
    if(array_value.id()==ID_array)
    {
      out_array_expr=to_array_expr(array_value);
      return true;
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

/*******************************************************************\

Function: remove_function_pointerst::arg_is_type_compatible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool remove_function_pointerst::arg_is_type_compatible(
  const typet &call_type,
  const typet &function_type)
{
  if(type_eq(call_type, function_type, ns)) return true;

  // any integer-vs-enum-vs-pointer is ok
  if(call_type.id()==ID_signedbv ||
     call_type.id()==ID_unsigned ||
     call_type.id()==ID_bool ||
     call_type.id()==ID_pointer ||
     call_type.id()==ID_c_enum ||
     call_type.id()==ID_c_enum_tag)
  {
    if(function_type.id()==ID_signedbv ||
       function_type.id()==ID_unsigned ||
       function_type.id()==ID_bool ||
       function_type.id()==ID_pointer ||
       function_type.id()==ID_c_enum ||
       function_type.id()==ID_c_enum_tag)
      return true;

    return false;
  }

  // structs/unions need to match,
  // which could be made more generous

  return false;
}

/*******************************************************************\

Function: remove_function_pointerst::is_type_compatible

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool remove_function_pointerst::is_type_compatible(
  bool return_value_used,
  const code_typet &call_type,
  const code_typet &function_type)
{
  // we are willing to ignore anything that's returned
  // if we call with 'void'
  if(!return_value_used)
  {
  }
  else if(type_eq(call_type.return_type(), empty_typet(), ns))
  {
    // ok
  }
  else
  {
    if(!arg_is_type_compatible(call_type.return_type(),
                               function_type.return_type()))
      return false;
  }

  // let's look at the parameters
  const code_typet::parameterst &call_parameters=call_type.parameters();
  const code_typet::parameterst &function_parameters=function_type.parameters();

  if(function_type.has_ellipsis() &&
     function_parameters.empty())
  {
    // always ok
  }
  else if(call_type.has_ellipsis() &&
          call_parameters.empty())
  {
    // always ok
  }
  else
  {
    // we are quite strict here, could be much more generous
    if(call_parameters.size()!=function_parameters.size())
      return false;

    for(unsigned i=0; i<call_parameters.size(); i++)
      if(!arg_is_type_compatible(call_parameters[i].type(),
                                 function_parameters[i].type()))
        return false;
  }

  return true;
}

/*******************************************************************\

Function: remove_function_pointerst::fix_argument_types

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_function_pointerst::fix_argument_types(
  code_function_callt &function_call)
{
  const code_typet &code_type=
    to_code_type(ns.follow(function_call.function().type()));

  const code_typet::parameterst &function_parameters=
    code_type.parameters();

  code_function_callt::argumentst &call_arguments=
    function_call.arguments();

  for(unsigned i=0; i<function_parameters.size(); i++)
  {
    if(i<call_arguments.size())
    {
      if(!type_eq(call_arguments[i].type(),
                  function_parameters[i].type(), ns))
      {
        call_arguments[i].make_typecast(function_parameters[i].type());
      }
    }
  }
}

/*******************************************************************\

Function: remove_function_pointerst::fix_return_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_function_pointerst::fix_return_type(
  code_function_callt &function_call,
  goto_programt &dest)
{
  // are we returning anything at all?
  if(function_call.lhs().is_nil()) return;

  const code_typet &code_type=
    to_code_type(ns.follow(function_call.function().type()));

  // type already ok?
  if(type_eq(
       function_call.lhs().type(),
       code_type.return_type(), ns))
    return;

  symbolt &tmp_symbol=new_tmp_symbol();
  tmp_symbol.type=code_type.return_type();
  tmp_symbol.location=function_call.source_location();

  symbol_exprt tmp_symbol_expr;
  tmp_symbol_expr.type()=tmp_symbol.type;
  tmp_symbol_expr.set_identifier(tmp_symbol.name);

  exprt old_lhs=function_call.lhs();
  function_call.lhs()=tmp_symbol_expr;

  goto_programt::targett t_assign=dest.add_instruction();
  t_assign->make_assignment();
  t_assign->code=code_assignt(
    old_lhs, typecast_exprt(tmp_symbol_expr, old_lhs.type()));
}

/*******************************************************************\

Function: remove_function_pointerst::remove_function_pointer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_function_pointerst::remove_function_pointer(
  goto_programt &goto_program,
  goto_programt::targett target)
{
  const code_function_callt &code=
    to_code_function_call(target->code);

  const exprt &function=code.function();

  // this better have the right type
  code_typet call_type=to_code_type(function.type());

  // refine the type in case the forward declaration was incomplete
  if(call_type.has_ellipsis() &&
     call_type.parameters().empty())
  {
    call_type.remove_ellipsis();
    forall_expr(it, code.arguments())
      call_type.parameters().push_back(
        code_typet::parametert(it->type()));
  }

  assert(function.id()==ID_dereference);
  assert(function.operands().size()==1);

  const exprt &pointer=function.op0();

  exprt precise_call;
  functionst functions;
  bool found_functions=false;
  if(try_get_precise_call(pointer, precise_call))
  {
    to_code_function_call(target->code).function()=precise_call;
    return;
  }
  found_functions=found_functions||try_get_from_address_of(pointer, functions);
  found_functions=found_functions||try_get_call_from_symbol(pointer, functions);
  found_functions=found_functions||try_get_call_from_index(pointer, functions);

  if(functions.size()==1)
  {
    to_code_function_call(target->code).function()=functions.front();
    return;
  }

  // if the functions list is still empty we didn't have any luck finding
  // any valid funcitons (or there are none??)
  if(!found_functions)
  {
    bool return_value_used=code.lhs().is_not_nil();

    // get all type-compatible functions
    // whose address is ever taken
    for(const auto &t : type_map)
    {
      // address taken?
      if(address_taken.find(t.first)==address_taken.end())
        continue;

      // type-compatible?
      if(!is_type_compatible(return_value_used, call_type, t.second))
        continue;

      if(t.first=="pthread_mutex_cleanup")
        continue;

      symbol_exprt expr;
      expr.type()=t.second;
      expr.set_identifier(t.first);
      functions.push_back(expr);
    }
  }
  else
  {
    assert(functions.size()>0);
  }

  // the final target is a skip
  goto_programt final_skip;

  goto_programt::targett t_final=final_skip.add_instruction();
  t_final->make_skip();

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  for(const auto &fun : functions)
  {
    // call function
    goto_programt::targett t1=new_code_calls.add_instruction();
    t1->make_function_call(code);
    to_code_function_call(t1->code).function()=fun;

    // the signature of the function might not match precisely
    fix_argument_types(to_code_function_call(t1->code));

    fix_return_type(to_code_function_call(t1->code), new_code_calls);
    // goto final
    goto_programt::targett t3=new_code_calls.add_instruction();
    t3->make_goto(t_final, true_exprt());

    // goto to call
    address_of_exprt address_of;
    address_of.object()=fun;
    address_of.type()=pointer_typet();
    address_of.type().subtype()=fun.type();

    if(address_of.type()!=pointer.type())
      address_of.make_typecast(pointer.type());

    goto_programt::targett t4=new_code_gotos.add_instruction();
    t4->make_goto(t1, equal_exprt(pointer, address_of));
  }

  // fall-through
  if(add_safety_assertion)
  {
    goto_programt::targett t=new_code_gotos.add_instruction();
    t->make_assertion(false_exprt());
    t->source_location.set_property_class("pointer dereference");
    t->source_location.set_comment("invalid function pointer");
  }

  goto_programt new_code;

  // patch them all together
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);

  // set locations
  Forall_goto_program_instructions(it, new_code)
  {
    irep_idt property_class=it->source_location.get_property_class();
    irep_idt comment=it->source_location.get_comment();
    it->source_location=target->source_location;
    it->function=target->function;
    if(!property_class.empty()) it->source_location.set_property_class(property_class);
    if(!comment.empty()) it->source_location.set_comment(comment);
  }

  goto_programt::targett next_target=target;
  next_target++;

  goto_program.destructive_insert(next_target, new_code);

  // We preserve the original dereferencing to possibly catch
  // further pointer-related errors.
  code_expressiont code_expression;
  code_expression.add_source_location()=function.source_location();
  code_expression.expression()=function;
  target->code.swap(code_expression);
  target->type=OTHER;
}

/*******************************************************************\

Function: remove_function_pointerst::remove_function_pointers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool remove_function_pointerst::remove_function_pointers(
  goto_programt &goto_program)
{
  bool did_something=false;

  Forall_goto_program_instructions(target, goto_program)
    if(target->is_function_call())
    {
      const code_function_callt &code=
        to_code_function_call(target->code);

      if(code.function().id()==ID_dereference)
      {
        remove_function_pointer(goto_program, target);
        did_something=true;
      }
    }

  if(did_something)
  {
    remove_skip(goto_program);
    goto_program.update();
  }

  return did_something;
}

/*******************************************************************\

Function: remove_function_pointerst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_function_pointerst::operator()(goto_functionst &functions)
{
  bool did_something=false;

  for(goto_functionst::function_mapt::iterator f_it=
      functions.function_map.begin();
      f_it!=functions.function_map.end();
      f_it++)
  {
    goto_programt &goto_program=f_it->second.body;

    if(remove_function_pointers(goto_program))
      did_something=true;
  }

  if(did_something)
    functions.compute_location_numbers();
}

/*******************************************************************\

Function: remove_function_pointers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool remove_function_pointers(
  symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  goto_programt &goto_program,
  bool add_safety_assertion)
{
  remove_function_pointerst
    rfp(symbol_table, add_safety_assertion, goto_functions);

  return rfp.remove_function_pointers(goto_program);
}

/*******************************************************************\

Function: remove_function_pointers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_function_pointers(
  symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  bool add_safety_assertion)
{
  remove_function_pointerst
    rfp(symbol_table, add_safety_assertion, goto_functions);

  rfp(goto_functions);
}

/*******************************************************************\

Function: remove_function_pointers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void remove_function_pointers(
  goto_modelt &goto_model,
  bool add_safety_assertion)
{
  remove_function_pointers(
    goto_model.symbol_table, goto_model.goto_functions,
    add_safety_assertion);
}
