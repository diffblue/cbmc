/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <replace_expr.h>
#include <expr_util.h>
#include <location.h>
#include <std_expr.h>
#include <config.h>
#include <std_expr.h>
#include <type_eq.h>

#include <ansi-c/c_types.h>

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
  explicit remove_function_pointerst(const namespacet &_ns):ns(_ns)
  {
  }

  void operator()(goto_functionst &functions);

protected:
  const namespacet &ns;

  void remove_function_pointer(
    goto_programt &goto_program,
    goto_programt::targett target);

  bool remove_function_pointers(goto_programt &goto_program);

  std::set<irep_idt> address_taken;
  
  typedef std::map<irep_idt, code_typet> type_mapt;
  type_mapt type_map;

  bool is_type_compatible(
    const code_typet &call_type,
    const code_typet &function_type);

  bool arg_is_type_compatible(
    const typet &call_type,
    const typet &function_type);
};

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
     call_type.id()==ID_c_enum)
  {
    if(function_type.id()==ID_signedbv ||
       function_type.id()==ID_unsigned ||
       function_type.id()==ID_bool ||
       function_type.id()==ID_pointer ||
       function_type.id()==ID_c_enum)
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
  const code_typet &call_type,
  const code_typet &function_type)
{
  // we are willing to ignore anything that's returned
  // if we call with 'void'
  if(type_eq(call_type.return_type(), empty_typet(), ns))
  {
    // ok
  }
  else
  {
    if(!arg_is_type_compatible(call_type.return_type(),
                               function_type.return_type()))
      return false;
  }

  // let's look at the arguments
  const code_typet::argumentst &call_arguments=call_type.arguments();
  const code_typet::argumentst &function_arguments=function_type.arguments();

  if(function_type.has_ellipsis() &&
     function_arguments.empty())
  {
    // always ok
  }
  else
  {
    // we are quite strict here, could be much more generous
    if(call_arguments.size()!=function_arguments.size())
      return false;
    
    for(unsigned i=0; i<call_arguments.size(); i++)
      if(!arg_is_type_compatible(call_arguments[i].type(),
                                 function_arguments[i].type()))
        return false;
  }
  
  return true;
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
  const code_typet &call_type=to_code_type(function.type());
  
  assert(function.id()==ID_dereference);
  assert(function.operands().size()==1);

  const exprt &pointer=function.op0();
  
  typedef std::list<exprt> functionst;
  functionst functions;
  
  // get all type-compatible functions
  // whose address is ever taken
  for(type_mapt::const_iterator f_it=
      type_map.begin();
      f_it!=type_map.end();
      f_it++)
  {
    // address taken?
    if(address_taken.find(f_it->first)==address_taken.end())
      continue;

    // type-compatible?
    if(!is_type_compatible(call_type, f_it->second))
      continue;
    
    symbol_exprt expr;
    expr.type()=f_it->second;
    expr.set_identifier(f_it->first);
    functions.push_back(expr);
  }
  
  // the final target is a skip
  
  goto_programt final_skip;
  goto_programt::targett t_final=final_skip.add_instruction();
  t_final->make_skip();

  // build the calls and gotos

  goto_programt new_code_calls;
  goto_programt new_code_gotos;

  for(functionst::const_iterator
      it=functions.begin();
      it!=functions.end();
      it++)
  {
    // call
    goto_programt::targett t1=new_code_calls.add_instruction();
    t1->make_function_call(code);
    to_code_function_call(t1->code).function()=*it;
    goto_programt::targett t2=new_code_calls.add_instruction();
    t2->make_goto(t_final, true_exprt());
  
    // goto
    address_of_exprt address_of;
    address_of.object()=*it;
    address_of.type()=pointer_typet();
    address_of.type().subtype()=it->type();
    
    if(address_of.type()!=pointer.type())
      address_of.make_typecast(pointer.type());
    
    goto_programt::targett t3=new_code_gotos.add_instruction();
    t3->make_goto(t1, equal_exprt(pointer, address_of));
  }

  goto_programt new_code;
  
  // patch them all together
  new_code.destructive_append(new_code_gotos);
  new_code.destructive_append(new_code_calls);
  new_code.destructive_append(final_skip);
  
  // set locations
  Forall_goto_program_instructions(it, new_code)
    it->location=target->location;
  
  goto_programt::targett next_target=target;
  next_target++;

  goto_program.instructions.splice(next_target, new_code.instructions);

  // we preserve the dereferencing to possibly catch
  // pointer-related errors
  code_expressiont code_expression;
  code_expression.location()=function.location();
  code_expression.expression()=function;
  target->code.swap(code_expression);
  target->type=OTHER;
}

/*******************************************************************\

Function: remove_function_pointerst::operator()

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
  
  compute_address_taken_functions(functions, address_taken);

  // build type map
  for(goto_functionst::function_mapt::iterator f_it=
      functions.function_map.begin();
      f_it!=functions.function_map.end();
      f_it++)
    type_map[f_it->first]=f_it->second.type;
  
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

void remove_function_pointers(
  const namespacet &ns,
  goto_functionst &functions,
  bool add_safety_assertion)
{
  remove_function_pointerst rfp(ns);
  rfp(functions);
}
