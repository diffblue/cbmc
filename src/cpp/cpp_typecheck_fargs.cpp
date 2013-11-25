/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <cassert>

#include <util/std_types.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_typecheck_fargs.h"
#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheck_fargst::has_class_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_typecheck_fargst::has_class_type() const
{
  for(exprt::operandst::const_iterator it=operands.begin();
      it!=operands.end();
      it++)
  {
    if(it->type().id()==ID_struct)
      return true;
  }

  return false;
}

/*******************************************************************\

Function: cpp_typecheck_fargst::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheck_fargst::build(
  const side_effect_expr_function_callt &function_call)
{
  in_use=true;

  operands.clear();
  operands.reserve(function_call.op1().operands().size());

  for(unsigned i=0; i<function_call.op1().operands().size(); i++)
    operands.push_back(function_call.op1().operands()[i]);
}

/*******************************************************************\

Function: cpp_typecheck_fargst::exact_match

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_typecheck_fargst::match(
  const code_typet &code_type,
  unsigned &distance,
  cpp_typecheckt &cpp_typecheck) const
{
  distance=0;

  exprt::operandst ops = operands;
  const code_typet::argumentst &arguments=code_type.arguments();

  if(arguments.size()>ops.size())
  {
    // Check for default values.
    ops.reserve(arguments.size());

    for(unsigned i=ops.size(); i<arguments.size(); i++)
    {
      const exprt &default_value=
        arguments[i].default_value();

      if(default_value.is_nil())
        return false;
        
      ops.push_back(default_value);
    }
  }
  else if(arguments.size()<ops.size())
  {
    // check for ellipsis
    if(!code_type.has_ellipsis())
      return false;
  }

  for(unsigned i=0; i<ops.size(); i++)
  {
    // read
    // http://publib.boulder.ibm.com/infocenter/comphelp/v8v101/topic/com.ibm.xlcpp8a.doc/language/ref/implicit_conversion_sequences.htm
    //
    // The following are the three categories of conversion sequences in order from best to worst:
    // * Standard conversion sequences
    // * User-defined conversion sequences
    // * Ellipsis conversion sequences
    
    if(i>=arguments.size())
    {
      // Ellipsis is the 'worst' of the conversion sequences
      distance+=1000;
      continue;
    }
    
    exprt argument=arguments[i];

    exprt &operand=ops[i];

    #if 0
    // unclear, todo
    if(is_reference(operand.type()))
      std::cout << "O: " << operand.pretty() << std::endl;

    assert(!is_reference(operand.type()));
    #endif

    // "this" is a special case -- we turn the pointer type
    // into a reference type to do the type matching
    if(i==0 && argument.get(ID_C_base_name)==ID_this)
    {
      argument.type().set(ID_C_reference, true);
      argument.type().set("#this", true);
    }

    unsigned rank = 0;
    exprt new_expr;

    #if 0
    std::cout << "C: " << cpp_typecheck.to_string(operand.type())
              << " -> " << cpp_typecheck.to_string(argument.type()) << std::endl;
    #endif

    // can we do the standard conversion sequence?
    if(cpp_typecheck.implicit_conversion_sequence(
        operand, argument.type(), new_expr, rank))
    {
      // ok
      distance+=rank;
      #if 0
      std::cout << "OK " << rank << std::endl;
      #endif
    }
    else
    {
      #if 0
      std::cout << "NOT OK" << std::endl;
      #endif
      return false; // no conversion possible
    }
  }

  return true;
}
