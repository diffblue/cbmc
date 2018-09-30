/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck_fargs.h"

#include <cassert>

#include <util/std_types.h>

#include <ansi-c/c_qualifiers.h>

#include "cpp_typecheck.h"

bool cpp_typecheck_fargst::has_class_type() const
{
  for(const auto &op : operands)
  {
    if(op.type().id() == ID_struct)
      return true;
  }

  return false;
}

void cpp_typecheck_fargst::build(
  const side_effect_expr_function_callt &function_call)
{
  in_use=true;
  operands = function_call.op1().operands();
}

bool cpp_typecheck_fargst::match(
  const code_typet &code_type,
  unsigned &distance,
  cpp_typecheckt &cpp_typecheck) const
{
  distance=0;

  exprt::operandst ops=operands;
  const code_typet::parameterst &parameters=code_type.parameters();

  if(parameters.size()>ops.size())
  {
    // Check for default values.
    ops.reserve(parameters.size());

    for(std::size_t i=ops.size(); i<parameters.size(); i++)
    {
      const exprt &default_value=
        parameters[i].default_value();

      if(default_value.is_nil())
        return false;

      ops.push_back(default_value);
    }
  }
  else if(parameters.size()<ops.size())
  {
    // check for ellipsis
    if(!code_type.has_ellipsis())
      return false;
  }

  exprt::operandst::iterator it=ops.begin();
  for(const auto &parameter : parameters)
  {
    // read
    // http://publib.boulder.ibm.com/infocenter/comphelp/v8v101/topic/
    //   com.ibm.xlcpp8a.doc/language/ref/implicit_conversion_sequences.htm
    //
    // The following are the three categories of conversion sequences
    // in order from best to worst:
    // * Standard conversion sequences
    // * User-defined conversion sequences
    // * Ellipsis conversion sequences

    assert(it!=ops.end());
    const exprt &operand=*it;
    typet type=parameter.type();

    #if 0
    // unclear, todo
    if(is_reference(operand.type()))
      std::cout << "O: " << operand.pretty() << '\n';

    assert(!is_reference(operand.type()));
    #endif

    // "this" is a special case -- we turn the pointer type
    // into a reference type to do the type matching
    if(it==ops.begin() && parameter.get(ID_C_base_name)==ID_this)
    {
      type.set(ID_C_reference, true);
      type.set(ID_C_this, true);
    }

    unsigned rank=0;
    exprt new_expr;

    #if 0
    std::cout << "C: " << cpp_typecheck.to_string(operand.type())
              << " -> " << cpp_typecheck.to_string(parameter.type())
              << '\n';
    #endif

    // can we do the standard conversion sequence?
    if(cpp_typecheck.implicit_conversion_sequence(
        operand, type, new_expr, rank))
    {
      // ok
      distance+=rank;
      #if 0
      std::cout << "OK " << rank << '\n';
      #endif
    }
    else if(
      operand.id() == ID_initializer_list && cpp_typecheck.cpp_is_pod(type) &&
      operand.operands().size() == 1 &&
      cpp_typecheck.implicit_conversion_sequence(
        operand.op0(), type, new_expr, rank))
    {
      distance += rank;
    }
    else
    {
      #if 0
      std::cout << "NOT OK\n";
      #endif
      return false; // no conversion possible
    }

    ++it;
  }

  // we may not have used all operands
  for( ; it!=ops.end(); ++it)
    // Ellipsis is the 'worst' of the conversion sequences
    distance+=1000;

  return true;
}
