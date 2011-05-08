/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_CPP_TYPECHECK_FARGS_H
#define CPROVER_CPP_TYPECHECK_FARGS_H

#include <std_code.h>
class cpp_typecheckt;

class cpp_typecheck_fargst // for function overloading
{
public:
  bool in_use, has_object;
  exprt::operandst operands;
  
  // has_object indicates that the first element of
  // 'operands' is the 'this' pointer (with the object type,
  // not pointer to object type)

  cpp_typecheck_fargst():in_use(false), has_object(false) { }

  bool has_class_type() const;

  void build(
    const side_effect_expr_function_callt &function_call);

  explicit cpp_typecheck_fargst(
    const side_effect_expr_function_callt &function_call):
    in_use(false), has_object(false)
  {
    build(function_call);
  }

  bool match(
    const code_typet &code_type,
    unsigned &distance,
    cpp_typecheckt &cpp_typecheck) const;

  void add_object(const exprt &expr)
  {
    //if(!in_use) return;
    has_object=true;
    operands.insert(operands.begin(), expr);
  }

  void remove_object()
  {
    assert(has_object);
    operands.erase(operands.begin());
    has_object = false;
  }
};

#endif
