/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#ifndef CPROVER_CPP_CPP_TEMPLATE_ARGS_H
#define CPROVER_CPP_CPP_TEMPLATE_ARGS_H

#include <util/expr.h>
#include <util/invariant.h>

// A data structures for template arguments, i.e.,
// a sequence of types/expressions of the form <E1, T2, ...>.
// Not to be confused with the template parameters!

class cpp_template_args_baset:public irept
{
public:
  cpp_template_args_baset():irept(ID_template_args)
  {
  }

  typedef exprt::operandst argumentst;

  argumentst &arguments()
  {
    return (argumentst &)(add(ID_arguments).get_sub());
  }

  const argumentst &arguments() const
  {
    return (const argumentst &)(find(ID_arguments).get_sub());
  }
};

// the non-yet typechecked variant

class cpp_template_args_non_tct:public cpp_template_args_baset
{
};

inline cpp_template_args_non_tct &to_cpp_template_args_non_tc(
  irept &irep)
{
  PRECONDITION(irep.id() == ID_template_args);
  return static_cast<cpp_template_args_non_tct &>(irep);
}

inline const cpp_template_args_non_tct &to_cpp_template_args_non_tc(
  const irept &irep)
{
  PRECONDITION(irep.id() == ID_template_args);
  return static_cast<const cpp_template_args_non_tct &>(irep);
}

// the already typechecked variant

class cpp_template_args_tct:public cpp_template_args_baset
{
public:
  bool has_unassigned() const
  {
    const argumentst &_arguments=arguments();
    for(argumentst::const_iterator
        it=_arguments.begin();
        it!=_arguments.end();
        it++)
      if(it->id()==ID_unassigned ||
         it->type().id()==ID_unassigned)
        return true;

    return false;
  }
};

inline cpp_template_args_tct &to_cpp_template_args_tc(irept &irep)
{
  PRECONDITION(irep.id() == ID_template_args);
  return static_cast<cpp_template_args_tct &>(irep);
}

inline const cpp_template_args_tct &to_cpp_template_args_tc(const irept &irep)
{
  PRECONDITION(irep.id() == ID_template_args);
  return static_cast<const cpp_template_args_tct &>(irep);
}

#endif // CPROVER_CPP_CPP_TEMPLATE_ARGS_H
