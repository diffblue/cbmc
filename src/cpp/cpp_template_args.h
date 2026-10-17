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

#include <functional>

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
  /// N5008 [temp.deduct]/2, [temp.arg]: an argument is usable only when every
  /// template parameter in it has been deduced or specified; the undeduced
  /// parameter may sit INSIDE the argument (`const _U2 &` in std::pair's
  /// deprecated converting-constructor constraint `is_constructible<_T2,
  /// const _U2&>` while `_U2` is still unassigned).  Checking only the top
  /// level let `is_constructible<T, ? &>` be instantiated, which instantiated
  /// T's forwarding constructor with a `?` argument; its body errors leaked
  /// ("no match for symbol 'set'" in every TU with a std::map to such a
  /// class) and members touched on the way were left bodiless.
  bool has_unassigned() const
  {
    std::function<bool(const irept &)> nested = [&](const irept &n) -> bool
    {
      if(n.id() == ID_unassigned)
        return true;
      for(const auto &s : n.get_sub())
        if(nested(s))
          return true;
      for(const auto &ns : n.get_named_sub())
        if(ns.first != ID_C_source_location && nested(ns.second))
          return true;
      return false;
    };
    for(const auto &arg : arguments())
      if(nested(arg))
        return true;

    return false;
  }

  /// N5008 [temp.deduct.type]/2: "If [deducing values] cannot be done
  /// for any P/A pair, ..., or if any template argument remains
  /// neither deduced nor explicitly specified, template argument
  /// deduction fails."  A conflicting deduction is recorded as an
  /// ID_nil binding (see mark_targs_conflicting in
  /// cpp_typecheck_resolve.cpp); such a candidate must be discarded
  /// without re-type-checking its pattern -- the re-typecheck throws
  /// on the nil parameter and is caught as SFINAE, which is correct
  /// but costs a full pattern conversion per doomed candidate
  /// (~39,000 of them for std::tuple's constructor overload set,
  /// dominated by tuple_size<pair<_T1,_T2>> vs tuple<int,int>).
  bool has_conflict() const
  {
    for(const auto &arg : arguments())
      if(arg.is_nil() || arg.type().is_nil())
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
