/*******************************************************************\

Module: Analyses

Author: Diffblue Ltd.

\*******************************************************************/
/// \file
/// Analyses

#ifndef CPROVER_ANALYSES_DOES_REMOVE_CONST_H
#define CPROVER_ANALYSES_DOES_REMOVE_CONST_H

#include <utility>

class goto_programt;
class exprt;
class source_locationt;
class typet;

class does_remove_constt
{
public:
  explicit does_remove_constt(const goto_programt &);
  std::pair<bool, source_locationt>  operator()() const;

private:
  bool does_expr_lose_const(const exprt &expr) const;

  bool is_type_at_least_as_const_as(
    const typet &type_more_const, const typet &type_compare) const;

  bool does_type_preserve_const_correctness(
    const typet *target_type, const typet *source_type) const;

  const goto_programt &goto_program;

  friend class does_remove_const_testt;
};

#endif // CPROVER_ANALYSES_DOES_REMOVE_CONST_H
