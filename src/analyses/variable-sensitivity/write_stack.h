/*******************************************************************\

 Module: Variable Sensitivity Domain

 Author: DiffBlue Limited.

\*******************************************************************/

/// \file
/// Represents a stack of write operations to an addressable memory
/// location

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WRITE_STACK_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WRITE_STACK_H

#include <analyses/variable-sensitivity/write_stack_entry.h>

class write_stackt
{
public:
  typedef std::vector<std::shared_ptr<write_stack_entryt>>
    continuation_stack_storet;

  write_stackt();

  write_stackt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  exprt to_expression() const;

  size_t depth() const;
  exprt target_expression(size_t depth) const;
  exprt offset_expression() const;
  bool is_top_value() const;

private:
  void construct_stack_to_pointer(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  void construct_stack_to_lvalue(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  void construct_stack_to_array_index(
    const index_exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  void add_to_stack(
    std::shared_ptr<write_stack_entryt> entry_pointer,
    const abstract_environmentt environment,
    const namespacet &ns);

  enum class integral_resultt
  {
    LHS_INTEGRAL,
    RHS_INTEGRAL,
    NEITHER_INTEGRAL
  };

  static integral_resultt get_which_side_integral(
    const exprt &expr,
    exprt &out_base_expr,
    exprt &out_integral_expr);

  continuation_stack_storet stack;
  bool top_stack;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WRITE_STACK_H
