/*******************************************************************\

 Module: Analyses Variable Sensitivity

 Author: DiffBlue Limited.

\*******************************************************************/

/// \file
/// Represents an entry in the write_stackt

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WRITE_STACK_ENTRY_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WRITE_STACK_ENTRY_H

#include "abstract_object.h"

class abstract_environmentt;
class namespacet;

class write_stack_entryt
{
public:
  virtual ~write_stack_entryt() = default;
  virtual std::pair<exprt, bool> get_access_expr() const = 0;
  virtual bool try_squash_in(
    std::shared_ptr<const write_stack_entryt> new_entry,
    const abstract_environmentt &enviroment,
    const namespacet &ns);
};

class simple_entryt : public write_stack_entryt
{
public:
  explicit simple_entryt(exprt expr);
  std::pair<exprt, bool> get_access_expr() const override;

private:
  exprt simple_entry;
};

class offset_entryt : public write_stack_entryt
{
public:
  explicit offset_entryt(abstract_object_pointert offset_value);
  std::pair<exprt, bool> get_access_expr() const override;
  bool try_squash_in(
    std::shared_ptr<const write_stack_entryt> new_entry,
    const abstract_environmentt &enviroment,
    const namespacet &ns) override;

private:
  abstract_object_pointert offset;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_WRITE_STACK_ENTRY_H
