/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_ENVIROMENT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_ENVIROMENT_H

#include <map>
#include <memory>
#include <stack>

#include <util/std_expr.h>
#include <util/message.h>
#include <analyses/variable-sensitivity/abstract_object.h>

class abstract_environmentt
{
public:
  // These three are really the heart of the method
  virtual abstract_object_pointert eval(
    const exprt &expr, const namespacet &ns) const;
  virtual bool assign(
    const exprt &expr,
    const abstract_object_pointert value,
    const namespacet &ns);
  virtual bool assume(const exprt &expr, const namespacet &ns);

  virtual abstract_object_pointert write(
    abstract_object_pointert lhs,
    abstract_object_pointert rhs,
    std::stack<exprt> remaining_stack,
    const namespacet &ns,
    bool merge_write);

  virtual abstract_object_pointert abstract_object_factory(
    const typet &type,
    const namespacet &ns,
    bool top=true,
    bool bottom=false) const;
  // For converting constants in the program
  // Maybe these two should be compacted to one call...
  virtual abstract_object_pointert abstract_object_factory(
    const typet &type, const exprt &e, const namespacet &ns) const;


  virtual bool merge(const abstract_environmentt &env);

  // This should be used as a default case / everything else has failed
  // The string is so that I can easily find and diagnose cases where this
  // occurs
  virtual void havoc(const std::string &havoc_string);

  void make_top();
  void make_bottom();

  bool get_is_bottom() const;
  bool get_is_top() const;

  void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const;

protected:
  bool is_bottom;

 // We may need to break out more of these cases into these
 virtual abstract_object_pointert eval_expression(
    const exprt &e, const namespacet &ns) const;

  typedef symbol_exprt map_keyt;
  std::map<map_keyt, abstract_object_pointert> map;

private:
  abstract_object_pointert abstract_object_factory(
    const typet &type, bool top, bool bottom, const exprt &e,
    const namespacet &ns) const;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_ENVIROMENT_H
