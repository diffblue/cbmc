/*******************************************************************\

 Module: Predicate abstraction for monotonic change

 Authors: Long Pham, Saswat Padhi

\*******************************************************************/

// We have based this class on constant_abstract_value.h. We are grateful to its
// authors.

/*
Overview: 
This predicate abstraction checks whether variables have monotonically increased
or decreased since the beginning of given GOTO code. We will use this predicate
abstraction in the automatic inference of decreases clauses (aka ranking
functions or loop variants). For example, consider a while-loop whose loop guard
is x < y, where x and y are variables. If we know that x always monotonically
increases in the loop body and that y always stays constant, we can successfully
infer that y - x is a correct decreases clause.

Example: 
For illustration, consider this C code:
int x = 42;
x++;
x--;

This will be translated to the following GOTO code:
DECL x
ASSIGN x := 42
ASSIGN x := x + 1
ASSIGN x := x - 1

Immediately after the declaration of x, x is said to be "declared but
uninitialized." Next, after the declaration of x, we initialize x to 42 by the
command ASSIGN x:= 42. Immediately after this assignment, x is said to be
"constant"; that is, x has stayed constant since the beginning of the code. 

Subsequently, after the command x++, x is said to be "monotonically increasing."
In this context, "monotonic" increase means "strict" increase. If x is "not
strictly" increasing but "non-strictly" increasing, then it means x has stayed
constant. 

Finally, we execute x-- after x++. Unlike interval analysis, this predicate
abstraction does NOT keep track of how much x has changed. Instead, it only
keeps track of the current monotonic-change status of x (e.g. monotonic
increase, constant, monotonic decrease). Hence, in the above example, we cannot
tell the net effect on x after x--. Consequently, after x--, the
monotonic-change status of x is "top"; i.e. we know nothing about x. 

Implementation overview:
The class monotonic_changet inherits from the class abstract_value_objectt. This
makes sense becuase predicate abstraction is a special case of abstract
interpretation. The base class abstract_value_objectt already contains two
abstract values: 
(i) top 
(ii) bottom. 

In addition to these two values, monotonic_changet has the following abstract
values to represent the current monotonic-change status: 
(iii) monotonic increase 
(iv) monotonic decrease 
(v) constant 
(vi) declared but uninitialized. 

What happens if we try to increment a variable that has been declared but
uninitialized? Incrementing such a variable is possible in the GOTO language,
but I believe it is impossible in C. 

Technical challenge: 
Existing derived classes of abstract_value_objectt include
(i) constant_abstract_valuet, 
(ii) interval_abstract_valuet, and
(iii) value_set_abstract_objectt. 
When computing the abstract value of an assignment, these classes only need to
consider the right-hand side of the assignment. By contrast, monotonic_changet
needs to know not only the right-hand side but also the left-hand side. 

For example, consider two assignments: x := x + 1 and x := y + 1. For the
existing derived classes of abstract_value_objectt, x's abstract value after
this assignment can be computed by just looking at the right-hand side.

On the other hand, monotonic_changet cannot computer x's abstract value by
looking at the right-hand side in isolation. It needs to check whether the
variable being incremented is the same as the variable on the left-hand side.
Furthermore, it needs to know the current monotonic-change status of x. If x's
current status is "constant," x := x + 1 will change x's status to "monotonic
increase." Instead, if x's current status is "monotonic decrease," x := x + 1
will change the status to "top."

In this way, to compute the abstract value of an assignment, we need information
about the left-hand side. As a consequence, to implement this predicate
abstraction, we have made fairly extensive modification to the existing code
base.
*/

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_MONOTONIC_CHANGE_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_MONOTONIC_CHANGE_H

#include <iosfwd>

#include <analyses/variable-sensitivity/abstract_value_object.h>

enum monotonicity_flags
{
  increase,
  decrease,
  constant,
  uninitialized,
  // We can tell whether it is top or bottom by is_top() and is_bottom(), which
  // are inherited from abstract_objectt.
  top_or_bottom
};

class monotonic_changet : public abstract_value_objectt
{
public:
  explicit monotonic_changet(const typet &t);
  monotonic_changet(const typet &t, bool tp, bool bttm);
  monotonic_changet(
    const typet &t,
    bool tp,
    bool bttm,
    monotonicity_flags initial_value);
  monotonic_changet(
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns);

  ~monotonic_changet() override = default;

  index_range_implementation_ptrt
  index_range_implementation(const namespacet &ns) const override;

  value_range_implementation_ptrt value_range_implementation() const override;

  constant_interval_exprt to_interval() const override;

  abstract_value_pointert
  constrain(const exprt &lower, const exprt &upper) const override;

  void output(
    std::ostream &out,
    const class ai_baset &ai,
    const class namespacet &ns) const override;

  void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const override;

  size_t internal_hash() const override
  {
    return std::hash<int>{}(monotonicity_value);
  }

  bool internal_equality(const abstract_object_pointert &other) const override
  {
    auto cast_other = std::dynamic_pointer_cast<const monotonic_changet>(other);
    return cast_other && monotonicity_value == cast_other->monotonicity_value;
  }

  monotonicity_flags monotonicity_value;

protected:
  CLONE

  /// Merges another abstract value into this one
  ///
  /// \param other: the abstract object to merge with
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns a new abstract object that is the result of the merge
  ///         unless the merge is the same as this abstract object, in which
  ///         case it returns this.
  abstract_object_pointert merge_with_value(
    const abstract_value_pointert &other,
    const widen_modet &widen_mode) const override;
  abstract_object_pointert merge_with_monotonic_change(
    const sharing_ptrt<const monotonic_changet> &other) const;

  abstract_object_pointert
  meet_with_value(const abstract_value_pointert &other) const override;
  abstract_object_pointert meet_with_monotonic_change(
    const sharing_ptrt<const monotonic_changet> &other) const;

private:
  void set_top_internal() override;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_MONOTONIC_CHANGE_H
