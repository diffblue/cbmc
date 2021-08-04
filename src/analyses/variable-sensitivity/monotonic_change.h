/*******************************************************************\

 Module: Abstract interpretation for strict and monotonic change

 Authors: Long Pham, Saswat Padhi

\*******************************************************************/

// We have based this class on constant_abstract_value.h. We are grateful to its
// authors.

/*
Overview:
This abstract interpretation checks whether variables have "strictly" and
"monotonically" increased/decreased since the beginning of given GOTO code. In
this context, "strict" means the increase/decrease is strict - it is NOT allowed
to stay unchanged. "Monotonic" means the variable keeps increasing (or
decreasing) within a loop body. If a variable increases at first and then starts
decreasing, this abstract interpretation cannot tell the overall change of the
variable. 

In another context, the word "monotonicity" refers to the fact that a candidate
decreases clause must strictly decrease in "all" iterations of the loop. So we
have two kinds of "monotonicity": (i) the monotonicity of the decreases clause
within a single loop iteration/body and (ii) the monotonicity of the
decreases clause across all iterations of the loop at run time. When there is a
risk of confusion, I will try to distinguish between these two kinds of
"monotonicity." However, usually, I will refer to monotonicity "within" a loop
iteration/body.

Motivation:
We will use this abstract interpretation in the automatic inference of decreases
clauses (aka ranking functions or loop variants). For example, consider a
while-loop whose loop guard is x < y, where x and y are variables. If we know
that x strictly increases in the loop body and that y stays unchanged, we can
successfully infer that y - x is a correct decreases clause.

Example: 
For illustration, consider the following GOTO code:
DECL x
ASSIGN x := x + 1
ASSIGN x := x - 1

Immediately after the declaration of x, the abstract value of x is
"unchanged." This means variable x has stayed unchanged since the "beginning" of
the code.

Next, after executing the command x++, the abstract value of x is "strict
increase." It means variable x has been strictly and monotonically increasing
since the "beginning" of the code.

Finally, we execute x-- after x++. Unlike interval analysis, this predicate
abstraction does NOT keep track of how much x has changed. Instead, it only
keeps track of the current strict-and-monotonic-change-status (i.e. the current
abstract value) of x. Hence, in the above example, we cannot tell the net effect
on x after x--. Consequently, after x--, the abstract value of x is "top"; i.e.
we know nothing about x. 

Abstract domain:
The class monotonic_changet inherits from the class abstract_value_objectt. This
makes sense because abstract interpretation is a special case of abstract
interpretation. The base class abstract_value_objectt already contains two
abstract values:
(i) top (i.e. inconclusive)
(ii) bottom (i.e. infeasible). 
These are the top and bottom elements of a lattice, respectively.

In addition to these two values, monotonic_changet has the following abstract
values:
(iii) strict monotonic increase
(iv) strict monotonic decrease
(v) unchanged.

The Hasse diagram of this abstract domain is displayed below.
              top
           /   |   \
          /    |    \
         /     |     \
        /      |      \
increase   unchanged  decrease
       \       |      /
        \      |     /
         \     |    /
           \   |   /
            bottom

Technical challenge: 
Existing derived classes of abstract_value_objectt include
(i) constant_abstract_valuet, 
(ii) interval_abstract_valuet, and
(iii) value_set_abstract_objectt. 
When computing the abstract value of an assignment, these classes only need to
consider the right-hand side of the assignment. Put simply, these abstract
interpretation are "non-relational." By contrast, monotonic_changet needs to
know not only the right-hand side but also the left-hand side. 

For example, consider two assignments: x := x + 1 and x := y + 1. For the
existing derived classes of abstract_value_objectt, x's abstract value after
this assignment can be computed by just looking at the right-hand side.

On the other hand, monotonic_changet cannot computer x's abstract value by
looking at the right-hand side in isolation. It needs to check whether the
variable being incremented is the same as the variable on the left-hand side.
Furthermore, it needs to know the current abstract value of x. If x's current
abstract value is "unchanged," x := x + 1 will change x's abstract value to
"monotonic increase." Instead, if x's current abstract value is "monotonic
decrease," x := x + 1 will change the abstract value to "top."

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
  strict_increase,
  strict_decrease,
  unchanged,
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
