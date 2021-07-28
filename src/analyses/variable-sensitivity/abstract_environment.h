/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// An abstract version of a program environment.  Each variable has
/// an abstract object rather than a value.  If these are top then
/// they are not explicitly stored so that the memory used is
/// proportional to what is known rather than just the number of
/// variables.
/// Note the use of sharing_mapt is critical for scalability.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_ENVIROMENT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_ENVIROMENT_H

#include <memory>

#include <analyses/variable-sensitivity/abstract_object.h>

exprt simplify_vsd_expr(exprt src, const namespacet &ns);
bool is_ptr_diff(const exprt &expr);
bool is_ptr_comparison(const exprt &expr);

class variable_sensitivity_object_factoryt;
using variable_sensitivity_object_factory_ptrt =
  std::shared_ptr<variable_sensitivity_object_factoryt>;

enum class widen_modet
{
  no,
  could_widen
};

class abstract_environmentt
{
public:
  using map_keyt = irep_idt;

  abstract_environmentt() = delete;

  explicit abstract_environmentt(
    variable_sensitivity_object_factory_ptrt _object_factory)
    : bottom(true), object_factory(std::move(_object_factory))
  {
  }

  /// These three are really the heart of the method

  /// Evaluate the value of an expression relative to the current domain
  ///
  /// \param expr: the expression to evaluate
  /// \param ns: the current namespace
  ///
  /// \return The abstract_object representing the value of the expression
  virtual abstract_object_pointert
  eval(const exprt &expr, const namespacet &ns) const;

  /// Assign a value to an expression
  ///
  /// \param expr: the expression to assign to
  /// \param value: the value to assign to the expression
  /// \param ns: the namespace
  ///
  /// \return A boolean, true if the assignment has changed the domain.
  ///
  ///  Assign is in principe simple, it updates the map with the new
  /// abstract object.  The challenge is how to handle write to compound
  /// objects, for example:
  ///    a[i].x.y = 23;
  /// In this case we clearly want to update a, but we need to delegate to
  /// the object in a so that it updates the right part of it (depending on
  /// what kind of array abstraction it is).  So, as we find the variable
  /// ('a' in this case) we build a stack of which part of it is accessed.
  ///
  /// As abstractions may split the assignment into multiple writes (for
  /// example pointers that could point to several locations, arrays with
  /// non-constant indexes), each of which has to handle the rest of the
  /// compound write, thus the stack is passed (to write, which does the
  /// actual updating) as an explicit argument rather than just via
  /// recursion.
  ///
  /// The same use case (but for the opposite reason; because you will only
  /// update one of the multiple objects) is also why a merge_write flag is
  /// needed.
  virtual bool assign(
    const exprt &expr,
    const abstract_object_pointert &value,
    const namespacet &ns);

  /// Reduces the domain based on a condition
  ///
  /// \param expr: the expression that is to be assumed
  /// \param ns: the current namespace
  ///
  /// \return True if the assume changed the domain.
  ///
  /// Reduces the domain to (an over-approximation) of the cases
  /// when the the expression holds.  Used to implement assume
  /// statements and conditional branches.
  /// It would be valid to simply return false here because it
  /// is an over-approximation.  We try to do better than that.
  /// The better the implementation the more precise the results
  /// will be.
  virtual bool assume(const exprt &expr, const namespacet &ns);
  exprt do_assume(const exprt &e, const namespacet &ns);

  /// Used within assign to do the actual dispatch
  ///
  /// \param lhs: the abstract object for the left hand side of the write
  ///             (i.e. the one to update).
  /// \param rhs: the value we are trying to write to the left hand side
  /// \param remaining_stack: what is left of the stack before the rhs can
  ///                         replace or be merged with the rhs
  /// \param ns: the namespace
  /// \param merge_write: Are we replacing the left hand side with the
  ///                     right hand side (e.g. we know for a fact that
  ///                     we are overwriting this object) or could the
  ///                     write in fact not take place and therefore we
  ///                     should merge to model the case where it did not.
  ///
  /// \return A modified version of the rhs after the write has taken place
  ///
  /// Write an abstract object onto another respecting a stack of
  /// member, index and dereference access. This ping-pongs between
  /// this method and the relevant write methods in abstract_struct,
  /// abstract_pointer and abstract_array until the stack is empty
  virtual abstract_object_pointert write(
    const abstract_object_pointert &lhs,
    const abstract_object_pointert &rhs,
    std::stack<exprt> remaining_stack,
    const namespacet &ns,
    bool merge_write);

  /// Delete a symbol from the map.  This is necessary if the
  /// symbol falls out of scope and should no longer be tracked.
  ///
  /// \param expr:  A symbol to delete from the map
  void erase(const symbol_exprt &expr);

  /// Look at the configuration for the sensitivity and create an
  /// appropriate abstract_object
  ///
  /// \param type: the type of the object whose state should be tracked
  /// \param top: does the type of the object start as top
  /// \param bottom: does the type of the object start as bottom in
  ///                the two-value domain
  /// \param ns: the current variable namespace
  ///
  /// \return The abstract object that has been created
  virtual abstract_object_pointert abstract_object_factory(
    const typet &type,
    const namespacet &ns,
    bool top,
    bool bottom) const;

  /// For converting constants in the program
  ///
  /// \param type: the type of the object whose state should be tracked
  /// \param e: the starting value of the symbol
  /// \param ns: the current variable namespace
  ///
  /// \return The abstract object that has been created
  ///
  /// Look at the configuration for the sensitivity and create an
  /// appropriate abstract_object, assigning an appropriate value
  /// Maybe the two abstract_object_factory methods should be
  /// compacted to one call...
  virtual abstract_object_pointert abstract_object_factory(
    const typet &type,
    const exprt &e,
    const namespacet &ns) const;

  /// Wraps an existing object in any configured context object
  ///
  /// \param abstract_object: The object to be wrapped
  ///
  /// \return The wrapped abstract object
  ///
  /// Look at the configuration context dependency, and constructs
  /// the appropriate wrapper object around the supplied object
  /// If no such configuration is enabled, the supplied object will be
  /// returned unchanged
  virtual abstract_object_pointert
  add_object_context(const abstract_object_pointert &abstract_object) const;

  /// Computes the join between "this" and "b"
  ///
  /// \param env: the other environment
  /// \param widen_mode: indicates if this is a widening merge
  ///
  /// \return A Boolean, true when the merge has changed something
  virtual bool merge(const abstract_environmentt &env, widen_modet widen_mode);

  /// This should be used as a default case / everything else has failed
  /// The string is so that I can easily find and diagnose cases where this
  /// occurs
  ///
  /// \param havoc_string: diagnostic string to track down havoc causing.
  ///
  /// Set the domain to top
  virtual void havoc(const std::string &havoc_string);

  /// Set the domain to top (i.e. everything)
  void make_top();

  /// Set the domain to top (i.e. no possible states / unreachable)
  void make_bottom();

  /// Gets whether the domain is bottom
  bool is_bottom() const;

  /// Gets whether the domain is top
  bool is_top() const;

  /// Print out all the values in the abstract object map
  ///
  /// \param out: the stream to write to
  /// \param ai: the abstract interpreter that contains this domain
  /// \param ns: the current namespace
  void output(std::ostream &out, const class ai_baset &ai, const namespacet &ns)
    const;

  /// Check the structural invariants are maintained.
  /// In this case this is checking there aren't any null pointer mapped values
  bool verify() const;

  /// For our implementation of variable sensitivity domains, we need
  /// to be able to efficiently find symbols that have changed between
  /// different domains. To do this, we need to be able to quickly
  /// find which symbols have new written locations, which we do by
  /// finding the intersection between two different domains
  /// (environments).
  ///
  /// Inputs are two abstract_environmentt's that need to be
  /// intersected for, so that we can find symbols that have changed
  /// between different domains.
  ///
  /// \return An std::vector containing the symbols that are present
  /// in both environments.
  static std::vector<abstract_environmentt::map_keyt> modified_symbols(
    const abstract_environmentt &first,
    const abstract_environmentt &second);

  abstract_object_statisticst gather_statistics(const namespacet &ns) const;

protected:
  bool bottom;

  // We may need to break out more of these cases into these
  virtual abstract_object_pointert
  eval_expression(const exprt &e, const namespacet &ns) const;

  abstract_object_pointert
  resolve_symbol(const exprt &e, const namespacet &ns) const;

  sharing_mapt<map_keyt, abstract_object_pointert> map;

private:
  /// Look at the configuration for the sensitivity and create an
  /// appropriate abstract_object
  ///
  /// \param type: the type of the object whose state should be tracked
  /// \param top: does the type of the object start as top in
  ///             the two-value domain
  /// \param bottom: does the type of the object start as bottom in
  ///                the two-value domain
  /// \param e: the starting value of the symbol if top and bottom
  ///           are both false
  /// \param environment: the current environment (normally *this)
  /// \param ns: the current variable namespace
  ///
  /// \return The abstract object that has been created
  abstract_object_pointert abstract_object_factory(
    const typet &type,
    bool top,
    bool bottom,
    const exprt &e,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  variable_sensitivity_object_factory_ptrt object_factory;
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_ENVIROMENT_H
