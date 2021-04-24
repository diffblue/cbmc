/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// abstract_objectt is the top of the inheritance heirarchy of objects
/// used to represent individual variables in the general non-relational
/// domain.  It is a two element abstraction (i.e. it is either top or
/// bottom).  Within the hierarchy of objects under it, child classes are
/// more precise abstractions (the converse doesn't hold to avoid
/// diamonds and inheriting unnecessary fields).  Thus the common parent
/// of two classes is an abstraction capable of representing both.  This
/// is important for understanding merge.
///
/// These objects are intended to be used in a copy-on-write style, which
/// is why their interface differs a bit from ai_domain_baset's
/// modify-in-place style of interface.
///
/// Although these can represent bottom (this variable cannot take any
/// value) it is not common for them to do so.

#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H

#include <memory>
#include <set>
#include <stack>

#include <goto-programs/goto_program.h>
#include <util/sharing_map.h>

class abstract_environmentt;
class namespacet;
struct abstract_object_statisticst;
enum class widen_modet;

#define CLONE                                                                  \
  internal_abstract_object_pointert mutable_clone() const override             \
  {                                                                            \
    typedef std::remove_const<                                                 \
      std::remove_reference<decltype(*this)>::type>::type current_typet;       \
    return internal_abstract_object_pointert(new current_typet(*this));        \
  }

/// Merge is designed to allow different abstractions to be merged
/// gracefully.  There are two real use-cases for this:
///
///  1. Having different abstractions for the variable in different
///     parts of the program.
///  2. Allowing different domains to write to ambiguous locations
///     for example, if a stores multiple values (maybe one per
///     location) with a constant for each, i does not represent one
///     single value (top, non-unit interval, etc.) and v is something
///     other than constant, then
///         a[i] = v
///     will cause this to happen.
///
/// To handle this, merge is dispatched to the first abstract object being
/// merged, which switches based on the type of the other object. If it can
/// merge then it merges, otherwise it calls the parent merge.

template <class T>
using sharing_ptrt = std::shared_ptr<const T>; // NOLINT(*)

typedef sharing_ptrt<class abstract_objectt> abstract_object_pointert;
using abstract_object_visitedt = std::set<abstract_object_pointert>;

class abstract_objectt : public std::enable_shared_from_this<abstract_objectt>
{
public:
  /// \param type: the type the abstract_object is representing
  explicit abstract_objectt(const typet &type);

  /// Start the abstract object at either top or bottom or neither
  /// Asserts if both top and bottom are true
  ///
  /// \param type: the type the abstract_object is representing
  /// \param top: is the abstract_object starting as top
  /// \param bottom: is the abstract_object starting as bottom
  abstract_objectt(const typet &type, bool top, bool bottom);

  /// Construct an abstract object from the expression
  ///
  /// \param expr: The expression to use as the starting pointer for an abstract
  ///   object
  /// \param environment: The environment this abstract object is
  ///   being created in
  /// \param ns: The namespace
  abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  /// Ctor for building object of types that differ from the types of input
  /// expressions
  ///
  /// \param type explicitly declared type the resulting object should have
  /// \param expr expression used to build the object
  /// \param environment abstract environment to evaluate the expression
  /// \param ns namespace to uncover names inside the expression
  abstract_objectt(
    const typet &type,
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  virtual ~abstract_objectt()
  {
  }

  /// Get the real type of the variable this abstract object is representing.
  ///
  /// \return The program type this abstract object represents
  virtual const typet &type() const;

  /// Find out if the abstract object is top
  ///
  /// \return Returns true if the abstract object is representing the top
  ///         (i.e. we don't know anything about the value).
  virtual bool is_top() const;

  /// Find out if the abstract object is bottom
  ///
  /// \return Returns true if the abstract object is representing the bottom.
  virtual bool is_bottom() const;

  /// \brief Verify the internal structure of an abstract_object is correct
  /// \return true if the abstract_object is correctly constructed, or false
  /// otherwise
  virtual bool verify() const;

  virtual void get_statistics(
    abstract_object_statisticst &statistics,
    abstract_object_visitedt &visited,
    const abstract_environmentt &env,
    const namespacet &ns) const;

  /// Interface for transforms
  ///
  /// \param expr: the expression to evaluate and find the result of it.
  ///              This will be the symbol referred to be op0()
  /// \param operands: an abstract_object (pointer) that represent
  ///                  the possible values of each operand
  /// \param environment: the abstract environment in which the
  ///                     expression is being evaluated
  /// \param ns: the current variable namespace
  ///
  /// \return Returns the abstract_object representing the result of
  ///         this expression to the maximum precision available.
  ///
  /// To try and resolve different expressions with the maximum level
  /// of precision available.
  virtual abstract_object_pointert expression_transform(
    const exprt &expr,
    const std::vector<abstract_object_pointert> &operands,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  /// Converts to a constant expression if possible
  ///
  /// \return Returns an exprt representing the value if the value is known and
  ///          constant. Otherwise returns the nil expression
  ///
  /// If abstract element represents a single value, then that value,
  /// otherwise nil. E.G. if it is an interval then this will be x if it is
  /// [x,x] This is the (sort of) dual to the constant_exprt constructor
  /// that allows an object to be built from a value.
  virtual exprt to_constant() const;

  /**
   * A helper function to evaluate writing to a component of an
   * abstract object. More precise abstractions may override this to
   * update what they are storing for a specific component.
   *
   * \param environment the abstract environment
   * \param ns the current namespace
   * \param stack the remaining stack of expressions on the LHS to evaluate
   * \param specifier the expression uses to access a specific component
   * \param value the value we are trying to write to the component
   * \param merging_write if true, this and all future writes will be merged
   * with the current value
   *
   * \return the abstract_objectt representing the result of writing
   * to a specific component.
   */
  virtual abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> &stack,
    const exprt &specifier,
    const abstract_object_pointert &value,
    bool merging_write) const;

  /// Print the value of the abstract object
  ///
  /// \param out: the stream to write to
  /// \param ai: the abstract interpreter that contains the abstract domain
  ///            (that contains the object ... )
  /// \param ns: the current namespace
  virtual void output(
    std::ostream &out,
    const class ai_baset &ai,
    const namespacet &ns) const;

  typedef std::set<goto_programt::const_targett> locationst;
  typedef sharing_mapt<irep_idt, abstract_object_pointert, false, irep_id_hash>
    shared_mapt;

  static void dump_map(std::ostream out, const shared_mapt &m);
  /**
   * \brief Dump all elements in m1 that are different or missing in m2
   *
   * \param out the stream to write output to
   * \param m1 the 'target' sharing_map
   * \param m2 the reference sharing map
   */
  static void
  dump_map_diff(std::ostream out, const shared_mapt &m1, const shared_mapt &m2);

  /**
   * Determine whether 'this' abstract_object has been modified in comparison
   * to a previous 'before' state.
   * \param before The abstract_object_pointert to use as a reference to
   * compare against
   * \return true if 'this' is considered to have been modified in comparison
   * to 'before', false otherwise.
   */
  virtual bool has_been_modified(const abstract_object_pointert &before) const
  {
    /// Default implementation, with no other information to go on
    /// falls back to relying on copy-on-write and pointer inequality
    /// to indicate if an abstract_objectt has been modified
    return this != before.get();
  };

  /// Clones the first parameter and merges it with the second.
  ///
  /// \param op1: the first abstract object to merge, this object determines
  ///             the sensitivity of the output and is the object compared
  ///             against to choose whether this merge changed anything
  /// \param op2: the second abstract object to merge
  /// \param out_modifications: reference to a flag indicating modification
  ///
  /// \return A pair containing the merged abstract object with the same
  ///         sensitivity as op1, and a modified flag which
  ///         will be true if the merged abstract object is different from op1
  struct combine_result
  {
    abstract_object_pointert object;
    bool modified;
  };
  static combine_result merge(
    const abstract_object_pointert &op1,
    const abstract_object_pointert &op2,
    const widen_modet &widen_mode);

  /// Interface method for the meet operation. Decides whether to use the base
  /// implementation or if a more precise abstraction is attainable.
  /// \param op1 lhs object for meet
  /// \param op2 rhs object for meet
  /// \return A pair containing the merged abstract object with the same
  ///         sensitivity as op1, and a modified flag which
  ///         will be true if the returned object is different from op1
  static combine_result meet(
    const abstract_object_pointert &op1,
    const abstract_object_pointert &op2);

  /// Base implementation of the meet operation: only used if no more precise
  /// abstraction can be used, can only result in {TOP, BOTTOM, one of the
  /// original objects}
  /// \param other pointer to the abstract object to meet
  /// \return the resulting abstract object pointer
  virtual abstract_object_pointert
  meet(const abstract_object_pointert &other) const;

  /**
   * Update the location context for an abstract object, potentially
   * propogating the update to any children of this abstract object.
   *
   * \param locations the set of locations to be updated
   * \param update_sub_elements if true, propogate the update operation to any
   * children of this abstract object
   *
   * \return a clone of this abstract object with it's location context
   * updated
   */
  virtual abstract_object_pointert update_location_context(
    const locationst &locations,
    const bool update_sub_elements) const;

  // Const versions must perform copy-on-write
  abstract_object_pointert make_top() const
  {
    if(is_top())
      return shared_from_this();

    internal_abstract_object_pointert clone = mutable_clone();
    clone->set_top();
    return clone;
  }

  abstract_object_pointert clear_top() const
  {
    if(!is_top())
      return shared_from_this();

    internal_abstract_object_pointert clone = mutable_clone();
    clone->set_not_top();
    return clone;
  }

  virtual abstract_object_pointert unwrap_context() const;

  /**
   * Pure virtual interface required of a client that can apply a copy-on-write
   * operation to a given abstract_object_pointert.
   */
  struct abstract_object_visitort
  {
    virtual abstract_object_pointert
    visit(const abstract_object_pointert element) const = 0;
  };

  /**
   * Apply a visitor operation to all sub elements of this abstract_object.
   * A sub element might be a member of a struct, or an element of an array,
   * for instance, but this is entirely determined by the particular
   * derived instance of abstract_objectt.
   *
   * \param visitor an instance of a visitor class that will be applied to
   * all sub elements
   * \return A new abstract_object if it's contents is modifed, or this if
   * no modification is needed
   */
  virtual abstract_object_pointert
  visit_sub_elements(const abstract_object_visitort &visitor) const
  {
    return shared_from_this();
  }

  virtual size_t internal_hash() const
  {
    return std::hash<abstract_object_pointert>{}(shared_from_this());
  }

  virtual bool internal_equality(const abstract_object_pointert &other) const
  {
    return shared_from_this() == other;
  }

private:
  /// To enforce copy-on-write these are private and have read-only accessors
  typet t;
  bool bottom;
  bool top;

  // Hooks to allow a sub-class to perform its own operations on
  // setting/clearing top
  virtual void set_top_internal()
  {
  }
  virtual void set_not_top_internal()
  {
  }

  /**
   * Helper function for abstract_objectt::abstract_object_merge to perform any
   * additional actions after the base abstract_object_merge has completed it's
   * actions but immediately prior to it returning. As such, this function gives
   * the ability to perform additional work for a merge.
   *
   * This default implementation just returns itself.
   *
   * \param other the object to merge with this
   *
   * \return the result of the merge
   */
  virtual abstract_object_pointert
  abstract_object_merge_internal(const abstract_object_pointert &other) const;

  /// Helper function for base meet, in case additional work was needed. Base
  /// implementation simply return pointer to itself.
  /// \param other pointer to the other object
  /// \return the resulting object
  virtual abstract_object_pointert
  abstract_object_meet_internal(const abstract_object_pointert &other) const;

protected:
  template <class T>
  using internal_sharing_ptrt = std::shared_ptr<T>;

  typedef internal_sharing_ptrt<class abstract_objectt>
    internal_abstract_object_pointert;

  // Macro is not used as this does not override
  virtual internal_abstract_object_pointert mutable_clone() const
  {
    return internal_abstract_object_pointert(new abstract_objectt(*this));
  }

  /// Create a new abstract object that is the result of the merge, unless
  /// the object would be unchanged, then would return itself.
  ///
  /// \param other: The object to merge with this
  ///
  /// \return Returns the result of the abstract object.
  abstract_object_pointert
  abstract_object_merge(const abstract_object_pointert &other) const;

  /// To detect the cases where the base merge is sufficient to do a merge
  /// We can't do if this->is_bottom() since we want the specific
  ///
  /// \param other: the object being merged with
  ///
  /// \return Returns true if the base class is capable of doing
  ///         a complete merge
  bool should_use_base_merge(const abstract_object_pointert &other) const;

  /// Create a new abstract object that is the result of the merge, unless
  /// the object would be unchanged, then would return itself.
  ///
  /// \param other: The object to merge with this
  /// \param widen_mode: Indicates if this is a widening merge
  ///
  /// \return Returns the result of the merge.
  virtual abstract_object_pointert merge(
    const abstract_object_pointert &other,
    const widen_modet &widen_mode) const;

  /// Helper function for base meet. Two cases: return itself (if trivially
  /// contained in other); return BOTTOM otherwise.
  /// \param other pointer to the other object
  /// \return the resulting object
  abstract_object_pointert
  abstract_object_meet(const abstract_object_pointert &other) const;

  /// Helper function to decide if base meet implementation should be used
  /// \param other pointer to the other object to meet
  /// \return true if base implementation would yield the most precise
  /// abstraction anyway
  bool should_use_base_meet(const abstract_object_pointert &other) const;

  // The one exception is merge in descendant classes, which needs this
  void set_top()
  {
    top = true;
    this->set_top_internal();
  }
  void set_not_top()
  {
    top = false;
    this->set_not_top_internal();
  }
  void set_not_bottom()
  {
    bottom = false;
  }
};

struct abstract_hashert
{
  typedef abstract_object_pointert argument_typet;
  typedef std::size_t result_typet;
  result_typet operator()(argument_typet const &s) const noexcept
  {
    return s->internal_hash();
  }
};

struct abstract_equalert
{
  typedef abstract_object_pointert argument_typet;
  typedef std::size_t result_typet;
  bool operator()(argument_typet const &left, argument_typet const &right) const
    noexcept
  {
    return left->internal_equality(right);
  }
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
