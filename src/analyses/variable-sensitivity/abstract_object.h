/*******************************************************************\

 Module: analyses variable-sensitivity

 Author: Thomas Kiley, thomas.kiley@diffblue.com

 abstract_objectt is the top of the inheritance heirarchy of objects
 used to represent individual variables in the general non-relational
 domain.  It is a two element abstraction (i.e. it is either top or
 bottom).  Within the hierachy of objects under it, child classes are
 more precise abstractions (the converse doesn't hold to avoid
 diamonds and inheriting unnecessary fields).  Thus the common parent
 of two classes is an abstraction capable of representing both.  This
 is important for understanding merge.

 These objects are intended to be used in a copy-on-write style, which
 is why their interface differs a bit from ai_domain_baset's
 modify-in-place style of interface.

 Although these can represent bottom (this variable cannot take any
 value) it is not common for them to do so.

\*******************************************************************/
#ifndef CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
#define CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H

class typet;
class constant_exprt;
class abstract_environmentt;
class namespacet;

#include <util/expr.h>
#include <memory>


#define CLONE \
  virtual abstract_objectt* clone() const override \
  { \
    typedef std::remove_const<std::remove_reference<decltype(*this)>::type \
      >::type current_typet; \
    return new current_typet(*this); \
  } \

#define MERGE(parent_typet) \
  virtual abstract_object_pointert merge( \
    const abstract_object_pointert op, \
    bool &out_any_modifications) override \
  {\
    assert(type()==op->type()); \
    typedef std::remove_const<std::remove_reference<decltype(*this)>::type \
      >::type current_typet; \
    \
    /*Check the supplied parent type is indeed a parent*/ \
    static_assert(std::is_base_of<parent_typet, current_typet>::value, \
      "parent_typet in MERGE must be parent class of the current type"); \
    \
    typedef sharing_ptrt<current_typet> current_type_ptrt; \
    /*Cast the supplied type to the current type to facilitate double dispatch*/ \
    current_type_ptrt n=std::dynamic_pointer_cast<current_typet>(op); \
    current_type_ptrt m=current_type_ptrt(new current_typet(*this)); \
    if (n!= NULL) \
    { \
      out_any_modifications=m->merge_state(current_type_ptrt(new current_typet(*this)), n); \
      return m; \
    } \
    else \
    { \
      return parent_typet::merge( \
        abstract_object_pointert(op), out_any_modifications); \
    } \
  } \

/* Merge is designed to allow different abstractions to be merged
 * gracefully.  There are two real use-cases for this:
 *
 *  1. Having different abstractions for the variable in different
 *     parts of the program.
 *  2. Allowing different domains to write to ambiguous locations
 *     for example, if a stores multiple values (maybe one per
 *     location) with a constant for each, i does not represent one
 *     single value (top, non-unit interval, etc.) and v is something
 *     other than constant, then
 *         a[i] = v
 *     will cause this to happen.
 *
 * To handle this, merge finds the most specific class that is a
 * parent to both classes and generates a new object of that type.
 * The actual state is then merged by merge_state.
 */

template<class T>
using sharing_ptrt=std::shared_ptr<T>;

typedef sharing_ptrt<class abstract_objectt> abstract_object_pointert;

class abstract_objectt
{
public:
  abstract_objectt(const typet &type);
  abstract_objectt(const typet &type, bool top, bool bottom);
  abstract_objectt(const abstract_objectt &old);
  abstract_objectt(const exprt &expr);

  const typet &type() const;
  virtual bool is_top() const;
  virtual bool is_bottom() const;

  // This is both the interface and the base case of the recursion
  // It uses merge state to produce a new object of the most
  // specific common parent type and is thus copy-on-write safe.
  virtual abstract_object_pointert merge(
    const abstract_object_pointert op, bool &out_any_modifications);

  // Interface for transforms
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  virtual exprt to_constant() const;

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const;

  virtual abstract_objectt* clone() const  // Macro is not used as this does not override
  {
    typedef std::remove_const<std::remove_reference<decltype(*this)>::type
      >::type current_typet;
    return new current_typet(*this);
  }

private:      // To enforce copy-on-write these are private and have read-only accessors
  typet t;
  bool bottom;
protected:  // TODO - remove
  bool top;

protected:    // The one exception is merge_state in descendent classes, which needs this
  void make_top() { top=true; }

  // Sets the state of this object
  bool merge_state(
    const abstract_object_pointert op1, const abstract_object_pointert op2);
};

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
