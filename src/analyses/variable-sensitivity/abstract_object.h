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



#include <memory>
#include <set>
#include <map>
#include <iosfwd>
#include <algorithm>
#include <stack>

#include <goto-programs/goto_program.h>
#include <util/expr.h>
#include <util/sharing_map.h>

class typet;
class constant_exprt;
class abstract_environmentt;
class namespacet;


#define CLONE \
  virtual internal_abstract_object_pointert mutable_clone() const override \
  { \
    typedef std::remove_const<std::remove_reference<decltype(*this)>::type \
      >::type current_typet; \
    return internal_abstract_object_pointert(new current_typet(*this)); \
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
 * To handle this, merge is dispatched to the first abstract object being
 * merged, which switches based on the type of the other object. If it can
 * merge then it merges, otherwise it calls the parent merge.
 */


template<class T>
using sharing_ptrt=std::shared_ptr<const T>; // NOLINT(*)

typedef sharing_ptrt<class abstract_objectt> abstract_object_pointert;

class abstract_objectt:public std::enable_shared_from_this<abstract_objectt>
{
public:
  explicit abstract_objectt(const typet &type);
  abstract_objectt(const typet &type, bool top, bool bottom);
  abstract_objectt(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns);

  virtual ~abstract_objectt() {}

  const typet &type() const;
  virtual bool is_top() const;
  virtual bool is_bottom() const;

  // Interface for transforms
  abstract_object_pointert expression_transform(
    const exprt &expr,
    const abstract_environmentt &environment,
    const namespacet &ns) const;

  virtual exprt to_constant() const;

  virtual abstract_object_pointert read(
    const abstract_environmentt &env,
    const exprt &specifier,
    const namespacet &ns) const;

  virtual abstract_object_pointert write(
    abstract_environmentt &environment,
    const namespacet &ns,
    const std::stack<exprt> stack,
    const exprt &specifier,
    const abstract_object_pointert value,
    bool merging_write) const;

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const;

  typedef std::set<goto_programt::const_targett> locationst;
  typedef sharing_mapt<irep_idt, abstract_object_pointert, irep_id_hash>
    shared_mapt;
    
  static void dump_map(std::ostream out, const shared_mapt &m);
  static void dump_map_diff(
    std::ostream out, const shared_mapt &m1, const shared_mapt &m2);

  abstract_object_pointert clone() const
  {
    return abstract_object_pointert(mutable_clone());
  }

  /**
   * Determine whether 'this' abstract_object has been modified in comparison
   * to a previous 'before' state.
   * \param before The abstract_object_pointert to use as a reference to
   * compare against
   * \return true if 'this' is considered to have been modified in comparison
   * to 'before', false otherwise.
   */
  virtual bool has_been_modified(const abstract_object_pointert before) const
  {
    // Default implementation, with no other information to go on
    // falls back to relying on copy-on-write and pointer inequality
    // to indicate if an abstract_objectt has been modified
    return this != before.get();
  };

  static abstract_object_pointert merge(
    abstract_object_pointert op1,
    abstract_object_pointert op2,
    bool &out_modifications);

  virtual abstract_object_pointert update_location_context(
    const locationst &locations,
    const bool update_sub_elements) const;

  // Const versions must perform copy-on-write
  abstract_object_pointert make_top() const
  {
    if(is_top())
      return shared_from_this();

    internal_abstract_object_pointert clone = mutable_clone();
    clone->make_top();
    return clone;
  }

  abstract_object_pointert clear_top() const
  {
    if(!is_top())
      return shared_from_this();

    internal_abstract_object_pointert clone = mutable_clone();
    clone->clear_top();
    return clone;
  }

  /**
   * Pure virtual interface required of a client that can apply a copy-on-write
   * operation to a given abstract_object_pointert.
   */
  struct abstract_object_visitort
  {
    virtual abstract_object_pointert visit(
      const abstract_object_pointert element) const = 0;
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
  virtual abstract_object_pointert visit_sub_elements(
    const abstract_object_visitort &visitor) const
  { return shared_from_this(); }

private:
  // To enforce copy-on-write these are private and have read-only accessors
  typet t;
  bool bottom;
  bool top;

  // Hooks to allow a sub-class to perform its own operations on
  // setting/clearing top
  virtual void make_top_internal() {}
  virtual void clear_top_internal() {}

  // Hook for a subclass to perform any additional operations as
  // part of an abstract_object_merge
  virtual abstract_object_pointert abstract_object_merge_internal(
    const abstract_object_pointert other) const;

protected:
  template<class T>
  using internal_sharing_ptrt=std::shared_ptr<T>;

  typedef internal_sharing_ptrt<class abstract_objectt>
    internal_abstract_object_pointert;

  // Macro is not used as this does not override
  virtual internal_abstract_object_pointert mutable_clone() const
  {
    return internal_abstract_object_pointert(new abstract_objectt(*this));
  }

  abstract_object_pointert abstract_object_merge(
    const abstract_object_pointert other) const;

  bool should_use_base_merge(const abstract_object_pointert other) const;

  // Sets the state of this object
  virtual abstract_object_pointert merge(abstract_object_pointert other) const;

  template<class keyt>
  static bool merge_maps(
    const std::map<keyt, abstract_object_pointert> &map1,
    const std::map<keyt, abstract_object_pointert> &map2,
    std::map<keyt, abstract_object_pointert> &out_map);


  template<class keyt, typename hash>
  static bool merge_shared_maps(
    const sharing_mapt<keyt, abstract_object_pointert, hash> &map1,
    const sharing_mapt<keyt, abstract_object_pointert, hash> &map2,
    sharing_mapt<keyt, abstract_object_pointert, hash> &out_map);



  // The one exception is merge in descendant classes, which needs this
  void make_top() { top=true; this->make_top_internal(); }
  void clear_top() { top=false; this->clear_top_internal(); }
};

template<typename keyt>
bool abstract_objectt::merge_maps(
  const std::map<keyt, abstract_object_pointert> &m1,
  const std::map<keyt, abstract_object_pointert> &m2,
  std::map<keyt, abstract_object_pointert> &out_map)
{
  out_map.clear();

  typedef std::map<keyt, abstract_object_pointert> abstract_object_mapt;

  bool modified=false;

  std::vector<std::pair<keyt, abstract_object_pointert>> intersection_set;
  std::set_intersection(
    m1.cbegin(),
    m1.cend(),
    m2.cbegin(),
    m2.cend(),
    std::back_inserter(intersection_set),
    [](
      const std::pair<keyt, abstract_object_pointert> &op1,
      const std::pair<keyt, abstract_object_pointert> &op2)
    {
      return op1.first < op2.first;
    });

  for(const typename abstract_object_mapt::value_type &entry : intersection_set)
  {
    // merge entries

    const abstract_object_pointert &v1=m1.at(entry.first);
    const abstract_object_pointert &v2=m2.at(entry.first);

    bool changes=false;
    abstract_object_pointert v_new=abstract_objectt::merge(v1, v2, changes);


    modified|=changes;

    out_map[entry.first]=v_new;
  }

  return modified;
}

template<typename keyt, typename hash>
bool abstract_objectt::merge_shared_maps(
  const sharing_mapt<keyt, abstract_object_pointert, hash> &m1,
  const sharing_mapt<keyt, abstract_object_pointert, hash> &m2,
  sharing_mapt<keyt, abstract_object_pointert, hash> &out_map)
{
  bool modified=false;

  auto delta_view = m1.get_delta_view(m2, true);

  for(auto &item : delta_view)
  {
    bool changes = false;
    abstract_object_pointert v_new = abstract_objectt::merge(
      item.m, item.other_m, changes);
    if (changes)
    {
      modified = true;
      out_map[item.k] = v_new;
    }
  }

  return modified;
}

#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
