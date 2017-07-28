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
#include <map>
#include <iosfwd>
#include <algorithm>
#include <goto-programs/goto_program.h>

#include <util/expr.h>


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

  virtual void output(
    std::ostream &out, const class ai_baset &ai, const namespacet &ns) const;

  abstract_object_pointert clone() const
  {
    return abstract_object_pointert(mutable_clone());
  }

  static abstract_object_pointert merge(
    abstract_object_pointert op1,
    abstract_object_pointert op2,
    bool &out_modifications);

  abstract_object_pointert update_last_written_locations(const goto_programt::const_targett &location) const
  {
    internal_abstract_object_pointert clone=mutable_clone();
    clone->last_written_locations.clear();
    clone->last_written_locations.push_back(location);
    return clone;
  }

  abstract_object_pointert update_last_written_locations(const std::vector<goto_programt::const_targett> &locations) const
  {
    internal_abstract_object_pointert clone=mutable_clone();
    clone->last_written_locations.clear();
    clone->last_written_locations=locations;
    return clone;
  }

  // Cheap and dirty diff calculation.
  // Moving to (unordered)_sets would allow reliance on built ins.
  std::vector<goto_programt::const_targett> get_new_location_set(const abstract_object_pointert &other) const
  {
    std::vector<goto_programt::const_targett> locations=this->get_last_written_locations();
    std::vector<goto_programt::const_targett> more_locations=other->get_last_written_locations();

    for(auto add_location:more_locations)
    {
      bool found=false;
      for(auto location:locations)
      {
        if(location->location_number == add_location->location_number)
        {
          found=true;
          break;
        }
      }
      if(found==false)
      {
        locations.push_back(add_location);
      }
    }

    return locations;
  }


  // For mutable
  void set_last_written_locations(const abstract_object_pointert &object)
  {
    last_written_locations.clear();
    for(auto location: object->get_last_written_locations())
    {
      last_written_locations.push_back(location);
    }
  }

  // For mutable
  void set_last_written_locations(goto_programt::const_targett &location)
  {
    last_written_locations.clear();
    last_written_locations.push_back(location);
  }

  std::vector<goto_programt::const_targett> get_last_written_locations() const
  {
    return last_written_locations;
  }

private:
  // To enforce copy-on-write these are private and have read-only accessors
  typet t;
  bool bottom;
  std::vector<goto_programt::const_targett> last_written_locations;

  abstract_object_pointert abstract_object_merge(
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

  bool top;

  // The one exception is merge in descendant classes, which needs this
  void make_top() { top=true; }

  bool should_use_base_merge(const abstract_object_pointert other) const;

  // Sets the state of this object
  virtual abstract_object_pointert merge(abstract_object_pointert other) const;

  template<class keyt>
  static bool merge_maps(
    const std::map<keyt, abstract_object_pointert> &map1,
    const std::map<keyt, abstract_object_pointert> &map2,
    std::map<keyt, abstract_object_pointert> &out_map);
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


#endif // CPROVER_ANALYSES_VARIABLE_SENSITIVITY_ABSTRACT_OBJECT_H
