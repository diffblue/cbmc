/*******************************************************************\

Module: Serializer

Author: Nathan.Phillips@diffblue.com

Purpose: Generic serialization of object hierarchies.

\*******************************************************************/

#ifndef CPROVER_UTIL_SERIALIZER_H
#define CPROVER_UTIL_SERIALIZER_H

#include <utility>
#include <string>
#include <functional>
#include <vector>
#include <set>
#include <map>
#include <cstdint>
#include <cassert>
#ifdef USE_BOOST
#include <boost/bimap.hpp>
#endif


/*******************************************************************\

Class: serializer_traitst

Purpose:
  A base class for classes that define traits that can be attached to a
  serializer.
  This is used to augment the behaviour of a family of serializers, typically
  by passing data that is required for serializing a particular type of object
  through to a sub-object serialization routine.

\*******************************************************************/
class serializer_traitst
{
public:
  // The virtual destructor ensures sub-classes are disposed correctly.
  virtual ~serializer_traitst()=default;
};


/*******************************************************************\

Class: serializert

Purpose:
  A base class for all serializers.
  This is used to implement serialization by being passed to the serialize
  method of classes to be serialized.
  Defines pure virtual methods for serializing basic types.
  Implements methods for serializing collection types.

\*******************************************************************/
class serializert
{
  /////////////////////////////////////////////////////////////////////////////
  // Section: Data used in this class

private:
  // The serializer for a containing object, if any
  serializert *parent;
  // Whether this serializer is used for reading rather than writing
  bool is_read;
  // Traits attached to this serializer
  serializer_traitst *traits;

  /////////////////////////////////////////////////////////////////////////////
  // Section: Constructors/destructors

protected:
  /*******************************************************************\

  Function: serializert::serializert

  Inputs:
    parent: The serializer for the containing object.
    is_read: Whether this serializer is used for reading rather than writing.

  Outputs:

  Purpose:
    Creates a serializert for a sub-object of a larger serialization.
    This is only called internally by sub-class implementations.

  \*******************************************************************/
  serializert(serializert *parent, bool is_read)
    : parent(parent), is_read(is_read), traits(nullptr)
  {
  }

  /*******************************************************************\

  Function: serializert::serializert

  Inputs:
    is_read: Whether this serializer is used for reading rather than writing.

  Outputs:

  Purpose:
    Creates a serializert.
    This will be exposed externally by sub-class implementations but is not
    itself public.

  \*******************************************************************/
  explicit serializert(bool is_read)
    : parent(nullptr), is_read(is_read), traits(nullptr)
  {
  }

  // The virtual destructor ensures sub-classes are disposed correctly.
  virtual ~serializert()=default;

  /////////////////////////////////////////////////////////////////////////////
  // Section: Accessors

public:
  /*******************************************************************\

  Function: serializert::is_for_reading

  Inputs:

  Outputs:
    Whether this serializer is used for reading rather than writing.

  Purpose:
    Gets whether this serializer is used for reading rather than writing.

  \*******************************************************************/
  bool is_for_reading() { return is_read; }

  /*******************************************************************\

  Function: serializert::get_traits

  Template parameters:
    traitst:
      The type of traits to return. Must be derived from serializer_traitst

  Inputs:

  Outputs:
    A reference to traits attached to this serializer or one of its parents of
    type traitst.

  Exceptions:
    std::logic_error:
      If there were no traits of type traitst attached to this serializer or
      one of its parents

  Purpose:
    Gets traits attached to this serializer of a specific type.

  \*******************************************************************/
  template<typename traitst>
  traitst &get_traits() const
  {
    traitst * result=dynamic_cast<traitst *>(traits);
    if(result!=nullptr)
      return *result;
    assert(parent!=nullptr);  // In release build allow undefined behaviour
    return parent->get_traits<traitst>();
  }

  /*******************************************************************\

  Function: serializert::set_traits

  Inputs:
    traits:
      Traits to attach to this serializer

  Outputs:

  Exceptions:
    std::logic_error:
      If there were already traits attached to this serializer

  Purpose:
    Sets traits attached to this serializer.

  \*******************************************************************/
  void set_traits(serializer_traitst &serializer_traits)
  {
    assert(traits==nullptr);
    traits=&serializer_traits;
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serialization of basic data types

public:
  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, bool &field)=0;

  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, char &field)=0;

  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, std::string &field)=0;

  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, int32_t &field)=0;

  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, uint32_t &field)=0;

  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, uint64_t &field)=0;

  /*******************************************************************\

  Function: serializert::serialize

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  virtual void serialize(const char *name, float &field)=0;

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing objects that implement a serialize method

protected:
  // This is a non-templated function so that it can be virtual
  // It therefore can't take an object of the type to be serialized
  // Instead it takes a function that writes to such an object
  virtual void serialize_object(
    const char *name,
    std::function<void(serializert &serializer)> serialize)=0;

public:
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    T:
      The type of the field to serialize. Must implement a serialize method.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field.

  \*******************************************************************/
  template<typename T>
  void serialize(const char *name, T &field)
  {
    serialize_object(
      name,
      [&field] (serializert &serializer)
      {
        field.serialize(serializer);
      });
  }

  /*******************************************************************\

  Function: serializert::read_object

  Template parameters:
    T:
      The type of the field to read.
      Must implement a serialize method and have a default constructor.

  Inputs:

  Outputs:
    An object of the type T read from the serializer.

  Purpose:
    Serializes a field.

  \*******************************************************************/
  template<typename T>
  T read_object()
  {
    T result;
    result.serialize(*this);
    return result;
  }

  /*******************************************************************\

  Function: serializert::read_object

  Template parameters:
    T:
      The type of the field to read.
      Must be serializable and have a default constructor.

  Inputs:
    name: The name of the field to serialize.

  Outputs:
    An object of the type T read from the field serializer.

  Purpose:
    Serializes a field.

  \*******************************************************************/
  template<typename T>
  T read_object(const char *name)
  {
    T result;
    serialize(name, result);
    return result;
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing rvalue references

public:
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    T:
      The type of the field to serialize. Must be serializable.

  Inputs:
    name: The name of the field to serialize.
    field: An rvalue reference to the field to serialize.

  Outputs:

  Purpose:
    Serializes a field.
    Since the field is an rvalue reference this override is useful for writing
      temporary objects or reading into temporary objects that store their
      values in a non-temporary.

  \*******************************************************************/
  template<typename T>
  void serialize(const char *name, T &&field)
  {
    serialize(name, static_cast<T &>(field));
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing pairs of serializable values

private:
  /*******************************************************************\

  Class serializable_pairt

  Template parameters:
    pairt:
      The type of the underlying pair to serialize.
      Must have member types first_type and second_type that are serializable.

  Purpose:
    Wraps a pair in a serializable object that removes const from the
    component members. Obviously this should not be used to read into a const
    value but is useful for writing const values such as are found in the
    value_type of maps.

  \*******************************************************************/
  template<typename pairt>
  class serializable_pairt
  {
  private:
    pairt &value;

  public:
    // This allows conversion from pairt
    // NOLINTNEXTLINE(runtime/explicit)
    serializable_pairt(pairt &value)
      : value(value)
    {
    }

    // This is an implicit conversion back to pairt
    operator pairt &() const { return value; }

    void serialize(serializert &serializer)
    {
      serializer.serialize(
        "first",
        const_cast<typename std::remove_const<
          typename pairt::first_type>::type &>(value.first));
      serializer.serialize(
        "second",
        const_cast<typename std::remove_const<
          typename pairt::second_type>::type &>(value.second));
    }
  };

public:
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    firstt: The type of the first element of the pair. Must be serializable.
    secondt: The type of the second element of the pair. Must be serializable.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field of type std::pair<firstt, secondt>.

  \*******************************************************************/
  template<typename firstt, typename secondt>
  void serialize(const char *name, std::pair<firstt, secondt> &field)
  {
    serialize(name, serializable_pairt<std::pair<firstt, secondt>>(field));
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing vectors

public:
  // A helper base class for writing vectors
  class collection_writert
  {
  public:
    virtual bool is_end() const=0;
    virtual void write(serializert &serializer)=0;
  };

  // Virtual function that must be implemented to support reading vectors
  virtual void read_array(
    const char *name,
    std::function<void(serializert &serializer)> read_elt)=0;

  // Virtual function that must be implemented to support writing vectors
  virtual void write_array(
    const char *name, collection_writert &collection_writer)=0;

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing vectors of objects that implement a serialize method

public:
  // A helper class for writing vectors of objects that implement a serialize
  //  method
  template<typename collectiont>
  class serializable_obj_collection_writert:public collection_writert
  {
  public:
    typedef typename collectiont::iterator iteratort;
    typedef typename collectiont::reference referencet;

  private:
    iteratort it;
    iteratort end_it;

  public:
    explicit serializable_obj_collection_writert(collectiont &collection)
      : it(collection.begin()), end_it(collection.end())
    {
    }

    serializable_obj_collection_writert(iteratort it, iteratort end_it)
      : it(it), end_it(end_it)
    {
    }

    bool is_end() const { return it==end_it; }

    void write(serializert &serializer)
    {
      it->serialize(serializer);
      ++it;
    }
  };

public:
  /*******************************************************************\

  Function: serializert::serialize_objects

  Template parameters:
    eltt:
      The type of elements of the vector.
      Must implement a serialize method and have a default constructor.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field of type std::vector<eltt>.
    One can just use serialize instead of serialize_objects, but then each
      object will be wrapped in another object with a single member

  \*******************************************************************/
  template<typename eltt>
  void serialize_objects(const char *name, std::vector<eltt> &field)
  {
    if(is_read)
    {
      read_array(
        name,
        [&field] (serializert &serializer)
        {
          field.emplace_back();
          field.back().serialize(serializer);
        });
    }
    else
    {
      serializable_obj_collection_writert<std::vector<eltt>> writer(field);
      write_array(name, writer);
    }
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing vectors of serializable values

protected:
  // A helper class for writing vectors of serializable objects (wrapped in a
  //  value field)
  template<typename collectiont>
  class serializable_collection_writert:public collection_writert
  {
  public:
    typedef typename collectiont::iterator iteratort;
    typedef typename collectiont::reference referencet;

  private:
    iteratort it;
    iteratort end_it;

  public:
    explicit serializable_collection_writert(collectiont &collection)
      : it(collection.begin()), end_it(collection.end())
    {
    }

    serializable_collection_writert(iteratort it, iteratort end_it)
      : it(it), end_it(end_it)
    {
    }

    bool is_end() const { return it==end_it; }

    void write(serializert &serializer)
    {
      serializer.serialize("value", *it);
      ++it;
    }
  };

public:
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    eltt:
      The type of elements of the vector.
      Must be serializable and have a default constructor.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field of type std::vector<eltt>.

  \*******************************************************************/
  template<typename eltt>
  void serialize(const char *name, std::vector<eltt> &field)
  {
    if(is_read)
    {
      read_array(
        name,
        [&field] (serializert &serializer)
      {
        field.emplace_back();
        serializer.serialize("value", field.back());
      });
    }
    else
    {
      serializable_collection_writert<std::vector<eltt>> writer(field);
      write_array(name, writer);
    }
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing sets of serializable values

public:
  /*******************************************************************\

  Function: serializert::serialize_set

  Template parameters:
    sett:
      The type of set to be serialized.
      Must have a member type value_type that is serializable and can be
        inserted into the set.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.
    create_elt: A function that returns new set elements.

  Outputs:

  Purpose:
    Serializes a set field.

  \*******************************************************************/
  template<typename sett>
  void serialize_set(
    const char *name,
    sett &field,
    const std::function<typename sett::value_type()> &create_elt)
  {
    if(is_read)
    {
      read_array(
        name,
        [&field, &create_elt](serializert &serializer)
      {
        typename sett::value_type elt=create_elt();
        serializer.serialize("value", elt);
        field.insert(elt);
      });
    }
    else
    {
      serializable_collection_writert<sett> writer(field);
      write_array(name, writer);
    }
  }

private:
  /*******************************************************************\

  Function: serializert::serialize_set

  Template parameters:
    sett:
      The type of set to be serialized.
      Must have a member type value_type that is serializable, has a default
        constructor and can be inserted into the set.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Helper function to serialize a set field.

  \*******************************************************************/
  template<typename sett>
  void serialize_set(const char *name, sett &field)
  {
    serialize_set(name, field, [] () { return typename sett::value_type(); });
  }

public:
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    eltt:
      The type of elements of the set.
      Must be serializable and have a default constructor.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field of type std::set<eltt>.

  \*******************************************************************/
  template<typename eltt>
  void serialize(const char *name, std::set<eltt> &field)
  {
    serialize_set(name, field);
  }

  /////////////////////////////////////////////////////////////////////////////
  // Section: Serializing maps of serializable values

private:
  // This helper function can serialize any type of map (mapt) that has member
  //  types key_type, mapped_type, value_type and reference, an insert method
  //  that takes std::pair<mapt::key_type, mapt::mapped_type> and can be
  //  enumerated to get elements of type mapt::reference from which a
  //  serializable_pairt<mapt::value_type> can be created.
  template<typename mapt>
  void serialize_map(const char *name, mapt &field)
  {
    if(is_read)
    {
      read_array(
        name,
        [&field](serializert &serializer)
      {
        typedef std::pair<typename mapt::key_type, typename mapt::mapped_type>
          pairt;
        pairt key_value_pair;
        serializable_pairt<pairt> wrapper(key_value_pair);
        wrapper.serialize(serializer);
        field.insert(key_value_pair);
      });
    }
    else
    {
      typedef serializable_pairt<typename mapt::value_type> wrappert;
      std::vector<wrappert> wrapper_vector;
      for(typename mapt::reference elt : field)
        wrapper_vector.emplace_back(elt);
      serializable_obj_collection_writert<std::vector<wrappert>>
        writer(wrapper_vector);
      write_array(name, writer);
    }
  }

public:
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    keyt: The type of keys of the map. Must be serializable.
    valuet: The type of values of the map. Must be serializable.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field of type std::map<keyt, valuet>.

  \*******************************************************************/
  template<typename keyt, typename valuet>
  void serialize(const char *name, std::map<keyt, valuet> &field)
  {
    serialize_map(name, field);
  }

#ifdef USE_BOOST
  /*******************************************************************\

  Function: serializert::serialize

  Template parameters:
    keyt: The type of keys of the map. Must be serializable.
    valuet: The type of values of the map. Must be serializable.

  Inputs:
    name: The name of the field to serialize.
    field: The field to serialize.

  Outputs:

  Purpose:
    Serializes a field of type boost::bimap<keyt, valuet>.

  \*******************************************************************/
  template<typename keyt, typename valuet>
  void serialize(const char *name, boost::bimap<keyt, valuet> &field)
  {
    serialize_map(name, field.left);
  }
#endif
};

#endif
