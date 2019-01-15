/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_JSON_H
#define CPROVER_UTIL_JSON_H

#include <vector>
#include <map>
#include <iosfwd>
#include <string>

#include "irep.h"

class json_objectt;
class json_arrayt;

class jsont
{
protected:
  typedef std::vector<jsont> arrayt;
  typedef std::map<std::string, jsont> objectt;

public:
  enum class kindt
  {
    J_STRING,
    J_NUMBER,
    J_OBJECT,
    J_ARRAY,
    J_TRUE,
    J_FALSE,
    J_NULL
  };

  kindt kind;

  bool is_string() const
  {
    return kind==kindt::J_STRING;
  }

  bool is_number() const
  {
    return kind==kindt::J_NUMBER;
  }

  bool is_object() const
  {
    return kind==kindt::J_OBJECT;
  }

  bool is_array() const
  {
    return kind==kindt::J_ARRAY;
  }

  bool is_true() const
  {
    return kind==kindt::J_TRUE;
  }

  bool is_false() const
  {
    return kind==kindt::J_FALSE;
  }

  bool is_null() const
  {
    return kind==kindt::J_NULL;
  }

  jsont():kind(kindt::J_NULL)
  {
  }

  void output(std::ostream &out) const
  {
    output_rec(out, 0);
  }

  void swap(jsont &other);

  static jsont json_boolean(bool value)
  {
    return jsont(value?kindt::J_TRUE:kindt::J_FALSE);
  }

  void clear()
  {
    value.clear();
    kind=kindt::J_NULL;
    object.clear();
    array.clear();
  }

  json_arrayt &make_array();
  json_objectt &make_object();

  // this presumes that this is an object
  const jsont &operator[](const std::string &key) const
  {
    objectt::const_iterator it=object.find(key);
    if(it==object.end())
      return null_json_object;
    else
      return it->second;
  }

  void output_rec(std::ostream &, unsigned indent) const;

  static const jsont null_json_object;

  static void output_key(std::ostream &out, const std::string &key);

  static void
  output_object(std::ostream &out, const objectt &object, unsigned indent);

  std::string value;

protected:
  arrayt array;
  objectt object;

  static void escape_string(const std::string &, std::ostream &);

  explicit jsont(kindt _kind):kind(_kind)
  {
  }

  jsont(kindt _kind, std::string _value) : kind(_kind), value(std::move(_value))
  {
  }

  jsont(kindt _kind, arrayt &&entries) : kind(_kind), array(std::move(entries))
  {
  }

  jsont(kindt _kind, objectt &&objects)
    : kind(_kind), object(std::move(objects))
  {
  }
};

inline std::ostream &operator<<(std::ostream &out, const jsont &src)
{
  src.output(out);
  return out;
}

class json_arrayt:public jsont
{
public:
  json_arrayt():jsont(kindt::J_ARRAY)
  {
  }

  explicit json_arrayt(arrayt &&entries)
    : jsont(kindt::J_ARRAY, std::move(entries))
  {
  }

  void resize(std::size_t size)
  {
    array.resize(size);
  }

  std::size_t size() const
  {
    return array.size();
  }

  bool empty() const
  {
    return array.empty();
  }

  jsont &push_back(const jsont &json)
  {
    array.push_back(json);
    return array.back();
  }

  jsont &push_back(jsont &&json)
  {
    array.push_back(std::move(json));
    return array.back();
  }

  jsont &push_back()
  {
    array.push_back(jsont());
    return array.back();
  }

  template <typename... argumentst>
  void emplace_back(argumentst &&... arguments)
  {
    array.emplace_back(std::forward<argumentst>(arguments)...);
  }

  arrayt::iterator begin()
  {
    return array.begin();
  }

  arrayt::const_iterator begin() const
  {
    return array.begin();
  }

  arrayt::const_iterator cbegin() const
  {
    return array.cbegin();
  }

  arrayt::iterator end()
  {
    return array.end();
  }

  arrayt::const_iterator end() const
  {
    return array.end();
  }

  arrayt::const_iterator cend() const
  {
    return array.cend();
  }

  typedef jsont value_type; // NOLINT(readability/identifiers)
};

class json_stringt:public jsont
{
public:
  explicit json_stringt(std::string _value)
    : jsont(kindt::J_STRING, std::move(_value))
  {
  }

#ifndef USE_STD_STRING
  explicit json_stringt(const irep_idt &_value)
    : jsont(kindt::J_STRING, id2string(_value))
  {
  }
#endif

  /// Constructon from string literal.
  explicit json_stringt(const char *_value) : jsont(kindt::J_STRING, _value)
  {
  }
};

class json_numbert:public jsont
{
public:
  explicit json_numbert(const std::string &_value):
    jsont(kindt::J_NUMBER, _value)
  {
  }
};

class json_objectt:public jsont
{
public:
  using value_type = objectt::value_type;
  using iterator = objectt::iterator;
  using const_iterator = objectt::const_iterator;

  json_objectt():jsont(kindt::J_OBJECT)
  {
  }

  explicit json_objectt(objectt &&objects)
    : jsont(kindt::J_OBJECT, std::move(objects))
  {
  }

  jsont &operator[](const std::string &key)
  {
    return object[key];
  }

  const jsont &operator[](const std::string &key) const
  {
    objectt::const_iterator it=object.find(key);
    if(it==object.end())
      return null_json_object;
    else
      return it->second;
  }

  iterator insert(const_iterator it, value_type value)
  {
    return object.insert(it, std::move(value));
  }

  objectt::iterator find(const std::string &key)
  {
    return object.find(key);
  }

  objectt::const_iterator find(const std::string &key) const
  {
    return object.find(key);
  }

  objectt::iterator begin()
  {
    return object.begin();
  }

  objectt::const_iterator begin() const
  {
    return object.begin();
  }

  objectt::const_iterator cbegin() const
  {
    return object.cbegin();
  }

  objectt::iterator end()
  {
    return object.end();
  }

  objectt::const_iterator end() const
  {
    return object.end();
  }

  objectt::const_iterator cend() const
  {
    return object.cend();
  }
};

class json_truet:public jsont
{
public:
  json_truet():jsont(kindt::J_TRUE) { }
};

class json_falset:public jsont
{
public:
  json_falset():jsont(kindt::J_FALSE) { }
};

class json_nullt:public jsont
{
public:
  json_nullt():jsont(kindt::J_NULL) { }
};

inline json_arrayt &jsont::make_array()
{
  kind=kindt::J_ARRAY;
  return static_cast<json_arrayt &>(*this);
}

inline json_arrayt &to_json_array(jsont &json)
{
  PRECONDITION(json.kind == jsont::kindt::J_ARRAY);
  return static_cast<json_arrayt &>(json);
}

inline const json_arrayt &to_json_array(const jsont &json)
{
  PRECONDITION(json.kind == jsont::kindt::J_ARRAY);
  return static_cast<const json_arrayt &>(json);
}

inline json_objectt &jsont::make_object()
{
  kind=kindt::J_OBJECT;
  return static_cast<json_objectt &>(*this);
}

inline json_objectt &to_json_object(jsont &json)
{
  PRECONDITION(json.kind == jsont::kindt::J_OBJECT);
  return static_cast<json_objectt &>(json);
}

inline const json_objectt &to_json_object(const jsont &json)
{
  PRECONDITION(json.kind == jsont::kindt::J_OBJECT);
  return static_cast<const json_objectt &>(json);
}

#endif // CPROVER_UTIL_JSON_H
