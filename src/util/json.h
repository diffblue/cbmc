/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JSON_H
#define CPROVER_JSON_H

#include <vector>
#include <map>
#include <iosfwd>
#include <string>

class json_objectt;
class json_arrayt;

class jsont
{
public:
  typedef enum { J_STRING, J_NUMBER, J_OBJECT, J_ARRAY,
                 J_TRUE, J_FALSE, J_NULL } kindt;
  kindt kind;
  
  inline bool is_string() const
  {
    return kind==J_STRING;
  }

  inline bool is_number() const
  {
    return kind==J_NUMBER;
  }

  inline bool is_object() const
  {
    return kind==J_OBJECT;
  }

  inline bool is_array() const
  {
    return kind==J_ARRAY;
  }

  inline bool is_true() const
  {
    return kind==J_TRUE;
  }

  inline bool is_false() const
  {
    return kind==J_FALSE;
  }

  inline bool is_null() const
  {
    return kind==J_NULL;
  }

  inline jsont():kind(J_NULL)
  {
  }

  inline void output(std::ostream &out) const
  {
    output_rec(out, 0);
  }
  
  void swap(jsont &other);
  
  inline static jsont json_boolean(bool value)
  {
    return jsont(value?J_TRUE:J_FALSE);
  }
  
  void clear()
  {
    value.clear();
    kind=J_NULL;
    object.clear();
    array.clear();
  }
  
  inline json_arrayt &make_array();
  inline json_objectt &make_object();
  
  // this presumes that this is an object
  inline const jsont &operator[](const std::string &key) const
  {
    objectt::const_iterator it=object.find(key);
    if(it==object.end())
      return null_json_object;
    else
      return it->second;
  }
  
protected:
  void output_rec(std::ostream &, unsigned indent) const;
  static void escape_string(const std::string &, std::ostream &);

  static const jsont null_json_object;

  inline explicit jsont(kindt _kind):kind(_kind)
  {
  }

  inline jsont(kindt _kind, const std::string &_value):kind(_kind), value(_value)
  {
  }

public:
  // should become protected  
  typedef std::vector<jsont> arrayt;
  arrayt array;
  
  typedef std::map<std::string, jsont> objectt;
  objectt object;
  
  std::string value;
};

static inline std::ostream & operator << (std::ostream &out, const jsont &src)
{
  src.output(out);
  return out;
}

class json_arrayt:public jsont
{
public:
  json_arrayt():jsont(J_ARRAY)
  {
  }
  
  inline void resize(std::size_t size)
  {
    array.resize(size);
  }
  
  std::size_t size() const
  {
    return array.size();
  }

  inline jsont &push_back(const jsont &json)
  {
    array.push_back(json);
    return static_cast<jsont &>(array.back());
  }

  inline jsont &push_back()
  {
    array.push_back(jsont());
    return static_cast<jsont &>(array.back());
  }
};

class json_stringt:public jsont
{
public:
  explicit json_stringt(const std::string &_value):
    jsont(J_STRING, _value)
  {
  }
};

class json_numbert:public jsont
{
public:
  explicit json_numbert(const std::string &_value):
    jsont(J_NUMBER, _value)
  {
  }
};

class json_objectt:public jsont
{
public:
  json_objectt():jsont(J_OBJECT)
  {
  }

  inline jsont &operator[](const std::string &key)
  {
    return object[key];
  }

  inline const jsont &operator[](const std::string &key) const
  {
    objectt::const_iterator it=object.find(key);
    if(it==object.end())
      return null_json_object;
    else
      return it->second;
  }
};

class json_truet:public jsont
{
public:
  json_truet():jsont(J_TRUE) { }
};

class json_falset:public jsont
{
public:
  json_falset():jsont(J_TRUE) { }
};

class json_nullt:public jsont
{
public:
  json_nullt():jsont(J_NULL) { }
};

json_arrayt &jsont::make_array()
{
  kind=J_ARRAY;
  return static_cast<json_arrayt &>(*this);
}

json_objectt &jsont::make_object()
{
  kind=J_OBJECT;
  return static_cast<json_objectt &>(*this);
}

#endif
