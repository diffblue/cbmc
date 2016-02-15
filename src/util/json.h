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

  inline explicit jsont(kindt _kind):kind(_kind)
  {
  }

  inline jsont(kindt _kind, const std::string &_value):kind(_kind), value(_value)
  {
  }

  typedef std::vector<jsont> arrayt;
  arrayt array;
  
  typedef std::map<std::string, jsont> objectt;
  objectt object;
  
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

  std::string value;

  inline void output(std::ostream &out) const
  {
    output_rec(out, 0);
  }
  
  void swap(jsont &other);
  
  inline static jsont json_true()
  {
    return jsont(J_TRUE);
  }
  
  inline static jsont json_false()
  {
    return jsont(J_FALSE);
  }
  
  inline static jsont json_null()
  {
    return null_json_object;
  }
  
  inline static jsont json_array()
  {
    return jsont(J_ARRAY);
  }
  
  inline static jsont json_object()
  {
    return jsont(J_OBJECT);
  }
  
  inline static jsont json_string(const std::string &value)
  {
    return jsont(J_STRING, value);
  }
  
  inline static jsont json_number(const std::string &value)
  {
    return jsont(J_NUMBER, value);
  }
  
  void clear()
  {
    value.clear();
    kind=J_NULL;
    object.clear();
    array.clear();
  }
  
protected:
  void output_rec(std::ostream &, unsigned indent) const;
  static void escape_string(const std::string &, std::ostream &);

  static const jsont null_json_object;
};

static inline std::ostream & operator << (std::ostream &out, const jsont &src)
{
  src.output(out);
  return out;
}

#endif
