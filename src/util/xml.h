/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_XML_H
#define CPROVER_UTIL_XML_H

#include <list>
#include <map>
#include <string>
#include <iosfwd>

class xmlt
{
public:
  xmlt()
  { }

  explicit xmlt(const std::string &_name):name(_name)
  { }

  typedef std::list<xmlt> elementst;
  typedef std::map<std::string, std::string> attributest;

  xmlt(std::string &&_name, attributest &&_attributes, elementst &&_elements)
    : name(std::move(_name)),
      attributes(std::move(_attributes)),
      elements(std::move(_elements))
  {
  }

  std::string name, data;

  attributest attributes;
  elementst elements;

  elementst::const_iterator find(const std::string &key) const;
  elementst::iterator find(const std::string &key);

  void set_attribute(
    const std::string &attribute,
    unsigned value);

  void set_attribute(
    const std::string &attribute,
    unsigned long value);

  void set_attribute(
    const std::string &attribute,
    unsigned long long value);

  void set_attribute(
    const std::string &attribute,
    const std::string &value);

  std::string get_attribute(
    const std::string &attribute) const
  {
    attributest::const_iterator i=attributes.find(attribute);
    if(i!=attributes.end())
      return i->second;
    return "";
  }

  void set_attribute_bool(
    const std::string &attribute,
    bool value)
  {
    set_attribute(attribute, value?"true":"false");
  }

  bool get_attribute_bool(const std::string &attribute) const
  {
    attributest::const_iterator i=attributes.find(attribute);
    if(i!=attributes.end())
      return (i->second=="true");
    return false;
  }

  std::string get_element(const std::string &element) const
  {
    elementst::const_iterator i=find(element);
    if(i!=elements.end())
      return i->data;
    return "";
  }

  xmlt &new_element(const std::string &key)
  {
    elements.push_back(xmlt());
    elements.back().name = key;
    return elements.back();
  }

  xmlt &new_element(const xmlt &xml)
  {
    elements.push_back(xml);
    return elements.back();
  }

  xmlt &new_element()
  {
    elements.push_back(xmlt());
    return elements.back();
  }

  void swap(xmlt &xml);
  void clear();

  void output(
    std::ostream &out,
    unsigned indent=0) const;

  static void escape(const std::string &s, std::ostream &out);
  static std::string unescape(const std::string &s);

  static void escape_attribute(const std::string &s, std::ostream &out);

protected:
  static void do_indent(
    std::ostream &out,
    unsigned indent);
};

inline std::ostream &operator<<(
  std::ostream &out,
  const xmlt &xml)
{
  xml.output(out);
  return out;
}

#endif // CPROVER_UTIL_XML_H
