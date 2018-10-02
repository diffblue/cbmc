/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "xml.h"

#include <ostream>

#include "exception_utils.h"
#include "string2int.h"

void xmlt::clear()
{
  data.clear();
  name.clear();
  attributes.clear();
  elements.clear();
}

void xmlt::swap(xmlt &xml)
{
  xml.data.swap(data);
  xml.attributes.swap(attributes);
  xml.elements.swap(elements);
  xml.name.swap(name);
}

void xmlt::output(std::ostream &out, unsigned indent) const
{
  // 'name' needs to be set, or we produce mal-formed
  // XML.

  if(name=="")
    return;

  do_indent(out, indent);

  out << '<' << name;

  for(const auto &attribute : attributes)
  {
    // it.first needs to be non-empty
    if(attribute.first.empty())
      continue;
    out << ' ' << attribute.first
        << '=' << '"';
    escape_attribute(attribute.second, out);
    out << '"';
  }

  if(elements.empty() && data.empty())
  {
    out << "/>" << "\n";
    return;
  }

  out << '>';

  if(elements.empty())
    escape(data, out);
  else
  {
    out << "\n";

    for(const auto &element : elements)
      element.output(out, indent+2);

    do_indent(out, indent);
  }

  out << '<' << '/' << name << '>' << "\n";
}

/// escaping for XML elements
void xmlt::escape(const std::string &s, std::ostream &out)
{
  for(const auto ch : s)
  {
    switch(ch)
    {
    case '&':
      out << "&amp;";
      break;

    case '<':
      out << "&lt;";
      break;

    case '>':
      out << "&gt;";
      break;

    case '\r':
      break; // drop!

    case '\n':
      out << '\n';
      break;

    default:
      // &#0; isn't allowed, but what shall we do?
      if((ch>=0 && ch<' ') || ch==127)
        out << "&#"+std::to_string((unsigned char)ch)+";";
      else
        out << ch;
    }
  }
}

/// escaping for XML attributes, assuming that double quotes " are used
/// consistently, not single quotes
void xmlt::escape_attribute(const std::string &s, std::ostream &out)
{
  for(const auto ch : s)
  {
    switch(ch)
    {
    case '&':
      out << "&amp;";
      break;

    case '<':
      out << "&lt;";
      break;

    case '>':
      out << "&gt;";
      break;

    case '"':
      out << "&quot;";
      break;

    default:
      // &#0; isn't allowed, but what shall we do?
      if((ch>=0 && ch<' ') || ch==127)
        out << "&#"+std::to_string((unsigned char)ch)+";";
      else
        out << ch;
    }
  }
}

void xmlt::do_indent(std::ostream &out, unsigned indent)
{
  out << std::string(indent, ' ');
}

xmlt::elementst::const_iterator xmlt::find(const std::string &name) const
{
  for(elementst::const_iterator it=elements.begin();
      it!=elements.end();
      it++)
    if(it->name==name)
      return it;

  return elements.end();
}

xmlt::elementst::iterator xmlt::find(const std::string &name)
{
  for(elementst::iterator it=elements.begin();
      it!=elements.end();
      it++)
    if(it->name==name)
      return it;

  return elements.end();
}

void xmlt::set_attribute(
  const std::string &attribute,
  unsigned value)
{
  set_attribute(attribute, std::to_string(value));
}

void xmlt::set_attribute(
  const std::string &attribute,
  unsigned long value)
{
  set_attribute(attribute, std::to_string(value));
}

void xmlt::set_attribute(
  const std::string &attribute,
  unsigned long long value)
{
  set_attribute(attribute, std::to_string(value));
}

void xmlt::set_attribute(
  const std::string &attribute,
  const std::string &value)
{
  if((value[0]=='\"' && value[value.size()-1]=='\"') ||
      (value[0]=='\'' && value[value.size()-1]=='\''))
  {
    attributes[attribute]=value.substr(1, value.size()-2);
  }
  else
  {
    attributes[attribute]=value;
  }
}

/// takes a string and unescapes any xml style escaped symbols
/// \par parameters: a string
/// \return the unescaped string
std::string xmlt::unescape(const std::string &str)
{
  std::string result("");

  result.reserve(str.size());

  for(std::string::const_iterator it=str.begin();
      it!=str.end();
      it++)
  {
    if(*it=='&')
    {
      std::string tmp;
      it++;

      while(it!=str.end() && *it!=';')
        tmp+=*it++;

      if(tmp=="gt")
        result+='>';
      else if(tmp=="lt")
        result+='<';
      else if(tmp=="amp")
        result+='&';
      else if(tmp[0]=='#' && tmp[1]!='x')
      {
        char c=unsafe_string2int(tmp.substr(1, tmp.size()-1));
        result+=c;
      }
      else
        throw deserialization_exceptiont("unknown XML escape code: " + tmp);
    }
    else
      result+=*it;
  }

  return result;
}
