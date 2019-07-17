/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "json.h"

#include <algorithm>
#include <ostream>

const jsont jsont::null_json_object(jsont::kindt::J_NULL);

void jsont::escape_string(const std::string &src, std::ostream &out)
{
  for(const auto &ch : src)
  {
    switch(ch)
    {
    case '\\':
    case '"':
      out << '\\';
      out << ch;
      break;

    case '\b':
      out << "\\b";
      break;

    case '\f':
      out << "\\f";
      break;

    case '\n':
      out << "\\n";
      break;

    case '\r':
      out << "\\r";
      break;

    case '\t':
      out << "\\t";
      break;

    default:
      out << ch;
    }
  }
}

/// Recursive printing of the json object.
/// \param out: The stream object to have the json printed to.
/// \param indent: The indentation level.
void jsont::output_rec(std::ostream &out, unsigned indent) const
{
  switch(kind)
  {
  case kindt::J_STRING:
    out << '"';
    escape_string(value, out);
    out << '"';
    break;

  case kindt::J_NUMBER:
    out << value;
    break;

  case kindt::J_OBJECT:
    out << '{';
    output_object(out, object, indent);
    if(!object.empty())
    {
      out << '\n';
      out << std::string(indent*2, ' ');
    }
    out << '}';
    break;

  case kindt::J_ARRAY:
    out << '[';

    if(array.empty())
      out << ' ';
    else
    {
      for(arrayt::const_iterator a_it=array.begin();
          a_it!=array.end();
          a_it++)
      {
        if(a_it!=array.begin())
          out << ',';

        if(a_it->is_object())
        {
          out << '\n';
          out << std::string((indent+1)*2, ' ');
        }
        else
          out << ' ';

        a_it->output_rec(out, indent+1);
      }

      if(array.back().is_object())
        out << '\n' << std::string(indent*2, ' ');
      else
        out << ' ';
    }

    out << ']';
    break;

  case kindt::J_TRUE: out << "true"; break;

  case kindt::J_FALSE: out << "false"; break;

  case kindt::J_NULL: out << "null"; break;
  }
}

/// Basic handling of the printing of a JSON object.
/// Dispatches to output_rec for most of the hard work.
/// \param out: The stream that the JSON object is to be
///   printed to.
/// \param object: The JSON object.
/// \param indent: The indentation level.
void jsont::output_object(
  std::ostream &out,
  const objectt &object,
  unsigned indent)
{
  for(objectt::const_iterator o_it = object.begin(); o_it != object.end();
      o_it++)
  {
    if(o_it != object.begin())
      out << ',';

    // A JSON object always starts with an opening brace,
    // after which we put a newline.
    out << '\n';

    out << std::string((indent + 1) * 2, ' ');

    jsont::output_key(out, o_it->first);
    o_it->second.output_rec(out, indent + 1);
  }
}

void jsont::output_key(std::ostream &out, const std::string &key)
{
  out << '"';
  jsont::escape_string(key, out);
  out << "\": ";
}

void jsont::swap(jsont &other)
{
  std::swap(other.kind, kind);
  other.array.swap(array);
  other.object.swap(object);
  other.value.swap(value);
}

bool operator==(const jsont &left, const jsont &right)
{
  if(left.kind != right.kind)
    return false;
  switch(left.kind)
  {
  case jsont::kindt::J_NULL:
    return true;
  case jsont::kindt::J_TRUE:
    return true;
  case jsont::kindt::J_FALSE:
    return true;
  case jsont::kindt::J_NUMBER:
    return left.value == right.value;
  case jsont::kindt::J_STRING:
    return left.value == right.value;
  case jsont::kindt::J_ARRAY:
  {
    const auto &left_array = static_cast<const json_arrayt &>(left);
    const auto &right_array = static_cast<const json_arrayt &>(right);
    return left_array.size() == right_array.size() &&
           std::equal(
             left_array.begin(), left_array.end(), right_array.begin());
  }
  case jsont::kindt::J_OBJECT:
  {
    const auto &left_object = static_cast<const json_objectt &>(left);
    const auto &right_object = static_cast<const json_objectt &>(right);
    if(left_object.size() != left_object.size())
      return false;
    return std::all_of(
      left_object.begin(),
      left_object.end(),
      [&](const std::pair<std::string, jsont> &pair) {
        return right_object[pair.first] == pair.second;
      });
  }
  }
  UNREACHABLE;
}
