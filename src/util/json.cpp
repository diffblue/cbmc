/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "json.h"

const jsont jsont::null_json_object(jsont::kindt::J_NULL);

/*******************************************************************\

Function: jsont::escape_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

/*******************************************************************\

Function: jsont::output_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    for(objectt::const_iterator o_it=object.begin();
        o_it!=object.end();
        o_it++)
    {
      if(o_it!=object.begin())
        out << ',';

      out << '\n';

      out << std::string((indent+1)*2, ' ');

      out << '"';
      escape_string(o_it->first, out);
      out << '"';
      out << ": ";
      o_it->second.output_rec(out, indent+1);
    }
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

/*******************************************************************\

Function: jsont::swap

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsont::swap(jsont &other)
{
  std::swap(other.kind, kind);
  other.array.swap(array);
  other.object.swap(object);
  other.value.swap(value);
}
