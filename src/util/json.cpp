/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "json.h"

const jsont jsont::null_json_object(jsont::J_NULL);

/*******************************************************************\

Function: jsont::escape_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void jsont::escape_string(const std::string &src, std::ostream &out)
{
  for(std::string::const_iterator
      it=src.begin(); it!=src.end(); it++)
  {
    switch(*it)
    {
    case '\\':
    case '"':
      out << '\\';
      out << *it;
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
      out << *it;
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
  case J_STRING:
    out << '"';
    escape_string(value, out);
    out << '"';
    break;

  case J_NUMBER:
    out << value;
    break;

  case J_OBJECT:
    out << '{';
    for(objectt::const_iterator o_it=object.begin();
        o_it!=object.end();
        o_it++)
    {
      if(o_it!=object.begin())
        out << ',';

      out << '\n';
      
      for(unsigned i=0; i<((indent+1)*2); i++)
        out << ' ';

      out << '"';
      escape_string(o_it->first, out);
      out << '"';
      out << ": ";
      o_it->second.output_rec(out, indent+1);
    }
    if(!object.empty())
    {
      out << '\n';
      for(unsigned i=0; i<(indent*2); i++)
        out << ' ';
    }
    out << '}';
    break;

  case J_ARRAY:
    out << '[';
    for(arrayt::const_iterator a_it=array.begin();
        a_it!=array.end();
        a_it++)
    {
      if(a_it!=array.begin())
        out << ',';
      out << ' ';
      a_it->output_rec(out, indent+1);
    }
    if(!array.empty()) out << ' ';
    out << ']';
    break;
    
  case J_TRUE: out << "true"; break;
  
  case J_FALSE: out << "false"; break;
  
  case J_NULL: out << "null"; break;
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

