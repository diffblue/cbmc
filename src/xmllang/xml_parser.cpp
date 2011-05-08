/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdlib.h>
#include <string.h>

#include <fstream>

#include "xml_parser.h"

xml_parsert xml_parser;

/*******************************************************************\

Function: parse_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// 'do it all' function
bool parse_xml(
  std::istream &in,
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  xml_parser.clear();
  xml_parser.filename=filename;
  xml_parser.in=&in;
  xml_parser.set_message_handler(message_handler);

  bool result=yyxmlparse();

  // save result
  xml_parser.parse_tree.element.swap(dest);

  // save some memory
  xml_parser.clear();

  return result;  
}

/*******************************************************************\

Function: parse_xml

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

// 'do it all' function
bool parse_xml(
  const std::string &filename,
  message_handlert &message_handler,
  xmlt &dest)
{
  std::ifstream in(filename.c_str());
  
  if(!in) return true;
 
  return parse_xml(in, filename, message_handler, dest);
}

/*******************************************************************\

Function: xml_parsert::unescape

  Inputs: a zero-terminated string

 Outputs: the unescaped string

 Purpose: takes a string and unescapes any xml style escaped symbols

\*******************************************************************/

std::string xml_parsert::unescape(const char *s)
{
  std::string result("");

  result.reserve(strlen(s));

  while(*s!=0)
  {
    if(*s=='&')
    {
      std::string tmp;
      s++;

      while(*s!=0 && *s!=';')
        tmp+=*s++;

      if(tmp=="gt") result+='>';
      else if(tmp=="lt") result+='<';
      else if(tmp=="amp") result+='&';
      else if(tmp[0]=='#' && tmp[1]!='x')
      {
        char c=atoi(tmp.substr(1, tmp.size()-1).c_str());
        result+=c;
      }
      else
        throw "XML escape code not implemented";
    }
    else
      result+=*s;
  }

  return result;
}
