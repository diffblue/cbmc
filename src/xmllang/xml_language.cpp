/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>
#include <fstream>

#include "xml_language.h"
#include "xml_parser.h"
#include "xml_typecheck.h"

/*******************************************************************\

Function: xml_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void xml_languaget::modules_provided(std::set<std::string> &modules)
{
}

/*******************************************************************\

Function: xml_languaget::preprocess

  Inputs:

 Outputs:

 Purpose: preprocessing

\*******************************************************************/

bool xml_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  return true;
}
             
/*******************************************************************\

Function: xml_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  // store the path

  parse_path=path;

  // parsing

  xml_parser.clear();
  xml_parser.filename=path;
  xml_parser.in=&instream;
  xml_parser.set_message_handler(message_handler);

  bool result=yyxmlparse();

  // save result
  xml_parse_tree.swap(xml_parser.parse_tree);

  // save some memory
  xml_parser.clear();

  return result;
}
             
/*******************************************************************\

Function: xml_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_languaget::typecheck(
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  return xml_typecheck(
    xml_parse_tree, context, module, message_handler);
}

/*******************************************************************\

Function: xml_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_languaget::final(
  contextt &context,
  message_handlert &message_handler)
{
  return false;
}

/*******************************************************************\

Function: xml_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void xml_languaget::show_parse(std::ostream &out)
{
  out << xml_parse_tree.element;
}

/*******************************************************************\

Function: new_xml_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_xml_language()
{
  return new xml_languaget;
}

/*******************************************************************\

Function: xml_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_languaget::from_expr(const exprt &expr, std::string &code,
                              const namespacet &ns)
{
  return true;
}

/*******************************************************************\

Function: xml_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool xml_languaget::from_type(const typet &type, std::string &code,
                              const namespacet &ns)
{
  return true;
}

/*******************************************************************\

Function: xml_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
                         
bool xml_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  messaget message(message_handler);
  message.error("not yet implemented");
  return true;
}

/*******************************************************************\

Function: xml_languaget::~xml_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

xml_languaget::~xml_languaget()
{
}
