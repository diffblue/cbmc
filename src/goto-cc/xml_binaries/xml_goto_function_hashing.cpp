/*******************************************************************\

Module: Convert goto functions to xml structures and back (with irep
        hashing)

Author: CM Wintersteiger

Date: July 2006

\*******************************************************************/

/// \file
/// Convert goto functions to xml structures and back (with irep hashing)

#include "xml_goto_function_hashing.h"
#include "xml_goto_program_hashing.h"

/// takes a goto_function and creates an according xml structure
/// \par parameters: goto_function and an xml node
/// \return none
void xml_goto_function_convertt::convert(
  const goto_functionst::goto_functiont &function,
  xmlt &xml)
{
  xml_goto_program_convertt gpconverter(ireps_container);
  if(function.body_available)
    gpconverter.convert(function.body, xml);
}

/// constructs the goto_function according to the information in the xml
/// structure.
/// \par parameters: xml structure and a goto_function to fill
/// \return none
void xml_goto_function_convertt::convert(
  const xmlt &xml,
  goto_functionst::goto_functiont &function)
{
  xml_goto_program_convertt gpconverter(ireps_container);
  function.body.clear();
  gpconverter.convert(xml, function.body);
  // don't forget to fix the functions type via the symbol table!
}
