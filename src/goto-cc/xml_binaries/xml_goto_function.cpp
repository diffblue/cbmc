/*******************************************************************\

Module: Convert goto functions to xml structures and back.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Convert goto functions to xml structures and back.

#include <util/xml_irep.h>

#include "xml_goto_function.h"
#include "xml_goto_program.h"

/// takes a goto_function and creates an according xml structure
/// \par parameters: goto_function and an xml node
/// \return none
void convert(const goto_functionst::goto_functiont &function, xmlt &xml)
{
  if(function.body_available)
    convert(function.body, xml);
}

/// constructs the goto_function according to the information in the xml
/// structure.
/// \par parameters: xml structure and a goto_function to fill
/// \return none
void convert(const xmlt &xml, goto_functionst::goto_functiont &function)
{
  function.body.clear();
  convert(xml, function.body);
  // don't forget to fix the functions type via the symbol table!
}
