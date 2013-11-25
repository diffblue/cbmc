/*******************************************************************\
 
Module: Convert goto functions to xml structures and back (with irep
        hashing)
 
Author: CM Wintersteiger
 
Date: July 2006
 
\*******************************************************************/

#include "xml_goto_function_hashing.h"
#include "xml_goto_program_hashing.h"

/*******************************************************************\
 
Function: xml_goto_function_convertt::convert
 
  Inputs: goto_function and an xml node 
 
 Outputs: none
 
 Purpose: takes a goto_function and creates an according xml structure 
 
\*******************************************************************/

void 
xml_goto_function_convertt::convert( const goto_functionst::goto_functiont& function, xmlt& xml)
{
  xml_goto_program_convertt gpconverter(ireps_container);
  if (function.body_available)
    gpconverter.convert(function.body, xml);
}

/*******************************************************************\
 
Function: xml_goto_function_convertt::convert
 
  Inputs: xml structure and a goto_function to fill
 
 Outputs: none
 
 Purpose: constructs the goto_function according to the information 
          in the xml structure.
 
\*******************************************************************/

void 
xml_goto_function_convertt::convert( const xmlt& xml, goto_functionst::goto_functiont& function)
{
  xml_goto_program_convertt gpconverter(ireps_container);
  function.body.clear();
  gpconverter.convert(xml, function.body);
  function.body_available = function.body.instructions.size()>0;
  // don't forget to fix the functions type via the symbol table!
}
