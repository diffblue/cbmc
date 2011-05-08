/*******************************************************************\
 
Module: Convert goto functions to xml structures and back.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#include <xml_irep.h>

#include "xml_goto_function.h"
#include "xml_goto_program.h"

/*******************************************************************\
 
Function: convert
 
  Inputs: goto_function and an xml node 
 
 Outputs: none
 
 Purpose: takes a goto_function and creates an according xml structure 
 
\*******************************************************************/

void convert( const goto_functionst::goto_functiont& function, xmlt& xml)
{
  if (function.body_available)
    convert(function.body, xml);
}

/*******************************************************************\
 
Function: convert
 
  Inputs: xml structure and a goto_function to fill
 
 Outputs: none
 
 Purpose: constructs the goto_function according to the information 
          in the xml structure.
 
\*******************************************************************/

void convert( const xmlt& xml, goto_functionst::goto_functiont& function)
{
  function.body.clear();
  convert(xml, function.body);
  function.body_available = function.body.instructions.size()>0;
  // don't forget to fix the functions type via the symbol table!
}
