/*******************************************************************\
 
Module: Convert goto functions to binary format and back (with irep
        hashing)
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#include "goto_function_serialization.h"
#include "goto_program_serialization.h"

/*******************************************************************\
 
Function: goto_function_serializationt::convert
 
  Inputs: goto_function and an xml node 
 
 Outputs: none
 
 Purpose: takes a goto_function and outputs the according serialization 
 
\*******************************************************************/

void goto_function_serializationt::convert( 
  const goto_functionst::goto_functiont& function, 
  std::ostream &out)
{
  if (function.body_available)
    gpconverter.convert(function.body, out);
}

/*******************************************************************\
 
Function: goto_function_serializationt::convert
 
  Inputs: xml structure and a goto_function to fill
 
 Outputs: none
 
 Purpose: reconstructs a goto_function from a serialized stream
 
\*******************************************************************/
void goto_function_serializationt::convert( 
  std::istream &in, 
  irept &funsymb)
{   
  gpconverter.convert(in, funsymb);  
  // don't forget to fix the functions type via the symbol table!
}
