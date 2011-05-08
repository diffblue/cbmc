/*******************************************************************\
 
Module: Convert goto programs to binary format and back (with irep
        hashing)
 
Author: CM Wintersteiger
 
Date: May 2007
 
\*******************************************************************/

#include <sstream>
#include <irep_serialization.h>

#include "goto_program_irep.h"
#include "goto_program_serialization.h"

/*******************************************************************\
 
Function: goto_program_serializationt::convert
 
  Inputs: goto program and an xml structure to fill
 
 Outputs: none
 
 Purpose: constructs the xml structure according to the goto program
          and the namespace into the given xml object.
 
\*******************************************************************/

void goto_program_serializationt::convert( 
  const goto_programt &goto_program,
  std::ostream &out)
{
  irepcache.push_back(irept());
  ::convert(goto_program, irepcache.back());  
  irepconverter.reference_convert(irepcache.back(), out);  
}

/*******************************************************************\
 
Function: goto_program_serializationt::convert
 
  Inputs: an xml structure and a goto program to fill
 
 Outputs: none
 
 Purpose: constructs the goto program according to the xml structure
          and the namespace into the given goto program object.
 
\*******************************************************************/

void goto_program_serializationt::convert( 
  std::istream &in,
  irept& gprep)
{
  irepconverter.reference_convert(in, gprep);
  // reference is not resolved here! 
}

