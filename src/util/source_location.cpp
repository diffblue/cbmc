/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "source_location.h"

/*******************************************************************\

Function: source_locationt::as_string

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string source_locationt::as_string() const
{
  std::string dest;

  const irep_idt &file=get_file();
  const irep_idt &line=get_line();
  const irep_idt &column=get_column();
  const irep_idt &function=get_function();

  if(file!="") { if(dest!="") dest+=' '; dest+="file "+id2string(file); }
  if(line!="") { if(dest!="") dest+=' '; dest+="line "+id2string(line); }
  if(column!="") { if(dest!="") dest+=' '; dest+="column "+id2string(column); }
  if(function!="") { if(dest!="") dest+=' '; dest+="function "+id2string(function); }

  return dest;
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator << (
  std::ostream &out,
  const source_locationt &source_location)
{
  if(source_location.is_nil()) return out;

  out << source_location.as_string();
  
  return out;
}

