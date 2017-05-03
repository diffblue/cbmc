/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <ostream>

#include "source_location.h"
#include "file_util.h"
#include "prefix.h"

/*******************************************************************\

Function: source_locationt::as_string

  Inputs: print_cwd, print the absolute path to the file

 Outputs:

 Purpose:

\*******************************************************************/

std::string source_locationt::as_string(bool print_cwd) const
{
  std::string dest;

  const irep_idt &file=get_file();
  const irep_idt &line=get_line();
  const irep_idt &column=get_column();
  const irep_idt &function=get_function();
  const irep_idt &bytecode=get_java_bytecode_index();

  if(!file.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="file ";
    if(print_cwd)
      dest+=
        concat_dir_file(id2string(get_working_directory()), id2string(file));
    else
      dest+=id2string(file);
  }
  if(!line.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="line "+id2string(line);
  }
  if(!column.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="column "+id2string(column);
  }
  if(!function.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="function "+id2string(function);
  }
  if(!bytecode.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="bytecode_index "+id2string(bytecode);
  }

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
  if(source_location.is_nil())
    return out;
  out << source_location.as_string();
  return out;
}
