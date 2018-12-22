/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "source_location.h"

#include <ostream>

#include "file_util.h"

/// \par parameters: print_cwd, print the absolute path to the file
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
    dest+="bytecode-index "+id2string(bytecode);
  }

  return dest;
}

void source_locationt::merge(const source_locationt &from)
{
  forall_named_irep(it, from.get_named_sub())
  {
    if(get(it->first).empty())
      set(it->first, it->second);
  }
}

/// Get a path to the file, including working directory.
/// \return Full path unless the file name is empty or refers
///   to a built-in, in which case {} is returned.
optionalt<std::string> source_locationt::full_path() const
{
  const auto file = id2string(get_file());

  if(file.empty() || is_built_in(file))
    return {};

  return concat_dir_file(id2string(get_working_directory()), file);
}

std::ostream &operator << (
  std::ostream &out,
  const source_locationt &source_location)
{
  if(source_location.is_nil())
    return out;
  out << source_location.as_string();
  return out;
}
