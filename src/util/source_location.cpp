/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "source_location.h"

#include "prefix.h"

#include <filesystem>
#include <ostream>

bool source_locationt::is_built_in(const std::string &s)
{
  std::string built_in1 = "<built-in-"; // "<built-in-additions>";
  std::string built_in2 = "<builtin-";  // "<builtin-architecture-strings>";
  return has_prefix(s, built_in1) || has_prefix(s, built_in2);
}

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
    if(!dest.empty())
      dest+=' ';
    dest+="file ";
    if(print_cwd)
    {
      dest += std::filesystem::path(id2string(get_working_directory()))
                .append(id2string(file))
                .string();
    }
    else
      dest+=id2string(file);
  }
  if(!line.empty())
  {
    if(!dest.empty())
      dest+=' ';
    dest+="line "+id2string(line);
  }
  if(!column.empty())
  {
    if(!dest.empty())
      dest+=' ';
    dest+="column "+id2string(column);
  }
  if(!function.empty())
  {
    if(!dest.empty())
      dest+=' ';
    dest+="function "+id2string(function);
  }
  if(!bytecode.empty())
  {
    if(!dest.empty())
      dest+=' ';
    dest+="bytecode-index "+id2string(bytecode);
  }

  return dest;
}

void source_locationt::merge(const source_locationt &from)
{
  for(const auto &irep_entry : from.get_named_sub())
  {
    if(get(irep_entry.first).empty())
      set(irep_entry.first, irep_entry.second);
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

  return std::filesystem::path(id2string(get_working_directory()))
    .append(file)
    .string();
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
