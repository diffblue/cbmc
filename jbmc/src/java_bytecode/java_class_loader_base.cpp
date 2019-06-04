/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_class_loader_base.h"

#include "jar_file.h"
#include "java_bytecode_parser.h"

#include <util/file_util.h>
#include <util/prefix.h>
#include <util/suffix.h>

#include <fstream>

void java_class_loader_baset::add_classpath_entry(const std::string &path)
{
  if(has_suffix(path, ".jar"))
  {
    if(std::ifstream(path).good())
    {
      classpath_entries.push_back(
        classpath_entryt(classpath_entryt::JAR, path));
    }
    else
    {
      warning() << "Warning: failed to access JAR file `" << path << "'" << eom;
    }
  }
  else
  {
    if(is_directory(path))
    {
      classpath_entries.push_back(
        classpath_entryt(classpath_entryt::DIRECTORY, path));
    }
    else
    {
      warning() << "Warning: failed to access directory `" << path << "'"
                << eom;
    }
  }
}

/// Convert a file name to the class name. Java interprets folders as packages,
/// therefore a prefix of `./` is removed if necessary, and all `/` are
/// converted to `.`. For example a class file `./com/diffblue/test.class` is
/// converted to the class name `com.diffblue.test`.
/// \param file: the name of the class file
/// \return the file name converted to Java class name
std::string java_class_loader_baset::file_to_class_name(const std::string &file)
{
  std::string result = file;

  // Strip .class. Note that the Java class loader would
  // not do that.
  if(has_suffix(result, ".class"))
    result.resize(result.size() - 6);

  // Strip a "./" prefix. Note that the Java class loader
  // would not do that.
#ifdef _WIN32
  while(has_prefix(result, ".\\"))
    result = std::string(result, 2, std::string::npos);
#else
  while(has_prefix(result, "./"))
    result = std::string(result, 2, std::string::npos);
#endif

  // slash to dot
  for(std::string::iterator it = result.begin(); it != result.end(); it++)
    if(*it == '/')
      *it = '.';

  return result;
}

/// Convert a class name to a file name, does the inverse of \ref
/// file_to_class_name.
/// \param class_name: the name of the class
/// \return the class name converted to file name
std::string
java_class_loader_baset::class_name_to_jar_file(const irep_idt &class_name)
{
  std::string result = id2string(class_name);

  // dots (package name separators) to slash
  for(std::string::iterator it = result.begin(); it != result.end(); it++)
    if(*it == '.')
      *it = '/';

  // add .class suffix
  result += ".class";

  return result;
}

/// Convert a class name to a file name, with OS-dependent syntax
/// \param class_name: the name of the class
/// \return the class name converted to file name
std::string
java_class_loader_baset::class_name_to_os_file(const irep_idt &class_name)
{
  std::string result = id2string(class_name);

  // dots (package name separators) to slash, depending on OS
  for(std::string::iterator it = result.begin(); it != result.end(); it++)
    if(*it == '.')
    {
#ifdef _WIN32
      *it = '\\';
#else
      *it = '/';
#endif
    }

  // add .class suffix
  result += ".class";

  return result;
}

/// attempt to load a class from a classpath_entry
optionalt<java_bytecode_parse_treet> java_class_loader_baset::load_class(
  const irep_idt &class_name,
  const classpath_entryt &cp_entry)
{
  switch(cp_entry.kind)
  {
  case classpath_entryt::JAR:
    return get_class_from_jar(class_name, cp_entry.path);

  case classpath_entryt::DIRECTORY:
    return get_class_from_directory(class_name, cp_entry.path);
  }

  UNREACHABLE;
}

/// Load class from jar file.
/// \param class_name: name of class to load in Java source format
/// \param jar_file: path of the jar file
/// \return optional value of parse tree, empty if class cannot be loaded
optionalt<java_bytecode_parse_treet>
java_class_loader_baset::get_class_from_jar(
  const irep_idt &class_name,
  const std::string &jar_file)
{
  try
  {
    auto &jar = jar_pool(jar_file);
    auto data = jar.get_entry(class_name_to_jar_file(class_name));

    if(!data.has_value())
      return {};

    debug() << "Getting class '" << class_name << "' from JAR " << jar_file
            << eom;

    std::istringstream istream(*data);
    return java_bytecode_parse(istream, class_name, get_message_handler());
  }
  catch(const std::runtime_error &)
  {
    error() << "failed to open JAR file '" << jar_file << "'" << eom;
    return {};
  }
}

/// Load class from directory.
/// \param class_name: name of class to load in Java source format
/// \param path: directory to load from
/// \return optional value of parse tree, empty if class cannot be loaded
optionalt<java_bytecode_parse_treet>
java_class_loader_baset::get_class_from_directory(
  const irep_idt &class_name,
  const std::string &path)
{
  // Look in the given directory
  const std::string class_file = class_name_to_os_file(class_name);
  const std::string full_path = concat_dir_file(path, class_file);

  if(std::ifstream(full_path))
  {
    debug() << "Getting class '" << class_name << "' from file " << full_path
            << eom;
    return java_bytecode_parse(full_path, class_name, get_message_handler());
  }
  else
    return {};
}
