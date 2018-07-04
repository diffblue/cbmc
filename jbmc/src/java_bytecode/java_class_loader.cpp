/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_class_loader.h"

#include <util/suffix.h>

#include <fstream>

#include "java_bytecode_parser.h"

#ifdef _WIN32
#define DIR_SEP "\\"
#else
#define DIR_SEP "/"
#endif

java_bytecode_parse_treet &java_class_loadert::operator()(
  const irep_idt &class_name)
{
  debug() << "Reading class " << class_name << eom;

  // have we got it already?
  auto entry=class_map.find(class_name);

  if(entry!=class_map.end())
    return entry->second; // yes

  // no
  auto &parse_tree = class_map[class_name];
  parse_tree.parsed_class.name=class_name;

  parse_tree.parsed_class.name=class_name;

  const std::string class_file = class_name_to_file(class_name);

  // rummage through list of entries in given order
  for(auto &entry : entries)
  {
    switch(entry.kind)
    {
    case entryt::JAR: // Look in a JAR
      {
        DATA_INVARIANT(entry.jar_file.has_value(), "must have jar_file");
        auto data=entry.jar_file->get_entry(class_file);
        if(!data.has_value())
          break;
          
        debug()
          << "Getting class `" << class_name << "' from jar " << entry.path
          << eom;

        std::istringstream istream(*data);
        java_bytecode_parse(istream, parse_tree, get_message_handler());
        return parse_tree;
      }
    
    case entryt::DIRECTORY: // Look in the given directory
      const std::string full_path =
        entry.path + DIR_SEP + class_file;

      if(std::ifstream(full_path))
      {
        debug()
          << "Getting class `" << class_name << "' from file " << full_path
          << eom;

        java_bytecode_parse(full_path, parse_tree, get_message_handler());
        return parse_tree;
      }
    }
  }

  // Not found or failed to load
  warning() << "failed to load class `" << class_name << '\'' << eom;

  return parse_tree;
}

void java_class_loadert::add_classpath_entry(const std::string &path)
{
  entries.push_back(entryt(path));
  entryt &new_entry=entries.back();

  if(has_suffix(path, ".jar"))
  {
    new_entry.kind=entryt::JAR;
    new_entry.jar_file=jar_filet(path);
  }
  else if(has_suffix(path, DIR_SEP "*"))
  {
    // need to get all the JARs in the directory
    PRECONDITION(false);
  }
  else
  {
    new_entry.kind=entryt::DIRECTORY;
  }
}

std::string java_class_loadert::file_to_class_name(const std::string &file)
{
  std::string result=file;

  // Strip .class. Note that the Java class loader would
  // not do that.
  if(has_suffix(result, ".class"))
    result.resize(result.size()-6);

  // Strip a "./" prefix. Note that the Java class loader
  // would not do that.
  #ifdef _WIN32
  while(has_prefix(result, ".\\"))
    result=std::string(result, 2, std::string::npos);
  #else
  while(has_prefix(result, "./"))
    result=std::string(result, 2, std::string::npos);
  #endif

  // slash to dot
  for(std::string::iterator it=result.begin(); it!=result.end(); it++)
    if(*it=='/')
      *it='.';

  return result;
}

std::string java_class_loadert::class_name_to_file(const irep_idt &class_name)
{
  std::string result=id2string(class_name);

  // dots (package name separators) to slash, depending on OS
  for(std::string::iterator it=result.begin(); it!=result.end(); it++)
    if(*it=='.')
    {
      #ifdef _WIN32
      *it='\\';
      #else
      *it='/';
      #endif
    }

  // add .class suffix
  result+=".class";

  return result;
}
