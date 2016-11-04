/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>
#include <map>
#include <fstream>

#include <util/suffix.h>
#include <util/prefix.h>
#include <util/config.h>

#include "java_bytecode_parser.h"
#include "java_class_loader.h"
#include "jar_file.h"

/*******************************************************************\

Function: java_class_loadert::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

java_bytecode_parse_treet &java_class_loadert::operator()(
  const irep_idt &class_name)
{
  std::stack<irep_idt> queue;

  // Always require java.lang.Object, as it is the base of
  // internal classes such as array types.
  queue.push("java.lang.Object");
  // java.lang.String
  queue.push("java.lang.String");
  queue.push(class_name);

  while(!queue.empty())
  {
    irep_idt c=queue.top();
    queue.pop();

    // do we have the class already?
    if(class_map.find(c)!=class_map.end())
      continue; // got it already

    debug() << "Reading class " << c << eom;

    java_bytecode_parse_treet &parse_tree=
      get_parse_tree(c);

    // add any dependencies to queue
    for(java_bytecode_parse_treet::class_refst::const_iterator
        it=parse_tree.class_refs.begin();
        it!=parse_tree.class_refs.end();
        it++)
      queue.push(*it);
  }

  return class_map[class_name];
}

/*******************************************************************\

Function: java_class_loadert::get_parse_tree

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

java_bytecode_parse_treet &java_class_loadert::get_parse_tree(
  const irep_idt &class_name)
{
  java_bytecode_parse_treet &parse_tree=class_map[class_name];

  // First check given JAR files
  for(const auto &jf : jar_files)
  {
    read_jar_file(jf);

    const auto &jm=jar_map[jf];

    auto jm_it=jm.entries.find(class_name);

    if(jm_it!=jm.entries.end())
    {
      debug() << "Getting class `" << class_name << "' from JAR "
              << jf << eom;

      std::string data=jar_pool(jf).get_entry(jm_it->second.index);

      std::istringstream istream(data);

      java_bytecode_parse(
        istream,
        parse_tree,
        get_message_handler());

      return parse_tree;
    }
  }

  // See if we can find it in the class path

  for(const auto &cp : config.java.classpath)
  {
    // in a JAR?
    if(has_suffix(cp, ".jar"))
    {
      read_jar_file(cp);

      const auto &jm=jar_map[cp];

      auto jm_it=jm.entries.find(class_name);

      if(jm_it!=jm.entries.end())
      {
        debug() << "Getting class `" << class_name << "' from JAR "
                << cp << eom;

        std::string data=jar_pool(cp).get_entry(jm_it->second.index);

        std::istringstream istream(data);

        java_bytecode_parse(
          istream,
          parse_tree,
          get_message_handler());

        return parse_tree;
      }
    }
    else
    {
      // in a given directory?
      std::string full_path=
        #ifdef _WIN32
        cp+'\\'+class_name_to_file(class_name);
        #else
        cp+'/'+class_name_to_file(class_name);
        #endif

      if(std::ifstream(full_path))
      {
        if(!java_bytecode_parse(
             full_path,
             parse_tree,
             get_message_handler()))
          return parse_tree;
      }
    }
  }

  // not found
  warning() << "failed to load class `" << class_name << '\'' << eom;
  parse_tree.parsed_class.name=class_name;
  return parse_tree;
}

/*******************************************************************\

Function: java_class_loadert::load_entire_jar

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_class_loadert::load_entire_jar(const std::string &file)
{
  read_jar_file(file);

  const auto &jm=jar_map[file];

  jar_files.push_front(file);

  for(const auto &e : jm.entries)
    operator()(e.first);

  jar_files.pop_front();
}

/*******************************************************************\

Function: java_class_loadert::read_jar_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_class_loadert::read_jar_file(const irep_idt &file)
{
  // done already?
  if(jar_map.find(file)!=jar_map.end()) return;

  #ifndef HAVE_LIBZIP
  error() << "no support for reading JAR files configured" << eom;
  return;
  #endif

  jar_filet &jar_file=jar_pool(id2string(file));

  if(!jar_file)
  {
    error() << "failed to open JAR file `" << file << "'" << eom;
    return;
  }

  debug() << "adding JAR file `" << file << "'" << eom;

  auto &jm=jar_map[file];
  std::size_t number_of_files=jar_file.index.size();

  for(std::size_t i=0; i<number_of_files; i++)
  {
    std::string file_name=jar_file.index[i];

    // does it end on .class?
    if(has_suffix(file_name, ".class"))
    {
      irep_idt class_name=file_to_class_name(file_name);

      // record
      jm.entries[class_name].index=i;
    }
  }
}

/*******************************************************************\

Function: java_class_loadert::file_to_class_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    if(*it=='/') *it='.';

  return result;
}

/*******************************************************************\

Function: java_class_loadert::class_name_to_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string java_class_loadert::class_name_to_file(const irep_idt &class_name)
{
  std::string result=id2string(class_name);

  // dots (package name separators) to slash, depending on OS
  for(std::string::iterator it=result.begin(); it!=result.end(); it++)
    if(*it=='.')
      #ifdef _WIN32
      *it='\\';
      #else
      *it='/';
      #endif

  // add .class suffix
  result+=".class";

  return result;
}
