/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stack>
#include <map>

#include <util/suffix.h>
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

  // in a JAR?
  class_jar_mapt::const_iterator c_j_it=
    class_jar_map.find(class_name);
  
  if(c_j_it!=class_jar_map.end())
  {
    std::vector<char> data;

    if(get_jar_entry(
      c_j_it->second.jar_file_name.c_str(), c_j_it->second.index, data))
      return parse_tree; // error
  
    std::istringstream istream(data.data());
    
    java_bytecode_parse(
      istream,
      parse_tree,
      get_message_handler());
      
    return parse_tree;
  }

  // in a given class file?
  class_file_mapt::const_iterator c_f_it=
    class_file_map.find(class_name);
  
  if(c_f_it!=class_file_map.end())
  {
    java_bytecode_parse(
      id2string(c_f_it->second),
      parse_tree,
      get_message_handler());
    
    return parse_tree;
  }
  
  // See if we can find a class file in class path
  
  for(std::list<std::string>::const_iterator
      cp_it=config.java.class_path.begin();
      cp_it!=config.java.class_path.end();
      cp_it++)
  {
    std::string full_path;
    
    #ifdef _WIN32
    full_path=*cp_it+'\\'+id2string(class_name)+".class";
    #else
    full_path=*cp_it+'/'+id2string(class_name)+".class";
    #endif
  
    if(!java_bytecode_parse(
         full_path,
         parse_tree,
         get_message_handler()))
      return parse_tree;
  }
    
  // not found
  warning() << "failed to load class `" << class_name << '\'' << eom;
  parse_tree.parsed_class.name=class_name;
  return parse_tree;  
}

/*******************************************************************\

Function: java_class_loadert::add_class_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_class_loadert::add_class_file(const irep_idt &file)
{
  class_file_map[file_to_class_name(id2string(file))]=file;
}

/*******************************************************************\

Function: java_class_loadert::add_jar_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_class_loadert::add_jar_file(const irep_idt &file)
{
  std::vector<std::string> entries;
  
  if(get_jar_index(file.c_str(), entries))
  {
    error() << "failed to open JAR file `" << file << "'" << eom;
    return;
  }
  
  std::size_t number_of_files=entries.size();
  
  for(std::size_t index=0; index<number_of_files; index++)
  {
    std::string file_name=entries[index];
    
    // does it end on .class?
    if(has_suffix(file_name, ".class"))
    {
      irep_idt class_name=file_to_class_name(file_name);
    
      // Already there? Ignore.
      if(class_jar_map.find(class_name)==class_jar_map.end())
      {
        // record
        class_jar_map[class_name].jar_file_name=file;
        class_jar_map[class_name].index=index;
      }
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

  // strip .class              
  if(has_suffix(result, ".class"))
    result.resize(result.size()-6);
    
  // slash to dot
  for(std::string::iterator it=result.begin(); it!=result.end(); it++)
    if(*it=='/') *it='.';

  return result;
}
