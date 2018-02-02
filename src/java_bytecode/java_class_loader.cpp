/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_class_loader.h"

#include <stack>
#include <fstream>

#include <util/suffix.h>
#include <util/prefix.h>
#include <util/config.h>

#include "java_bytecode_parser.h"

#include "library/java_core_models.inc"

/// This variable stores the data of the file core-models.jar. The macro
/// JAVA_CORE_MODELS_SIZE is defined in the header java_core_models.inc, which
/// gets generated at compile time by running a small utility (converter.cpp) on
/// actual .jar file. The number of bytes in the variable is
/// JAVA_CORE_MODELS_SIZE, another macro defined in java_core_models.inc.
unsigned char java_core_models[] = { JAVA_CORE_MODELS_DATA };

java_class_loadert::parse_tree_with_overlayst &java_class_loadert::operator()(
  const irep_idt &class_name)
{
  std::stack<irep_idt> queue;
  // Always require java.lang.Object, as it is the base of
  // internal classes such as array types.
  queue.push("java.lang.Object");
  // java.lang.String
  queue.push("java.lang.String");
  // add java.lang.Class
  queue.push("java.lang.Class");
  // Require java.lang.Throwable as the catch-type used for
  // universal exception handlers:
  queue.push("java.lang.Throwable");
  queue.push(class_name);

  // Require user provided classes to be loaded even without explicit reference
  for(const auto &id : java_load_classes)
    queue.push(id);

  java_class_loader_limitt class_loader_limit(
    get_message_handler(), java_cp_include_files);

  while(!queue.empty())
  {
    irep_idt c=queue.top();
    queue.pop();

    if(class_map.count(c) != 0)
      continue;

    debug() << "Parsing class " << c << eom;

    parse_tree_with_overlayst &parse_trees =
      get_parse_tree(class_loader_limit, c);

    // Add any dependencies to queue
    for(const java_bytecode_parse_treet &parse_tree : parse_trees)
      for(const irep_idt &class_ref : parse_tree.class_refs)
        queue.push(class_ref);

    // Add any extra dependencies provided by our caller:
    if(get_extra_class_refs)
    {
      for(const irep_idt &id : get_extra_class_refs(c))
        queue.push(id);
    }
  }

  return class_map.at(class_name);
}

optionalt<java_bytecode_parse_treet> java_class_loadert::get_class_from_jar(
  const irep_idt &class_name,
  const std::string &jar_file,
  java_class_loader_limitt &class_loader_limit)
{
  jar_indext &jar_index = jars_by_path.at(jar_file);
  auto jar_index_it = jar_index.find(class_name);
  if(jar_index_it == jar_index.end())
    return {};

  debug()
    << "Getting class `" << class_name << "' from JAR " << jar_file << eom;

  std::string data =
    jar_pool(class_loader_limit, jar_file).get_entry(jar_index_it->second);

  java_bytecode_parse_treet parse_tree;
  std::istringstream istream(data);
  if(java_bytecode_parse(istream, parse_tree, get_message_handler()))
    return {};
  return parse_tree;
}

java_class_loadert::parse_tree_with_overlayst &
java_class_loadert::get_parse_tree(
  java_class_loader_limitt &class_loader_limit,
  const irep_idt &class_name)
{
  parse_tree_with_overlayst &parse_trees = class_map[class_name];
  PRECONDITION(parse_trees.empty());

  // First add all given JAR files
  for(const auto &jar_file : jar_files)
  {
    read_jar_file(class_loader_limit, jar_file);
    optionalt<java_bytecode_parse_treet> parse_tree =
      get_class_from_jar(class_name, jar_file, class_loader_limit);
    if(parse_tree)
      parse_trees.push_back(*parse_tree);
  }

  // Then add core models
  if(use_core_models)
  {
    // Add internal jar file. The name is used to load it once only and
    // reference it later.
    std::string core_models = "core-models.jar";
    jar_pool(
      class_loader_limit, core_models, java_core_models, JAVA_CORE_MODELS_SIZE);

    // This does not read from the jar file but from the jar_filet object we
    // just created
    read_jar_file(class_loader_limit, core_models);

    optionalt<java_bytecode_parse_treet> parse_tree =
      get_class_from_jar(class_name, core_models, class_loader_limit);
    if(parse_tree)
      parse_trees.push_back(*parse_tree);
  }

  // Then add everything on the class path
  for(const auto &cp_entry : config.java.classpath)
  {
    if(has_suffix(cp_entry, ".jar"))
    {
      read_jar_file(class_loader_limit, cp_entry);

      optionalt<java_bytecode_parse_treet> parse_tree =
        get_class_from_jar(class_name, cp_entry, class_loader_limit);
      if(parse_tree)
        parse_trees.push_back(*parse_tree);
    }
    else
    {
      // Look in the given directory
      const std::string class_file = class_name_to_file(class_name);
      const std::string full_path =
        #ifdef _WIN32
        cp_entry + '\\' + class_file;
        #else
        cp_entry + '/' + class_file;
        #endif

      if(!class_loader_limit.load_class_file(class_file))
        continue;

      if(std::ifstream(full_path))
      {
        debug()
          << "Getting class `" << class_name << "' from file " << full_path
          << eom;
        java_bytecode_parse_treet parse_tree;
        if(!java_bytecode_parse(full_path, parse_tree, get_message_handler()))
          parse_trees.push_back(std::move(parse_tree));
      }
    }
  }

  if(!parse_trees.empty())
    return parse_trees;

  // Not found or failed to load
  warning() << "failed to load class `" << class_name << '\'' << eom;
  java_bytecode_parse_treet parse_tree;
  parse_tree.parsed_class.name=class_name;
  parse_trees.push_back(std::move(parse_tree));
  return parse_trees;
}

void java_class_loadert::load_entire_jar(
  java_class_loader_limitt &class_loader_limit,
  const std::string &jar_path)
{
  jar_index_optcreft jar_index = read_jar_file(class_loader_limit, jar_path);
  if(!jar_index)
    return;

  jar_files.push_front(jar_path);

  for(const auto &e : jar_index->get())
    operator()(e.first);

  jar_files.pop_front();
}

java_class_loadert::jar_index_optcreft java_class_loadert::read_jar_file(
  java_class_loader_limitt &class_loader_limit,
  const std::string &jar_path)
{
  auto existing_it = jars_by_path.find(jar_path);
  if(existing_it != jars_by_path.end())
    return std::cref(existing_it->second);

  std::vector<std::string> filenames;
  try
  {
    filenames = this->jar_pool(class_loader_limit, jar_path).filenames();
  }
  catch(const std::runtime_error &)
  {
    error() << "failed to open JAR file `" << jar_path << "'" << eom;
    return jar_index_optcreft();
  }
  debug() << "Adding JAR file `" << jar_path << "'" << eom;

  // Create a new entry in the map and initialize using the list of file names
  // that were retained in the jar_filet by the class_loader_limit filter
  jar_indext &jar_index = jars_by_path[jar_path];
  for(auto &file_name : filenames)
  {
    if(has_suffix(file_name, ".class"))
    {
      debug()
        << "Found class file " << file_name << " in JAR `" << jar_path << "'"
        << eom;
      irep_idt class_name=file_to_class_name(file_name);
      jar_index[class_name] = file_name;
    }
  }
  return std::cref(jar_index);
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

jar_filet &java_class_loadert::jar_pool(
  java_class_loader_limitt &class_loader_limit,
  const std::string &file_name)
{
  const auto it=m_archives.find(file_name);
  if(it==m_archives.end())
  {
    // VS: Can't construct in place
    auto file=jar_filet(class_loader_limit, file_name);
    return m_archives.emplace(file_name, std::move(file)).first->second;
  }
  else
    return it->second;
}

jar_filet &java_class_loadert::jar_pool(
  java_class_loader_limitt &class_loader_limit,
  const std::string &buffer_name,
  const void *pmem,
  size_t size)
{
  const auto it=m_archives.find(buffer_name);
  if(it==m_archives.end())
  {
    // VS: Can't construct in place
    auto file=jar_filet(class_loader_limit, pmem, size);
    return m_archives.emplace(buffer_name, std::move(file)).first->second;
  }
  else
    return it->second;
}
