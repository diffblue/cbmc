/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_class_loader.h"

#include <stack>
#include <fstream>

#include <util/suffix.h>
#include <util/prefix.h>

#include "java_bytecode_parser.h"

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

    debug() << "Reading class " << c << eom;

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

/// Check if class is an overlay class by searching for `ID_overlay_class` in
/// its list of annotations. TODO(nathan) give a short explanation about what
/// overlay classes are.
/// \param c: a `classt` object from a java byte code parse tree
/// \return true if parsed class is an overlay class, else false
static bool is_overlay_class(const java_bytecode_parse_treet::classt &c)
{
  return java_bytecode_parse_treet::find_annotation(
           c.annotations, ID_overlay_class)
    .has_value();
}

/// Check through all the places class parse trees can appear and returns the
/// first implementation it finds plus any overlay class implementations
/// \param class_loader_limit: Filter to decide whether to load classes
/// \param class_name: Name of class to load
/// \returns The list of valid implementations, including overlays
/// \remarks
///   Allows multiple definitions of the same class to appear on the
///   classpath, so long as all but the first definition are marked with the
///   attribute `\@java::org.cprover.OverlayClassImplementation`.
java_class_loadert::parse_tree_with_overlayst &
java_class_loadert::get_parse_tree(
  java_class_loader_limitt &class_loader_limit,
  const irep_idt &class_name)
{
  parse_tree_with_overlayst &parse_trees = class_map[class_name];
  PRECONDITION(parse_trees.empty());

  // do we refuse to load?
  if(!class_loader_limit.load_class_file(class_name_to_jar_file(class_name)))
  {
    debug() << "not loading " << class_name << " because of limit" << eom;
    java_bytecode_parse_treet parse_tree;
    parse_tree.parsed_class.name = class_name;
    parse_trees.push_back(std::move(parse_tree));
    return parse_trees;
  }

  // Rummage through the class path
  for(const auto &cp_entry : classpath_entries)
  {
    auto parse_tree = load_class(class_name, cp_entry);
    if(parse_tree.has_value())
      parse_trees.emplace_back(std::move(*parse_tree));
  }

  auto parse_tree_it = parse_trees.begin();
  // If the first class implementation is an overlay emit a warning and
  // skip over it until we find a non-overlay class
  while(parse_tree_it != parse_trees.end())
  {
    // Skip parse trees that failed to load - though these shouldn't exist yet
    if(parse_tree_it->loading_successful)
    {
      if(!is_overlay_class(parse_tree_it->parsed_class))
      {
        // Keep the non-overlay class
        ++parse_tree_it;
        break;
      }
      warning()
        << "Skipping class " << class_name
        << " marked with OverlayClassImplementation but found before"
          " original definition"
        << eom;
    }
    auto unloaded_or_overlay_out_of_order_it = parse_tree_it;
    ++parse_tree_it;
    parse_trees.erase(unloaded_or_overlay_out_of_order_it);
  }
  // Collect overlay classes
  while(parse_tree_it != parse_trees.end())
  {
    // Remove non-initial classes that aren't overlays
    if(!is_overlay_class(parse_tree_it->parsed_class))
    {
      warning()
        << "Skipping duplicate definition of class " << class_name
        << " not marked with OverlayClassImplementation" << eom;
      auto duplicate_non_overlay_it = parse_tree_it;
      ++parse_tree_it;
      parse_trees.erase(duplicate_non_overlay_it);
    }
    else
      ++parse_tree_it;
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

/// Load all class files from a .jar file
/// \param jar_path: the path for the .jar to load
std::vector<irep_idt> java_class_loadert::load_entire_jar(
  const std::string &jar_path)
{
  auto classes = read_jar_file(jar_path);
  if(!classes.has_value())
    return {};

  classpath_entries.push_front(
    classpath_entryt(classpath_entryt::JAR, jar_path));

  for(const auto &c : *classes)
    operator()(c);

  classpath_entries.pop_front();

  return *classes;
}

optionalt<std::vector<irep_idt>>
java_class_loadert::read_jar_file(const std::string &jar_path)
{
  std::vector<std::string> filenames;
  try
  {
    filenames = jar_pool(jar_path).filenames();
  }
  catch(const std::runtime_error &)
  {
    error() << "failed to open JAR file `" << jar_path << "'" << eom;
    return {};
  }
  debug() << "Adding JAR file `" << jar_path << "'" << eom;

  // Create a new entry in the map and initialize using the list of file names
  // that are in jar_filet
  std::vector<irep_idt> classes;
  for(auto &file_name : filenames)
  {
    if(has_suffix(file_name, ".class"))
    {
      debug()
        << "Found class file " << file_name << " in JAR `" << jar_path << "'"
        << eom;
      irep_idt class_name=file_to_class_name(file_name);
      classes.push_back(class_name);
    }
  }
  return classes;
}
