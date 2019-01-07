/*******************************************************************\

Module: Util

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// Util

#include "json_irep.h"

#include "exception_utils.h"
#include "irep.h"
#include "json.h"

#include <algorithm>

/// To convert to JSON from an irep structure by recursively generating JSON
/// for the different sub trees.
/// \param _include_comments: when writing JSON, should the comments
///   sub tree be included.
json_irept::json_irept(bool _include_comments):
  include_comments(_include_comments)
{
}

/// To convert to JSON from an irep structure by recursively generating JSON
/// for the different sub trees.
/// \param irep: The irep structure to turn into json
/// \return The json object.
json_objectt json_irept::convert_from_irep(const irept &irep) const
{
  json_objectt irep_object;

  irep_object["id"] = json_stringt(irep.id_string());

  convert_sub_tree("sub", irep.get_sub(), irep_object);
  convert_named_sub_tree("namedSub", irep.get_named_sub(), irep_object);

  return irep_object;
}

/// To convert to JSON from a list of ireps that are in an unlabelled subtree.
/// The parent JSON object will get a key called sub_tree_id and the value shall
/// be an array of JSON objects generated from each of the sub trees
/// \param sub_tree_id: the name to give the subtree in the parent object
/// \param sub_trees: the list of subtrees to parse
/// \param parent: the parent JSON object who should be added to

void json_irept::convert_sub_tree(
  const std::string &sub_tree_id,
  const irept::subt &sub_trees,
  json_objectt &parent) const
{
  if(!sub_trees.empty())
  {
    json_arrayt sub_objects;
    for(const irept &sub_tree : sub_trees)
    {
      json_objectt sub_object=convert_from_irep(sub_tree);
      sub_objects.push_back(sub_object);
    }
    parent[sub_tree_id]=sub_objects;
  }
}

/// To convert to JSON from a map of ireps that are in a named subtree. The
/// parent JSON object will get a key called sub_tree_id and the value shall be
/// a JSON object whose keys shall be the name of the sub tree and the value
/// will be the object generated from the sub tree.
/// \param sub_tree_id: the name to give the subtree in the parent object
/// \param sub_trees: the map of subtrees to parse
/// \param parent: the parent JSON object who should be added to
void json_irept::convert_named_sub_tree(
  const std::string &sub_tree_id,
  const irept::named_subt &sub_trees,
  json_objectt &parent) const
{
  if(!sub_trees.empty())
  {
    json_objectt sub_objects;
    for(const auto &sub_tree : sub_trees)
      if(include_comments || !irept::is_comment(sub_tree.first))
      {
        json_objectt sub_object = convert_from_irep(sub_tree.second);
        sub_objects[id2string(sub_tree.first)] = sub_object;
      }
    parent[sub_tree_id]=sub_objects;
  }
}

/// Deserialize a JSON irep representation.
/// \param in: json object to convert
/// \return result - irep equivalent of input
irept json_irept::convert_from_json(const jsont &in) const
{
  if(!in.is_object())
  {
    throw deserialization_exceptiont(
      "irep JSON representation must be an object");
  }

  const json_objectt &json_object = to_json_object(in);

  irept out;

  {
    const auto it = json_object.find("id");

    if(it != json_object.end())
    {
      out.id(it->second.value);
    }
  }

  {
    const auto it = json_object.find("sub");

    if(it != json_object.end())
    {
      for(const auto &sub : to_json_array(it->second))
        out.get_sub().push_back(convert_from_json(sub));
    }
  }

  {
    const auto it = json_object.find("namedSub");

    if(it != json_object.end())
    {
      for(const auto &named_sub : to_json_object(it->second))
        out.add(named_sub.first) = convert_from_json(named_sub.second);
    }
  }

  return out;
}

json_objectt json(const source_locationt &location)
{
  json_objectt result;

  if(!location.get_working_directory().empty())
    result["workingDirectory"] = json_stringt(location.get_working_directory());

  if(!location.get_file().empty())
    result["file"] = json_stringt(location.get_file());

  if(!location.get_line().empty())
    result["line"] = json_stringt(location.get_line());

  if(!location.get_column().empty())
    result["column"] = json_stringt(location.get_column());

  if(!location.get_function().empty())
    result["function"] = json_stringt(location.get_function());

  if(!location.get_java_bytecode_index().empty())
    result["bytecodeIndex"] = json_stringt(location.get_java_bytecode_index());

  return result;
}
