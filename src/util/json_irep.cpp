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
/// sub tree be included.
json_irept::json_irept(bool _include_comments):
  include_comments(_include_comments)
{
}

/// To convert to JSON from an irep structure by recursively generating JSON
/// for the different sub trees.
/// \param irep: The irep structure to turn into json
/// \return: The json object.
json_objectt json_irept::convert_from_irep(const irept &irep) const
{
  json_objectt irep_object;

  if(irep.id()!=ID_nil)
    irep_object["id"]=json_stringt(irep.id_string());

  convert_sub_tree("sub", irep.get_sub(), irep_object);
  convert_named_sub_tree("namedSub", irep.get_named_sub(), irep_object);

  if(include_comments)
    convert_named_sub_tree("comment", irep.get_comments(), irep_object);

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
    {
      json_objectt sub_object=convert_from_irep(sub_tree.second);
      sub_objects[id2string(sub_tree.first)]=sub_object;
    }
    parent[sub_tree_id]=sub_objects;
  }
}

/// Deserialize a JSON irep representation.
/// \param in: json object to convert
/// \return result - irep equivalent of input
irept json_irept::convert_from_json(const jsont &in) const
{
  std::vector<std::string> have_keys;
  for(const auto &keyval : in.object)
    have_keys.push_back(keyval.first);
  std::sort(have_keys.begin(), have_keys.end());
  if(have_keys!=std::vector<std::string>{"comment", "id", "namedSub", "sub"})
  {
    throw deserialization_exceptiont(
      "irep JSON representation is missing one of needed keys: "
      "'id', 'sub', 'namedSub', 'comment'");
  }

  irept out(in["id"].value);

  for(const auto &sub : in["sub"].array)
    out.get_sub().push_back(convert_from_json(sub));

  for(const auto &named_sub : in["namedSub"].object)
    out.add(named_sub.first)=convert_from_json(named_sub.second);

  for(const auto &comment : in["comment"].object)
    out.add(comment.first)=convert_from_json(comment.second);

  return out;
}
