/*******************************************************************\

Module: Util

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

/// \file
/// Util

#ifndef CPROVER_UTIL_JSON_IREP_H
#define CPROVER_UTIL_JSON_IREP_H

#include "irep.h"
#include "json.h"

class source_locationt;

class json_irept
{
public:
  explicit json_irept(bool include_comments);
  json_objectt convert_from_irep(const irept &) const;
  irept convert_from_json(const jsont &) const;

private:
  void convert_sub_tree(
    const std::string &sub_tree_id,
    const irept::subt &sub_trees,
    json_objectt &parent) const;

  void convert_named_sub_tree(
    const std::string &sub_tree_id,
    const irept::named_subt &sub_trees,
    json_objectt &parent) const;

  bool include_comments;
};

json_objectt json(const source_locationt &);

#endif // CPROVER_UTIL_JSON_IREP_H
