/*******************************************************************\

Module: Util

Author: Thomas Kiley, thomas.kiley@diffblue.com

\*******************************************************************/

#ifndef CPROVER_UTIL_JSON_IREP_H
#define CPROVER_UTIL_JSON_IREP_H

#include <util/irep.h>
class jsont;
class json_objectt;

class json_irept
{
public:
  explicit json_irept(bool include_comments);
  void convert_from_irep(const irept &irep, jsont &json) const;

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

#endif // CPROVER_UTIL_JSON_IREP_H
