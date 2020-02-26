/*******************************************************************\

Module: Classes for representing generic structured data

Author: Thomas Kiley

\*******************************************************************/
#ifndef CPROVER_UTIL_STRUCTURED_DATA_H
#define CPROVER_UTIL_STRUCTURED_DATA_H

#include "json.h"
#include "xml.h"
#include <string>
#include <vector>

struct labelt
{
public:
  explicit labelt(std::vector<std::string> components);

  std::string camel_case() const;
  std::string snake_case() const;
  std::string kebab_case() const;
  std::string pretty() const;

  bool operator<(const labelt &other) const;

private:
  std::vector<std::string> components;
};

struct structured_data_entryt
{
  static structured_data_entryt data_node(const jsont &data);
  static structured_data_entryt
  entry(std::map<labelt, structured_data_entryt> children);

  bool is_leaf() const;
  std::string leaf_data() const;
  jsont leaf_object() const;
  std::map<labelt, structured_data_entryt> get_children() const;

private:
  explicit structured_data_entryt(const jsont &data);
  explicit structured_data_entryt(
    std::map<labelt, structured_data_entryt> children);

  jsont data;
  std::map<labelt, structured_data_entryt> children;
};

class structured_datat
{
public:
  explicit structured_datat(std::map<labelt, structured_data_entryt> data);

  xmlt to_xml() const;
  jsont to_json() const;
  std::string to_pretty() const;

private:
  std::map<labelt, structured_data_entryt> data;
};

#endif // CPROVER_UTIL_STRUCTURED_DATA_H
