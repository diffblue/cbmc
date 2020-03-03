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

/// A way of representing nested key/value data. Used for logging on any
/// message handler.
/// Usage:
/// ```
/// structured_datat data{
///   {{labelt{{"my", "data"}},
///      structured_data_entryt::entry(
///        {{labelt{{"my", "number"}},
///           structured_data_entryt::data_node(json_numbert("10"))},
///         {labelt{{"my", "string"}},
///           structured_data_entryt::data_node(json_stringt("hi"))}})}}};
/// message() << data << eom;
/// ```
/// Then if the output dependending on the UI of the message handler, you'll
/// get appropriately formatted data:
///
/// XML:
/// ```xml
/// <my-data>
///   <my-number>10</my-number>
///   <my-string>hi</my-string>
/// </my-data>
/// ```
///
/// JSON:
/// ```json
/// {
///   "myData": {
///      "myNumber": 10
///      "myString": "hi"
///    }
///  }
/// ```
///
/// Plain:
/// ```
/// My data:
///    My number: 10
///    My string: hi
/// ```
class structured_datat
{
public:
  explicit structured_datat(std::map<labelt, structured_data_entryt> data);
  const std::map<labelt, structured_data_entryt> & data() const;

private:
  std::map<labelt, structured_data_entryt> _data;
};

xmlt to_xml(const structured_datat &data);
jsont to_json(const structured_datat &data);
std::string to_pretty(const structured_datat &);

#endif // CPROVER_UTIL_STRUCTURED_DATA_H
