/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Options

#ifndef CPROVER_UTIL_OPTIONS_H
#define CPROVER_UTIL_OPTIONS_H

#include <string>
#include <map>
#include <list>

class json_objectt;
class xmlt;

class optionst
{
public:
  typedef std::list<std::string> value_listt;
  typedef std::map<std::string, value_listt> option_mapt;

  const std::string get_option(const std::string &option) const;
  bool get_bool_option(const std::string &option) const;
  signed int get_signed_int_option(const std::string &option) const;
  unsigned int get_unsigned_int_option(const std::string &option) const;
  const value_listt &get_list_option(const std::string &option) const;

  /// N.B. opts.is_set("foo") does not imply opts.get_bool_option("foo")
  bool is_set(const std::string &option) const;

  void set_option(const std::string &option, const bool value);
  void set_option(const std::string &option, const int value);
  void set_option(const std::string &option, const unsigned value);
  void set_option(const std::string &option, const std::string &value);

  void set_option(const std::string &option, const char *value)
  {
    set_option(option, std::string(value));
  }

  void set_option(const std::string &option, const value_listt &values)
  {
    option_map[option]=values;
  }

  optionst() { }
  ~optionst() { }

  optionst &operator=(const optionst &other)
  {
    option_map=other.option_map;
    return *this;
  }

  json_objectt to_json() const;
  xmlt to_xml() const;
  void output(std::ostream &out) const;

protected:
  option_mapt option_map;
  const value_listt empty_list;
};

#endif // CPROVER_UTIL_OPTIONS_H
