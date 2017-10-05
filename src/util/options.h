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

class optionst
{
public:
  using value_listt = std::list<std::string>;
  using option_mapt = std::map<std::string, value_listt>;

  const std::string get_option(const std::string &option) const;
  bool get_bool_option(const std::string &option) const;
  signed int get_signed_int_option(const std::string &option) const;
  unsigned int get_unsigned_int_option(const std::string &option) const;
  const value_listt &get_list_option(const std::string &option) const;

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

protected:
  option_mapt option_map;
  const value_listt empty_list;
};

#endif // CPROVER_UTIL_OPTIONS_H
