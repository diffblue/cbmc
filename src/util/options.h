/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_OPTIONS_H
#define CPROVER_OPTIONS_H

#include <string>
#include <map>
#include <list>

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
  void set_option(const std::string &option, const bool value);
  void set_option(const std::string &option, const int value);
  void set_option(const std::string &option, const unsigned value);
  void set_option(const std::string &option, const std::string &value);
  
  optionst() { }
  ~optionst() { }

protected:
  option_mapt option_map;  
  const value_listt empty_list;
};

#endif
