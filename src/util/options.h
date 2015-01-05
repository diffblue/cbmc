/*******************************************************************\

Module: Options

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_OPTIONS_H
#define CPROVER_OPTIONS_H

#include <string>
#include <map>

class optionst
{
public:
  typedef std::map<std::string, std::string> option_mapt;
  
  option_mapt option_map; // input
  
  virtual const std::string get_option(const std::string &option) const;
  virtual bool get_bool_option(const std::string &option) const;
  virtual signed int get_signed_int_option(const std::string &option) const;
  virtual unsigned int get_unsigned_int_option(const std::string &option) const;
  virtual void set_option(const std::string &option, const bool value);
  virtual void set_option(const std::string &option, const int value);
  virtual void set_option(const std::string &option, const unsigned value);
  virtual void set_option(const std::string &option, const std::string &value);
  
  optionst() { }
  virtual ~optionst() { }
};

#endif
