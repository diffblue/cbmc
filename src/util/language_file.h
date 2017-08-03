/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_LANGUAGE_FILE_H
#define CPROVER_UTIL_LANGUAGE_FILE_H

#include <iosfwd>
#include <set>
#include <map>
#include <string>

#include "message.h"

class symbol_tablet;
class language_filet;
class languaget;

class language_modulet
{
public:
  std::string name;
  bool type_checked, in_progress;
  language_filet *file;

  language_modulet()
  { type_checked=in_progress=false; }
};

class language_filet
{
public:
  typedef std::set<std::string> modulest;
  modulest modules;

  languaget *language;
  std::string filename;

  void get_modules();

  void convert_lazy_method(
    const irep_idt &id,
    symbol_tablet &symbol_table);

  language_filet(const language_filet &rhs);

  language_filet():language(nullptr)
  {
  }

  ~language_filet();
};

class language_filest:public messaget
{
public:
  typedef std::map<std::string, language_filet> file_mapt;
  file_mapt file_map;

  // Contains pointers into file_mapt!
  typedef std::map<std::string, language_modulet> module_mapt;
  module_mapt module_map;

  // Contains pointers into filemapt!
  // This is safe-ish as long as this is std::map.
  typedef std::map<irep_idt, language_filet *> lazy_method_mapt;
  lazy_method_mapt lazy_method_map;

  void clear_files()
  {
    file_map.clear();
  }

  void set_should_generate_opaque_method_stubs(bool stubs_enabled);

  bool parse();

  void show_parse(std::ostream &out);

  bool typecheck(symbol_tablet &symbol_table);

  bool final(symbol_tablet &symbol_table);

  bool interfaces(symbol_tablet &symbol_table);

  bool has_lazy_method(const irep_idt &id)
  {
    return lazy_method_map.count(id)!=0;
  }

  // The method must have been added to the symbol table and registered
  // in lazy_method_map (currently always in language_filest::typecheck)
  // for this to be legal.
  void convert_lazy_method(
    const irep_idt &id,
    symbol_tablet &symbol_table)
  {
    return lazy_method_map.at(id)->convert_lazy_method(id, symbol_table);
  }

  void clear()
  {
    file_map.clear();
    module_map.clear();
    lazy_method_map.clear();
  }

protected:
  bool typecheck_module(
    symbol_tablet &symbol_table,
    language_modulet &module);

  bool typecheck_module(
    symbol_tablet &symbol_table,
    const std::string &module);
};

#endif // CPROVER_UTIL_LANGUAGE_FILE_H
