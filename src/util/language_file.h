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
    symbol_tablet &symtab);

  language_filet(const language_filet &rhs);

  language_filet():language(NULL)
  {
  }

  ~language_filet();
};

class language_filest:public messaget
{
public:
  typedef std::map<std::string, language_filet> filemapt;
  filemapt filemap;

  // Contains pointers into filemapt!
  typedef std::map<std::string, language_modulet> modulemapt;
  modulemapt modulemap;

  // Contains pointers into filemapt!
  // This is safe-ish as long as this is std::map.
  typedef std::map<irep_idt, language_filet*> lazymethodmapt;
  lazymethodmapt lazymethodmap;

  void clear_files()
  {
    filemap.clear();
  }

  bool parse();

  void show_parse(std::ostream &out);

  bool typecheck(symbol_tablet &symbol_table);

  bool final(symbol_tablet &symbol_table);

  bool interfaces(symbol_tablet &symbol_table);

  bool has_lazy_method(const irep_idt &id)
  {
    return lazymethodmap.count(id);
  }

  void convert_lazy_method(
    const irep_idt &id,
    symbol_tablet &symtab)
  {
    return lazymethodmap.at(id)->convert_lazy_method(id, symtab);
  }

  void clear()
  {
    filemap.clear();
    modulemap.clear();
    lazymethodmap.clear();
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
