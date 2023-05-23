/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_LANGAPI_LANGUAGE_FILE_H
#define CPROVER_LANGAPI_LANGUAGE_FILE_H

#include <util/symbol_table.h>

#include <iosfwd>
#include <map>
#include <memory> // unique_ptr
#include <set>
#include <string>
#include <unordered_set>

class message_handlert;
class language_filet;
class languaget;

class language_modulet final
{
public:
  std::string name;
  bool type_checked, in_progress;
  symbol_tablet symbol_table;
  language_filet *file;

  language_modulet():
    type_checked(false),
    in_progress(false),
    file(nullptr)
  {}
};

class language_filet final
{
public:
  typedef std::set<std::string> modulest;
  modulest modules;

  std::unique_ptr<languaget> language;
  std::string filename;

  void get_modules();

  void convert_lazy_method(
    const irep_idt &id,
    symbol_table_baset &symbol_table);

  explicit language_filet(const std::string &filename);
  language_filet(const language_filet &rhs);

  ~language_filet();
};

class language_filest
{
private:
  typedef std::map<std::string, language_filet> file_mapt;
  file_mapt file_map;

  typedef std::map<std::string, language_modulet> module_mapt;
  module_mapt module_map;

  // Contains pointers into file_map!
  // This is safe-ish as long as this is std::map.
  typedef std::map<irep_idt, language_filet *> lazy_method_mapt;
  lazy_method_mapt lazy_method_map;

public:
  language_filet &add_file(const std::string &filename)
  {
    language_filet language_file(filename);
    return file_map.emplace(filename, std::move(language_file)).first->second;
  }

  void remove_file(const std::string &filename)
  {
    // Clear relevant entries from lazy_method_map
    language_filet *language_file = &file_map.at(filename);
    std::unordered_set<irep_idt> files_methods;
    for(auto const &method : lazy_method_map)
    {
      if(method.second == language_file)
        files_methods.insert(method.first);
    }
    for(const irep_idt &method_name : files_methods)
      lazy_method_map.erase(method_name);

    file_map.erase(filename);
  }

  void clear_files()
  {
    lazy_method_map.clear();
    file_map.clear();
  }

  bool parse(message_handlert &message_handler);

  void show_parse(std::ostream &out);

  bool generate_support_functions(symbol_table_baset &symbol_table);

  optionalt<symbol_tablet>
  typecheck(const bool keep_file_local, message_handlert &message_handler);
  optionalt<symbol_tablet> typecheck(message_handlert &message_handler)
  {
    return typecheck(false, message_handler);
  }

  bool final(symbol_table_baset &symbol_table);

  bool interfaces(symbol_table_baset &symbol_table);

  // The method must have been added to the symbol table and registered
  // in lazy_method_map (currently always in language_filest::typecheck)
  // for this to be legal.
  void convert_lazy_method(
    const irep_idt &id,
    symbol_table_baset &symbol_table,
    message_handlert &message_handler)
  {
    PRECONDITION(symbol_table.has_symbol(id));
    lazy_method_mapt::iterator it=lazy_method_map.find(id);
    if(it!=lazy_method_map.end())
      it->second->convert_lazy_method(id, symbol_table);
  }

  bool can_convert_lazy_method(const irep_idt &id) const
  {
    return lazy_method_map.count(id) != 0;
  }

  void clear()
  {
    file_map.clear();
    module_map.clear();
    lazy_method_map.clear();
  }

protected:
  bool typecheck_module(
    language_modulet &module,
    const bool keep_file_local,
    message_handlert &message_handler);

  bool typecheck_module(
    const std::string &module,
    const bool keep_file_local,
    message_handlert &message_handler);
};

#endif // CPROVER_UTIL_LANGUAGE_FILE_H
