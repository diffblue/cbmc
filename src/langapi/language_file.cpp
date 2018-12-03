/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language_file.h"

#include <fstream>

#include <util/object_factory_parameters.h>

#include "language.h"

language_filet::language_filet(const language_filet &rhs):
  modules(rhs.modules),
  language(rhs.language==nullptr?nullptr:rhs.language->new_language()),
  filename(rhs.filename)
{
}

/// To avoid compiler errors, the complete definition of a pointed-to type must
/// be visible at the point at which the unique_ptr destructor is created.  In
/// this case, the pointed-to type is forward-declared, so we have to place the
/// destructor in the source file, where the full definition is availible.
language_filet::~language_filet()=default;

language_filet::language_filet(const std::string &filename)
  : filename(filename)
{
}

void language_filet::get_modules()
{
  language->modules_provided(modules);
}

void language_filet::convert_lazy_method(
  const irep_idt &id,
  symbol_table_baset &symbol_table)
{
  language->convert_lazy_method(id, symbol_table);
}

void language_filest::show_parse(std::ostream &out)
{
  for(const auto &file : file_map)
    file.second.language->show_parse(out);
}

bool language_filest::parse()
{
  for(auto &file : file_map)
  {
    // open file

    std::ifstream infile(file.first);

    if(!infile)
    {
      error() << "Failed to open " << file.first << eom;
      return true;
    }

    // parse it

    languaget &language=*(file.second.language);

    if(language.parse(infile, file.first))
    {
      error() << "Parsing of " << file.first << " failed" << eom;
      return true;
    }

    // what is provided?

    file.second.get_modules();
  }

  return false;
}

bool language_filest::typecheck(symbol_tablet &symbol_table)
{
  // typecheck interfaces

  for(auto &file : file_map)
  {
    if(file.second.language->interfaces(symbol_table))
      return true;
  }

  // build module map

  unsigned collision_counter=0;

  for(auto &file : file_map)
  {
    const language_filet::modulest &modules=
      file.second.modules;

    for(language_filet::modulest::const_iterator
        mo_it=modules.begin();
        mo_it!=modules.end();
        mo_it++)
    {
      // these may collide, and then get renamed
      std::string module_name=*mo_it;

      while(module_map.find(module_name)!=module_map.end())
      {
        module_name=*mo_it+"#"+std::to_string(collision_counter);
        collision_counter++;
      }

      language_modulet module;
      module.file=&file.second;
      module.name=module_name;
      module_map.insert(
        std::pair<std::string, language_modulet>(module.name, module));
    }
  }

  // typecheck files

  for(auto &file : file_map)
  {
    if(file.second.modules.empty())
    {
      if(file.second.language->typecheck(symbol_table, ""))
        return true;
      // register lazy methods.
      // TODO: learn about modules and generalise this
      // to module-providing languages if required.
      std::unordered_set<irep_idt> lazy_method_ids;
      file.second.language->methods_provided(lazy_method_ids);
      for(const auto &id : lazy_method_ids)
        lazy_method_map[id]=&file.second;
    }
  }

  // typecheck modules

  for(auto &module : module_map)
  {
    if(typecheck_module(symbol_table, module.second))
      return true;
  }

  return false;
}

bool language_filest::generate_support_functions(
  symbol_tablet &symbol_table)
{
  std::set<std::string> languages;

  for(auto &file : file_map)
  {
    if(languages.insert(file.second.language->id()).second)
      if(file.second.language->generate_support_functions(symbol_table))
        return true;
  }

  return false;
}

bool language_filest::final(symbol_table_baset &symbol_table)
{
  std::set<std::string> languages;

  for(auto &file : file_map)
  {
    if(languages.insert(file.second.language->id()).second)
      if(file.second.language->final(symbol_table))
        return true;
  }

  return false;
}

bool language_filest::interfaces(
  symbol_tablet &symbol_table)
{
  for(auto &file : file_map)
  {
    if(file.second.language->interfaces(symbol_table))
      return true;
  }

  return false;
}

bool language_filest::typecheck_module(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  // check module map

  module_mapt::iterator it=module_map.find(module);

  if(it==module_map.end())
  {
    error() << "found no file that provides module " << module << eom;
    return true;
  }

  return typecheck_module(symbol_table, it->second);
}

bool language_filest::typecheck_module(
  symbol_tablet &symbol_table,
  language_modulet &module)
{
  // already typechecked?

  if(module.type_checked)
    return false;

  // already in progress?

  if(module.in_progress)
  {
    error() << "circular dependency in " << module.name << eom;
    return true;
  }

  module.in_progress=true;

  // first get dependencies of current module

  std::set<std::string> dependency_set;

  module.file->language->dependencies(module.name, dependency_set);

  for(std::set<std::string>::const_iterator it=
      dependency_set.begin();
      it!=dependency_set.end();
      it++)
  {
    if(typecheck_module(symbol_table, *it))
    {
      module.in_progress=false;
      return true;
    }
  }

  // type check it

  status() << "Type-checking " << module.name << eom;

  if(module.file->language->typecheck(symbol_table, module.name))
  {
    module.in_progress=false;
    return true;
  }

  module.type_checked=true;
  module.in_progress=false;

  return false;
}
