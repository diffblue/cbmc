/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language_file.h"

#include <linking/linking_class.h>

#include "language.h"

#include <fstream>

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

bool language_filest::parse(message_handlert &message_handler)
{
  messaget log(message_handler);

  for(auto &file : file_map)
  {
    // open file

    std::ifstream infile(file.first);

    if(!infile)
    {
      log.error() << "Failed to open " << file.first << messaget::eom;
      return true;
    }

    // parse it

    languaget &language=*(file.second.language);

    if(language.parse(infile, file.first))
    {
      log.error() << "Parsing of " << file.first << " failed" << messaget::eom;
      return true;
    }

    // what is provided?

    file.second.get_modules();
  }

  return false;
}

optionalt<symbol_tablet> language_filest::typecheck(
  const bool keep_file_local,
  message_handlert &message_handler)
{
  symbol_tablet symbol_table;

  // typecheck interfaces

  for(auto &file : file_map)
  {
    if(file.second.language->interfaces(symbol_table))
      return {};
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
  linkingt linker{symbol_table, message_handler};
  for(auto &file : file_map)
  {
    if(file.second.modules.empty())
    {
      if(file.second.language->can_keep_file_local())
      {
        auto file_symtab_opt =
          file.second.language->typecheck("", keep_file_local);
        if(!file_symtab_opt.has_value())
          return {};
        if(linker.link(*file_symtab_opt))
          return {};
      }
      else
      {
        auto file_symtab_opt = file.second.language->typecheck("");
        if(!file_symtab_opt.has_value())
          return {};
        if(linker.link(*file_symtab_opt))
          return {};
      }
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
    bool failed =
      typecheck_module(module.second, keep_file_local, message_handler);
    if(failed)
      return {};
    if(linker.link(module.second.symbol_table))
      return {};
  }

  return std::move(symbol_table);
}

bool language_filest::generate_support_functions(
  symbol_table_baset &symbol_table)
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

bool language_filest::interfaces(symbol_table_baset &symbol_table)
{
  for(auto &file : file_map)
  {
    if(file.second.language->interfaces(symbol_table))
      return true;
  }

  return false;
}

bool language_filest::typecheck_module(
  const std::string &module,
  const bool keep_file_local,
  message_handlert &message_handler)
{
  // check module map

  module_mapt::iterator it=module_map.find(module);

  if(it==module_map.end())
  {
    messaget log(message_handler);
    log.error() << "found no file that provides module " << module
                << messaget::eom;
    return true;
  }

  return typecheck_module(it->second, keep_file_local, message_handler);
}

bool language_filest::typecheck_module(
  language_modulet &module,
  const bool keep_file_local,
  message_handlert &message_handler)
{
  // already typechecked?

  if(module.type_checked)
    return false;

  messaget log(message_handler);

  // already in progress?

  if(module.in_progress)
  {
    log.error() << "circular dependency in " << module.name << messaget::eom;
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
    module.in_progress =
      !typecheck_module(*it, keep_file_local, message_handler);
    if(module.in_progress == false)
      return true;
  }

  // type check it

  log.status() << "Type-checking " << module.name << messaget::eom;

  if(module.file->language->can_keep_file_local())
  {
    auto module_symtab_opt =
      module.file->language->typecheck(module.name, keep_file_local);
    if(!module_symtab_opt.has_value())
    {
      module.in_progress = false;
      return true;
    }
    module.symbol_table = std::move(*module_symtab_opt);
  }
  else
  {
    auto module_symtab_opt = module.file->language->typecheck(module.name);
    if(!module_symtab_opt.has_value())
    {
      module.in_progress = false;
      return true;
    }
    module.symbol_table = std::move(*module_symtab_opt);
  }

  module.type_checked=true;
  module.in_progress=false;

  return false;
}
