/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "language_file.h"

#include <fstream>

#include "language.h"

language_filet::language_filet(const language_filet &rhs):
  modules(rhs.modules),
  language(rhs.language==nullptr?nullptr:rhs.language->new_language()),
  filename(rhs.filename)
{
}

language_filet::~language_filet()
{
  if(language!=nullptr)
    delete language;
}

void language_filet::get_modules()
{
  language->modules_provided(modules);
}

void language_filet::convert_lazy_method(
  const irep_idt &id,
  symbol_tablet &symbol_table)
{
  language->convert_lazy_method(id, symbol_table);
}

void language_filest::show_parse(std::ostream &out)
{
  for(file_mapt::iterator it=file_map.begin();
      it!=file_map.end(); it++)
    it->second.language->show_parse(out);
}

/// Turn on or off stub generation for all the languages
/// \param should_generate_stubs: Should stub generation be enabled
void language_filest::set_should_generate_opaque_method_stubs(
  bool stubs_enabled)
{
  for(file_mapt::value_type &language_file_entry : file_map)
  {
    languaget *language=language_file_entry.second.language;
    language->set_should_generate_opaque_method_stubs(stubs_enabled);
  }
}

bool language_filest::parse()
{
  for(file_mapt::iterator it=file_map.begin();
      it!=file_map.end(); it++)
  {
    // open file

    std::ifstream infile(it->first);

    if(!infile)
    {
      error() << "Failed to open " << it->first << eom;
      return true;
    }

    // parse it

    languaget &language=*(it->second.language);

    if(language.parse(infile, it->first))
    {
      error() << "Parsing of " << it->first << " failed" << eom;
      return true;
    }

    // what is provided?

    it->second.get_modules();
  }

  return false;
}

bool language_filest::typecheck(symbol_tablet &symbol_table)
{
  // typecheck interfaces

  for(file_mapt::iterator it=file_map.begin();
      it!=file_map.end(); it++)
  {
    if(it->second.language->interfaces(symbol_table))
      return true;
  }

  // build module map

  unsigned collision_counter=0;

  for(file_mapt::iterator fm_it=file_map.begin();
      fm_it!=file_map.end(); fm_it++)
  {
    const language_filet::modulest &modules=
      fm_it->second.modules;

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
      module.file=&fm_it->second;
      module.name=module_name;
      module_map.insert(
        std::pair<std::string, language_modulet>(module.name, module));
    }
  }

  // typecheck files

  for(file_mapt::iterator it=file_map.begin();
      it!=file_map.end(); it++)
  {
    if(it->second.modules.empty())
    {
      if(it->second.language->typecheck(symbol_table, ""))
        return true;
      // register lazy methods.
      // TODO: learn about modules and generalise this
      // to module-providing languages if required.
      std::set<irep_idt> lazy_method_ids;
      it->second.language->lazy_methods_provided(lazy_method_ids);
      for(const auto &id : lazy_method_ids)
        lazy_method_map[id]=&it->second;
    }
  }

  // typecheck modules

  for(module_mapt::iterator it=module_map.begin();
      it!=module_map.end(); it++)
  {
    if(typecheck_module(symbol_table, it->second))
      return true;
  }

  return false;
}

bool language_filest::final(
  symbol_tablet &symbol_table)
{
  std::set<std::string> languages;

  for(file_mapt::iterator it=file_map.begin();
      it!=file_map.end(); it++)
  {
    if(languages.insert(it->second.language->id()).second)
      if(it->second.language->final(symbol_table))
        return true;
  }

  return false;
}

bool language_filest::interfaces(
  symbol_tablet &symbol_table)
{
  for(file_mapt::iterator it=file_map.begin();
      it!=file_map.end(); it++)
  {
    if(it->second.language->interfaces(symbol_table))
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
