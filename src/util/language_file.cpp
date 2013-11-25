/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include "i2string.h"
#include "language.h"
#include "language_file.h"
  
/*******************************************************************\

Function: language_filet::language_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

language_filet::language_filet(const language_filet &rhs):
  modules(rhs.modules),
  language(rhs.language==NULL?NULL:rhs.language->new_language()),
  filename(rhs.filename)
{
}

/*******************************************************************\

Function: language_filet::~language_filet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

language_filet::~language_filet()
{
  if(language!=NULL) delete language;
}

/*******************************************************************\

Function: language_filet::get_modules

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void language_filet::get_modules()
{
  language->modules_provided(modules);
}

/*******************************************************************\

Function: language_filest::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void language_filest::show_parse(std::ostream &out)
{
  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
    it->second.language->show_parse(out);
}

/*******************************************************************\

Function: language_filest::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_filest::parse()
{
  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    // open file

    std::ifstream infile(it->first.c_str());

    if(!infile)
    {
      error("Failed to open "+it->first);
      return true;
    }

    // parse it

    languaget &language=*(it->second.language);

    if(language.parse(infile, it->first, get_message_handler()))
    {
      error("Parsing of "+it->first+" failed");
      return true;
    }

    // what is provided?

    it->second.get_modules();
  }

  return false;
}

/*******************************************************************\

Function: language_filest::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_filest::typecheck(symbol_tablet &symbol_table)
{
  // typecheck interfaces

  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(it->second.language->interfaces(symbol_table, get_message_handler()))
      return true;
  }

  // build module map
  
  unsigned collision_counter=0;

  for(filemapt::iterator fm_it=filemap.begin();
      fm_it!=filemap.end(); fm_it++)
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
      
      while(modulemap.find(module_name)!=modulemap.end())
      {
        module_name=*mo_it+"#"+i2string(collision_counter);
        collision_counter++;
      }
      
      language_modulet module;
      module.file=&fm_it->second;
      module.name=module_name;
      modulemap.insert(
        std::pair<std::string, language_modulet>(module.name, module));
    }
  }

  // typecheck files

  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(it->second.modules.empty())
      if(it->second.language->typecheck(symbol_table, "", get_message_handler()))
        return true;
  }

  // typecheck modules

  for(modulemapt::iterator it=modulemap.begin();
      it!=modulemap.end(); it++)
  {
    if(typecheck_module(symbol_table, it->second))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: language_filest::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_filest::final(
  symbol_tablet &symbol_table)
{
  std::set<std::string> languages;

  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(languages.insert(it->second.language->id()).second)
      if(it->second.language->final(symbol_table, get_message_handler()))
        return true;
  }

  return false;
}

/*******************************************************************\

Function: language_filest::interfaces

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_filest::interfaces(
  symbol_tablet &symbol_table)
{
  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(it->second.language->interfaces(symbol_table, get_message_handler()))
      return true;
  }

  return false;
}

/*******************************************************************\

Function: language_filest::typecheck_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_filest::typecheck_module(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  // check module map

  modulemapt::iterator it=modulemap.find(module);

  if(it==modulemap.end())
  {
    error("found no file that provides module "+module);
    return true;
  }

  return typecheck_module(symbol_table, it->second);
}

/*******************************************************************\

Function: language_filest::typecheck_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    error("circular dependency in "+module.name);
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

  status("Type-checking "+module.name);

  if(module.file->language->typecheck(symbol_table, module.name, get_message_handler()))
  {
    module.in_progress=false;
    return true;
  }

  module.type_checked=true;
  module.in_progress=false;

  return false;
}
