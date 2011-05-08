/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <fstream>

#include "language.h"
#include "language_file.h"
#include "strstream2string.h"
  
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

bool language_filest::typecheck(contextt &context)
{
  // typecheck interfaces

  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(it->second.language->interfaces(context, get_message_handler()))
      return true;
  }

  // build module map

  for(filemapt::iterator fm_it=filemap.begin();
      fm_it!=filemap.end(); fm_it++)
  {
    std::set<std::string> &modules=fm_it->second.modules;

    for(std::set<std::string>::const_iterator mo_it=modules.begin();
        mo_it!=modules.end(); mo_it++)
    {
      language_modulet module;
      module.file=&fm_it->second;
      module.name=*mo_it;
      modulemap.insert(std::pair<std::string, language_modulet>(module.name, module));
    }
  }

  // typecheck files

  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(it->second.modules.empty())
      if(it->second.language->typecheck(context, "", get_message_handler()))
        return true;
  }

  // typecheck modules

  for(modulemapt::iterator it=modulemap.begin();
      it!=modulemap.end(); it++)
  {
    if(typecheck_module(context, it->second))
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
  contextt &context)
{
  std::set<std::string> languages;

  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(languages.insert(it->second.language->id()).second)
      if(it->second.language->final(context, get_message_handler()))
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
  contextt &context)
{
  for(filemapt::iterator it=filemap.begin();
      it!=filemap.end(); it++)
  {
    if(it->second.language->interfaces(context, get_message_handler()))
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
  contextt &context,
  const std::string &module)
{
  // check module map

  modulemapt::iterator it=modulemap.find(module);

  if(it==modulemap.end())
  {
    error("found no file that provides module "+module);
    return true;
  }

  return typecheck_module(context, it->second);
}

/*******************************************************************\

Function: language_filest::typecheck_module

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool language_filest::typecheck_module(
  contextt &context,
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
    if(typecheck_module(context, *it))
    {
      module.in_progress=false;
      return true;
    }
  }

  // type check it

  status("Type-checking "+module.name);

  if(module.file->language->typecheck(context, module.name, get_message_handler()))
  {
    module.in_progress=false;
    return true;
  }

  module.type_checked=true;
  module.in_progress=false;

  return false;
}
