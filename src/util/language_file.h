/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LANGUAGE_FILE_H
#define CPROVER_LANGUAGE_FILE_H

#include <ostream>
#include <set>
#include <string>

#include <message.h>

class contextt;
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

  typedef std::map<std::string, language_modulet> modulemapt;
  modulemapt modulemap;

  void clear_files()
  {
    filemap.clear();
  }

  bool parse();
  
  void show_parse(std::ostream &out);
  
  bool typecheck(contextt &context);

  bool final(contextt &context);

  bool interfaces(contextt &context);
  
  void clear()
  {
    filemap.clear();
    modulemap.clear();
  }

protected:                      
  bool typecheck_module(
    contextt &context,
    language_modulet &module);

  bool typecheck_module(
    contextt &context,
    const std::string &module);
};
 
#endif
