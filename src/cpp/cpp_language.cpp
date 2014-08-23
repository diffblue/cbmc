/*******************************************************************\

Module: C++ Language Module

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <cstring>
#include <sstream>
#include <fstream>

#include <util/config.h>
#include <util/replace_symbol.h>

#include <linking/linking.h>
#include <linking/entry_point.h>

#include <ansi-c/c_preprocess.h>
#include <ansi-c/trans_unit.h>

#include "cpp_internal_additions.h"
#include "cpp_language.h"
#include "expr2cpp.h"
#include "cpp_parser.h"
#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> cpp_languaget::extensions() const
{
  std::set<std::string> s;
  
  s.insert("cpp");
  s.insert("CPP");
  s.insert("cc");
  s.insert("c++");
  s.insert("ii");
  s.insert("cxx");
  
  #ifndef _WIN32
  s.insert("C");
  #endif

  return s;
}

/*******************************************************************\

Function: cpp_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(translation_unit(parse_path));
}

/*******************************************************************\

Function: cpp_languaget::preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool cpp_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  if(config.ansi_c.mode==configt::ansi_ct::MODE_GCC_C)
    config.ansi_c.mode=configt::ansi_ct::MODE_GCC_CPP;

  if(path=="")
    return c_preprocess(instream, outstream, get_message_handler());

  // check extension

  const char *ext=strrchr(path.c_str(), '.');
  if(ext!=NULL && std::string(ext)==".ipp")
  {
    std::ifstream infile(path.c_str());

    char ch;

    while(infile.read(&ch, 1))
      outstream << ch;

    return false;
  }

  return c_preprocess(path, outstream, get_message_handler());
}

/*******************************************************************\

Function: cpp_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  // store the path

  parse_path=path;

  // preprocessing

  std::ostringstream o_preprocessed;

  cpp_internal_additions(o_preprocessed);

  if(preprocess(instream, path, o_preprocessed))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  cpp_parser.clear();
  cpp_parser.set_file(path);
  cpp_parser.in=&i_preprocessed;
  cpp_parser.set_message_handler(get_message_handler());

  switch(config.ansi_c.mode)
  {
  case configt::ansi_ct::MODE_CODEWARRIOR_C_CPP:
    cpp_parser.mode=ansi_c_parsert::CW;
    break;
   
  case configt::ansi_ct::MODE_VISUAL_STUDIO_C_CPP:
    cpp_parser.mode=ansi_c_parsert::MSC;
    break;
    
  case configt::ansi_ct::MODE_ANSI_C_CPP:
    cpp_parser.mode=ansi_c_parsert::ANSI;
    break;
    
  case configt::ansi_ct::MODE_GCC_C:
  case configt::ansi_ct::MODE_GCC_CPP:
    cpp_parser.mode=ansi_c_parsert::GCC;
    break;
    
  case configt::ansi_ct::MODE_ARM_C_CPP:
    cpp_parser.mode=ansi_c_parsert::ARM;
    break;
    
  default:
    assert(false);
  }

  bool result=cpp_parser.parse();

  // save result
  cpp_parse_tree.swap(cpp_parser.parse_tree);

  // save some memory
  cpp_parser.clear();

  return result;
}

/*******************************************************************\

Function: cpp_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  if(module=="") return false;

  symbol_tablet new_symbol_table;

  if(cpp_typecheck(cpp_parse_tree, new_symbol_table, module, get_message_handler()))
    return true;

  return linking(symbol_table, new_symbol_table, get_message_handler());
}

/*******************************************************************\

Function: cpp_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_languaget::final(symbol_tablet &symbol_table)
{
  if(entry_point(symbol_table, "c::main", get_message_handler()))
    return true;

  return false;
}

/*******************************************************************\

Function: cpp_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_languaget::show_parse(std::ostream &out)
{
  for(cpp_parse_treet::itemst::const_iterator it=
      cpp_parse_tree.items.begin();
      it!=cpp_parse_tree.items.end();
      it++)
    show_parse(out, *it);
}

/*******************************************************************\

Function: cpp_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_languaget::show_parse(
  std::ostream &out,
  const cpp_itemt &item)
{
  if(item.is_linkage_spec())
  {
    const cpp_linkage_spect &linkage_spec=
      item.get_linkage_spec();

    out << "LINKAGE " << linkage_spec.linkage().get("value")
        << ":" << std::endl;

    for(cpp_linkage_spect::itemst::const_iterator
        it=linkage_spec.items().begin();
        it!=linkage_spec.items().end();
        it++)
      show_parse(out, *it);

    out << std::endl;
  }
  else if(item.is_namespace_spec())
  {
    const cpp_namespace_spect &namespace_spec=
      item.get_namespace_spec();

    out << "NAMESPACE " << namespace_spec.get_namespace()
        << ":" << std::endl;

    for(cpp_namespace_spect::itemst::const_iterator
        it=namespace_spec.items().begin();
        it!=namespace_spec.items().end();
        it++)
      show_parse(out, *it);

    out << std::endl;
  }
  else if(item.is_using())
  {
    const cpp_usingt &cpp_using=item.get_using();

    out << "USING ";
    if(cpp_using.get_namespace())
      out << "NAMESPACE ";
    out << cpp_using.name() << std::endl;
    out << std::endl;
  }
  else if(item.is_declaration())
  {
    item.get_declaration().output(out);
  }
  else
    out << "UNKNOWN: " << item << std::endl;
}

/*******************************************************************\

Function: new_cpp_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_cpp_language()
{
  return new cpp_languaget;
}

/*******************************************************************\

Function: cpp_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2cpp(expr, ns);
  return false;
}

/*******************************************************************\

Function: cpp_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2cpp(type, ns);
  return false;
}

/*******************************************************************\

Function: cpp_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cpp_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  const namespacet &ns)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(code);

  // parsing

  cpp_parser.clear();
  cpp_parser.set_file(irep_idt());
  cpp_parser.in=&i_preprocessed;
  cpp_parser.set_message_handler(get_message_handler());

  bool result=cpp_parser.parse();

  if(cpp_parser.parse_tree.items.empty())
    result=true;
  else
  {
    // TODO
    //expr.swap(cpp_parser.parse_tree.declarations.front());

    // typecheck it
    result=cpp_typecheck(expr, get_message_handler(), ns);
  }

  // save some memory
  cpp_parser.clear();

  return result;
}

/*******************************************************************\

Function: cpp_languaget::~cpp_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

cpp_languaget::~cpp_languaget()
{
}
