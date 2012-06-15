/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string.h>

#include <sstream>
#include <fstream>

#include <expr_util.h>
#include <replace_symbol.h>
#include <config.h>

#include "ansi_c_language.h"
#include "ansi_c_convert.h"
#include "ansi_c_typecheck.h"
#include "ansi_c_parser.h"
#include "expr2c.h"
#include "trans_unit.h"
#include "c_link.h"
#include "c_preprocess.h"
#include "c_main.h"
#include "internal_additions.h"
#include "remove_internal_symbols.h"

/*******************************************************************\

Function: ansi_c_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> ansi_c_languaget::extensions() const
{
  std::set<std::string> s;
  s.insert("c");
  s.insert("i");
  return s;
}

/*******************************************************************\

Function: ansi_c_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void ansi_c_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(translation_unit(parse_path));
}

/*******************************************************************\

Function: ansi_c_languaget::preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool ansi_c_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // stdin?
  if(path=="")
    return c_preprocess(PREPROCESS_C, instream, outstream, message_handler);

  return c_preprocess(PREPROCESS_C, path, outstream, message_handler);  
}
             
/*******************************************************************\

Function: ansi_c_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  // store the path

  parse_path=path;

  // preprocessing

  std::ostringstream o_preprocessed;

  if(preprocess(instream, path, o_preprocessed, message_handler))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  std::string code;
  ansi_c_internal_additions(code);
  std::istringstream codestr(code);

  ansi_c_parser.clear();
  ansi_c_parser.filename=ID_built_in;
  ansi_c_parser.in=&codestr;
  ansi_c_parser.set_message_handler(message_handler);
  ansi_c_parser.grammar=ansi_c_parsert::LANGUAGE;

  switch(config.ansi_c.mode)
  {
  case configt::ansi_ct::MODE_CODEWARRIOR:
    ansi_c_parser.mode=ansi_c_parsert::CW;
    break;
   
  case configt::ansi_ct::MODE_VISUAL_STUDIO:
    ansi_c_parser.mode=ansi_c_parsert::MSC;
    break;
    
  case configt::ansi_ct::MODE_ANSI:
    ansi_c_parser.mode=ansi_c_parsert::ANSI;
    break;
    
  case configt::ansi_ct::MODE_GCC:
    ansi_c_parser.mode=ansi_c_parsert::GCC;
    break;
    
  case configt::ansi_ct::MODE_ARM:
    ansi_c_parser.mode=ansi_c_parsert::ARM;
    break;
    
  default:
    assert(false);
  }

  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(!result)
  {
    ansi_c_parser.line_no=0;
    ansi_c_parser.filename=path;
    ansi_c_parser.in=&i_preprocessed;
    ansi_c_scanner_init();
    result=ansi_c_parser.parse();
  }

  // save result
  parse_tree.swap(ansi_c_parser.parse_tree);

  // save some memory
  ansi_c_parser.clear();

  return result;
}
             
/*******************************************************************\

Function: ansi_c_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::typecheck(
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  if(ansi_c_convert(parse_tree, module, message_handler))
    return true;

  contextt new_context;

  if(ansi_c_typecheck(parse_tree, new_context, module, message_handler))
    return true;

  remove_internal_symbols(new_context);
  
  if(c_link(context, new_context, message_handler))
    return true;
    
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::final(
  contextt &context,
  message_handlert &message_handler)
{
  if(c_main(context, "c::main", message_handler)) return true;
  
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void ansi_c_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

/*******************************************************************\

Function: new_ansi_c_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_ansi_c_language()
{
  return new ansi_c_languaget;
}

/*******************************************************************\

Function: ansi_c_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2c(expr, ns);
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool ansi_c_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2c(type, ns);
  return false;
}

/*******************************************************************\

Function: ansi_c_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
                         
bool ansi_c_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(code);
  
  // parsing

  ansi_c_parser.clear();
  ansi_c_parser.filename="";
  ansi_c_parser.in=&i_preprocessed;
  ansi_c_parser.set_message_handler(message_handler);
  ansi_c_parser.grammar=ansi_c_parsert::EXPRESSION;
  ansi_c_parser.mode=ansi_c_parsert::GCC;
  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=ansi_c_parser.parse_tree.items.front().value();
    
    result=ansi_c_convert(expr, "", message_handler);

    // typecheck it
    if(!result)
      result=ansi_c_typecheck(expr, message_handler, ns);
  }

  // save some memory
  ansi_c_parser.clear();

  return result;
}

/*******************************************************************\

Function: ansi_c_languaget::~ansi_c_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

ansi_c_languaget::~ansi_c_languaget()
{
}
