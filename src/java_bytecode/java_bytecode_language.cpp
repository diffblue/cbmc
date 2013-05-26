/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#if 0
#include <string.h>

#include <sstream>
#include <fstream>

#include <expr_util.h>
#include <replace_symbol.h>
#include <config.h>
#endif

#include "java_bytecode_language.h"

#if 0
#include "java_bytecode_convert.h"
#include "java_bytecode_typecheck.h"
#include "java_bytecode_parser.h"
#include "c_final.h"
#include "trans_unit.h"
#include "c_link.h"
#include "c_preprocess.h"
#include "c_main.h"
#include "internal_additions.h"
#endif

#include <ansi-c/expr2c.h>

/*******************************************************************\

Function: java_bytecode_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> java_bytecode_languaget::extensions() const
{
  std::set<std::string> s;
  s.insert("class");
  return s;
}

/*******************************************************************\

Function: java_bytecode_languaget::modules_provided

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_languaget::modules_provided(std::set<std::string> &modules)
{
  // modules.insert(translation_unit(parse_path));
}

/*******************************************************************\

Function: java_bytecode_languaget::preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool java_bytecode_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  #if 0
  // stdin?
  if(path=="")
    return c_preprocess(instream, outstream, message_handler);

  return c_preprocess(path, outstream, message_handler);  
  #endif
}
             
/*******************************************************************\

Function: java_bytecode_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::parse(
  std::istream &instream,
  const std::string &path,
  message_handlert &message_handler)
{
  #if 0
  // store the path

  parse_path=path;

  // preprocessing

  std::ostringstream o_preprocessed;

  if(preprocess(instream, path, o_preprocessed, message_handler))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  std::string code;
  java_bytecode_internal_additions(code);
  std::istringstream codestr(code);

  java_bytecode_parser.clear();
  java_bytecode_parser.filename="<built-in>";
  java_bytecode_parser.in=&codestr;
  java_bytecode_parser.set_message_handler(message_handler);
  java_bytecode_parser.grammar=java_bytecode_parsert::LANGUAGE;

  switch(config.java_bytecode.mode)
  {
  case configt::java_bytecodet::MODE_CODEWARRIOR:
    java_bytecode_parser.mode=java_bytecode_parsert::CW;
    break;
   
  case configt::java_bytecodet::MODE_VISUAL_STUDIO:
    java_bytecode_parser.mode=java_bytecode_parsert::MSC;
    break;
    
  case configt::java_bytecodet::MODE_ANSI:
    java_bytecode_parser.mode=java_bytecode_parsert::ANSI;
    break;
    
  case configt::java_bytecodet::MODE_GCC:
    java_bytecode_parser.mode=java_bytecode_parsert::GCC;
    break;
    
  case configt::java_bytecodet::MODE_ARM:
    java_bytecode_parser.mode=java_bytecode_parsert::ARM;
    break;
    
  default:
    assert(false);
  }

  java_bytecode_scanner_init();

  bool result=java_bytecode_parser.parse();

  if(!result)
  {
    java_bytecode_parser.line_no=0;
    java_bytecode_parser.filename=path;
    java_bytecode_parser.in=&i_preprocessed;
    java_bytecode_scanner_init();
    result=java_bytecode_parser.parse();
  }

  // save result
  parse_tree.swap(java_bytecode_parser.parse_tree);

  // save some memory
  java_bytecode_parser.clear();

  return result;
  #endif
}
             
/*******************************************************************\

Function: java_bytecode_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::typecheck(
  contextt &context,
  const std::string &module,
  message_handlert &message_handler)
{
  #if 0
  if(java_bytecode_convert(parse_tree, module, message_handler))
    return true;

  contextt new_context;

  if(java_bytecode_typecheck(parse_tree, new_context, module, message_handler))
    return true;

  if(c_link(context, new_context, message_handler))
    return true;
    
  return false;
  #endif
}

/*******************************************************************\

Function: java_bytecode_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::final(
  contextt &context,
  message_handlert &message_handler)
{
  #if 0
  if(c_final(context, message_handler)) return true;
  if(c_main(context, "c::", "c::main", message_handler)) return true;
  
  return false;
  #endif
}

/*******************************************************************\

Function: java_bytecode_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
void java_bytecode_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

/*******************************************************************\

Function: new_java_bytecode_language

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

languaget *new_java_bytecode_language()
{
  return new java_bytecode_languaget;
}

/*******************************************************************\

Function: java_bytecode_languaget::from_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2c(expr, ns);
  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::from_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2c(type, ns);
  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::to_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
                         
bool java_bytecode_languaget::to_expr(
  const std::string &code,
  const std::string &module,
  exprt &expr,
  message_handlert &message_handler,
  const namespacet &ns)
{
  #if 0
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(code);
  
  // parsing

  java_bytecode_parser.clear();
  java_bytecode_parser.filename="";
  java_bytecode_parser.in=&i_preprocessed;
  java_bytecode_parser.set_message_handler(message_handler);
  java_bytecode_parser.grammar=java_bytecode_parsert::EXPRESSION;
  java_bytecode_parser.mode=java_bytecode_parsert::GCC;
  java_bytecode_scanner_init();

  bool result=java_bytecode_parser.parse();

  if(java_bytecode_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=java_bytecode_parser.parse_tree.items.front().value();
    
    result=java_bytecode_convert(expr, "", message_handler);

    // typecheck it
    if(!result)
      result=java_bytecode_typecheck(expr, message_handler, ns);
  }

  // save some memory
  java_bytecode_parser.clear();

  return result;
  #endif
}

/*******************************************************************\

Function: java_bytecode_languaget::~java_bytecode_languaget

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

java_bytecode_languaget::~java_bytecode_languaget()
{
}
