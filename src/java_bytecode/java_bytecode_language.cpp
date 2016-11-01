/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <string>

#include <util/symbol_table.h>
#include <util/suffix.h>
#include <util/config.h>
#include <util/cmdline.h>
#include <util/string2int.h>

#include <goto-programs/class_hierarchy.h>

#include "java_bytecode_language.h"
#include "java_bytecode_convert_class.h"
#include "java_bytecode_convert_method.h"
#include "java_bytecode_internal_additions.h"
#include "java_bytecode_typecheck.h"
#include "java_entry_point.h"
#include "java_bytecode_parser.h"
#include "java_class_loader.h"

#include "expr2java.h"

/*******************************************************************\

Function: java_bytecode_languaget::get_language_options

  Inputs: Command-line options

 Outputs: None

 Purpose: Consume options that are java bytecode specific.

\*******************************************************************/

void java_bytecode_languaget::get_language_options(const cmdlinet &cmd)
{
  disable_runtime_checks=cmd.isset("disable-runtime-check");
  assume_inputs_non_null=cmd.isset("java-assume-inputs-non-null");
  if(cmd.isset("java-max-input-array-length"))
    max_nondet_array_length=
      std::stoi(cmd.get_value("java-max-input-array-length"));
  if(cmd.isset("java-max-vla-length"))
    max_user_array_length=std::stoi(cmd.get_value("java-max-vla-length"));
}

/*******************************************************************\

Function: java_bytecode_languaget::extensions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::set<std::string> java_bytecode_languaget::extensions() const
{
  return { "class", "jar" };
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
  std::ostream &outstream)
{
  // there is no preprocessing!
  return true;
}

/*******************************************************************\

Function: java_bytecode_languaget::parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  java_class_loader.set_message_handler(get_message_handler());

  // look at extension
  if(has_suffix(path, ".class"))
  {
    // override main_class
    main_class=java_class_loadert::file_to_class_name(path);
  }
  else if(has_suffix(path, ".jar"))
  {
    #ifdef HAVE_LIBZIP
    if(config.java.main_class.empty())
    {
      // Does it have a main class set in the manifest?
      jar_filet::manifestt manifest=
        java_class_loader.jar_pool(path).get_manifest();
      std::string manifest_main_class=manifest["Main-Class"];

      if(manifest_main_class!="")
        main_class=manifest_main_class;
    }
    else
      main_class=config.java.main_class;

    // Do we have one now?
    if(main_class.empty())
    {
      status() << "JAR file without entry point: loading it all" << eom;
      java_class_loader.load_entire_jar(path);
    }
    else
      java_class_loader.add_jar_file(path);

    #else
    error() << "No support for reading JAR files" << eom;
    return true;
    #endif
  }
  else
    assert(false);

  if(!main_class.empty())
  {
    status() << "Java main class: " << main_class << eom;
    java_class_loader(main_class);
  }

  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::typecheck

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/



bool java_bytecode_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module)
{
  std::map<irep_idt, std::pair<const symbolt*, const java_bytecode_parse_treet::methodt*> >
    lazy_methods;

  // first convert all
  for(java_class_loadert::class_mapt::const_iterator
      c_it=java_class_loader.class_map.begin();
      c_it!=java_class_loader.class_map.end();
      c_it++)
  {
    if(c_it->second.parsed_class.name.empty())
      continue;

    debug() << "Converting class " << c_it->first << eom;

    if(java_bytecode_convert_class(
         c_it->second,
         symbol_table,
         get_message_handler(),
         disable_runtime_checks,
         max_user_array_length,
         lazy_methods))
      return true;
  }

  // Now incrementally elaborate methods that are reachable from this entry point:

  // Convert-method will need this to find virtual function targets.
  class_hierarchyt ch;
  ch(symbol_table);

  std::vector<irep_idt> worklist1;
  std::vector<irep_idt> worklist2;

  auto main_function=get_main_symbol(symbol_table,main_class,get_message_handler(),true);
  if(main_function.stop_convert)
  {
    // Failed, mark all functions in the given main class reachable.
    const auto& methods=java_class_loader.class_map.at(main_class).parsed_class.methods;
    for(const auto& method : methods)
    {
      const irep_idt methodid="java::"+id2string(main_class)+"."+
        id2string(method.name)+":"+
        id2string(method.signature);
      worklist2.push_back(methodid);
    }
  }
  else
    worklist2.push_back(main_function.main_function.name);

  std::set<irep_idt> already_populated;
  while(worklist2.size()!=0)
  {
    std::swap(worklist1,worklist2);
    for(const auto& mname : worklist1)
    {
      if(!already_populated.insert(mname).second)
        continue;
      auto findit=lazy_methods.find(mname);
      if(findit==lazy_methods.end())
      {
        debug() << "Skip " << mname << eom;
        continue;
      }
      debug() << "Lazy methods: elaborate " << mname << eom;
      const auto& parsed_method=findit->second;
      java_bytecode_convert_method(*parsed_method.first,*parsed_method.second,
				   symbol_table,get_message_handler(),
				   disable_runtime_checks,max_user_array_length,worklist2,ch);
    }
    worklist1.clear();
  }

  // Remove symbols for methods that were declared but never used:
  symbol_tablet keep_symbols;

  for(const auto& sym : symbol_table.symbols)
  {
    if(lazy_methods.count(sym.first) && !already_populated.count(sym.first))
      continue;
    keep_symbols.add(sym.second);
  }

  debug() << "Lazy methods: removed " << symbol_table.symbols.size() - keep_symbols.symbols.size() << " unreachable methods" << eom;

  symbol_table.swap(keep_symbols);

  // now typecheck all
  if(java_bytecode_typecheck(
       symbol_table, get_message_handler()))
    return true;

  return false;
}

/*******************************************************************\

Function: java_bytecode_languaget::final

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_bytecode_languaget::final(symbol_tablet &symbol_table)
{
  /*
  if(c_final(symbol_table, message_handler)) return true;
  */
  java_internal_additions(symbol_table);


  main_function_resultt res=
    get_main_symbol(symbol_table, main_class, get_message_handler());
  if(res.stop_convert)
    return res.error_found;

  symbolt entry=res.main_function;

  return(
    java_entry_point(
      symbol_table,
      main_class,
      get_message_handler(),
      assume_inputs_non_null,
      max_nondet_array_length));
}

/*******************************************************************\

Function: java_bytecode_languaget::show_parse

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void java_bytecode_languaget::show_parse(std::ostream &out)
{
  java_class_loader(main_class).output(out);
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
  code=expr2java(expr, ns);
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
  code=type2java(type, ns);
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

  return true; // fail for now
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
