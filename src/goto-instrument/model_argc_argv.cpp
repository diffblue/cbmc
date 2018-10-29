/*******************************************************************\

Module: Initialize command line arguments

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Initialize command line arguments

#include "model_argc_argv.h"

#include <sstream>

#include <util/cprover_prefix.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/namespace.h>
#include <util/config.h>
#include <util/replace_symbol.h>
#include <util/symbol_table.h>
#include <util/prefix.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

/// Set up argv with up to max_argc pointers into an array of 4096 bytes.
/// \param goto_model: Contains the input program's symbol table and
///   intermediate representation
/// \param max_argc: User-specified maximum number of arguments to be modelled
/// \param message_handler: message logging
/// \return True, if and only if modelling succeeded
bool model_argc_argv(
  goto_modelt &goto_model,
  unsigned max_argc,
  message_handlert &message_handler)
{
  messaget message(message_handler);
  const namespacet ns(goto_model.symbol_table);

  if(!goto_model.symbol_table.has_symbol(
       goto_model.goto_functions.entry_point()))
  {
    message.error() << "Linking not done, missing "
                    << goto_model.goto_functions.entry_point()
                    << messaget::eom;
    return true;
  }

  const symbolt &main_symbol=
    ns.lookup(config.main.empty()?ID_main:config.main);

  if(main_symbol.mode!=ID_C)
  {
    message.error() << "argc/argv modelling is C specific"
                    << messaget::eom;
    return true;
  }

  const code_typet::parameterst &parameters=
    to_code_type(main_symbol.type).parameters();
  if(parameters.size()!=2 &&
     parameters.size()!=3)
  {
    message.warning() << "main expected to take 2 or 3 arguments,"
                      << " argc/argv instrumentation skipped"
                      << messaget::eom;
    return false;
  }

  const symbolt &argc_primed = ns.lookup("argc'");
  symbol_exprt ARGC("ARGC", argc_primed.type);
  const symbolt &argv_primed = ns.lookup("argv'");
  symbol_exprt ARGV("ARGV", argv_primed.type);

  // set the size of ARGV storage to 4096, which matches the minimum
  // guaranteed by POSIX (_POSIX_ARG_MAX):
  // http://pubs.opengroup.org/onlinepubs/009695399/basedefs/limits.h.html
  std::ostringstream oss;
  oss << "int ARGC;\n"
      << "char *ARGV[1];\n"
      << "void " << goto_model.goto_functions.entry_point() << "()\n"
      << "{\n"
      << "  unsigned next=0u;\n"
      << "  " CPROVER_PREFIX "assume(ARGC>=1);\n"
      << "  " CPROVER_PREFIX "assume(ARGC<=" << max_argc << ");\n"
      << "  char arg_string[4096];\n"
      << "  " CPROVER_PREFIX "input(\"arg_string\", &arg_string[0]);\n"
      << "  for(int i=0; i<ARGC && i<" << max_argc << "; ++i)\n"
      << "  {\n"
      << "    unsigned len;\n"
      << "    " CPROVER_PREFIX "assume(len<4096);\n"
      << "    " CPROVER_PREFIX "assume(next+len<4096);\n"
      << "    " CPROVER_PREFIX "assume(arg_string[next+len]==0);\n"
      << "    ARGV[i]=&(arg_string[next]);\n"
      << "    next+=len+1;\n"
      << "  }\n"
      << "}";
  std::istringstream iss(oss.str());

  ansi_c_languaget ansi_c_language;
  ansi_c_language.set_message_handler(message_handler);
  configt::ansi_ct::preprocessort pp=config.ansi_c.preprocessor;
  config.ansi_c.preprocessor=configt::ansi_ct::preprocessort::NONE;
  ansi_c_language.parse(iss, "");
  config.ansi_c.preprocessor=pp;

  symbol_tablet tmp_symbol_table;
  ansi_c_language.typecheck(tmp_symbol_table, "<built-in-library>");

  goto_programt init_instructions;
  exprt value=nil_exprt();
  // locate the body of the newly built start function as well as any
  // additional declarations we might need; the body will then be
  // converted and inserted into the start function
  for(const auto &symbol_pair : tmp_symbol_table.symbols)
  {
    // add __CPROVER_assume if necessary (it might exist already)
    if(
      symbol_pair.first == CPROVER_PREFIX "assume" ||
      symbol_pair.first == CPROVER_PREFIX "input")
      goto_model.symbol_table.add(symbol_pair.second);
    else if(symbol_pair.first == goto_model.goto_functions.entry_point())
    {
      value = symbol_pair.second.value;

      unchecked_replace_symbolt replace;
      replace.insert(ARGC, ns.lookup("argc'").symbol_expr());
      replace.insert(ARGV, ns.lookup("argv'").symbol_expr());
      replace(value);
    }
    else if(
      has_prefix(
        id2string(symbol_pair.first),
        id2string(goto_model.goto_functions.entry_point()) + "::") &&
      goto_model.symbol_table.add(symbol_pair.second))
      UNREACHABLE;
  }
  POSTCONDITION(value.is_not_nil());

  goto_convert(
    to_code(value),
    goto_model.symbol_table,
    init_instructions,
    message_handler,
    main_symbol.mode);

  Forall_goto_program_instructions(it, init_instructions)
  {
    it->source_location.set_file("<built-in-library>");
    it->function=goto_model.goto_functions.entry_point();
  }

  goto_functionst::function_mapt::iterator start_entry=
    goto_model.goto_functions.function_map.find(
      goto_model.goto_functions.entry_point());

  DATA_INVARIANT(
    start_entry!=goto_model.goto_functions.function_map.end() &&
    start_entry->second.body_available(),
    "entry point expected to have a body");

  goto_programt &start=start_entry->second.body;
  goto_programt::targett main_call=start.instructions.begin();
  for(goto_programt::targett end=start.instructions.end();
      main_call!=end;
      ++main_call)
  {
    if(main_call->is_function_call())
    {
      const exprt &func=
        to_code_function_call(main_call->code).function();
      if(func.id()==ID_symbol &&
         to_symbol_expr(func).get_identifier()==main_symbol.name)
        break;
    }
  }
  POSTCONDITION(main_call!=start.instructions.end());

  start.insert_before_swap(main_call, init_instructions);

  // update counters etc.
  remove_skip(start);

  return false;
}
