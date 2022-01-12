/*******************************************************************\

Module: Predicates to specify memory footprint in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Predicates to specify memory footprint in function contracts

#include "memory_predicates.h"

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/expr2c.h>

#include <goto-programs/goto_convert_functions.h>

#include <linking/static_lifetime_init.h>

#include <util/config.h>
#include <util/prefix.h>

bool return_value_visitort::found_return_value()
{
  return found;
}

void return_value_visitort::operator()(const exprt &exp)
{
  if(exp.id() != ID_symbol)
    return;
  const symbol_exprt &sym = to_symbol_expr(exp);
  found |= sym.get_identifier() == CPROVER_PREFIX "return_value";
}

std::set<irep_idt> &functions_in_scope_visitort::function_calls()
{
  return function_set;
}

void functions_in_scope_visitort::operator()(const goto_programt &prog)
{
  forall_goto_program_instructions(ins, prog)
  {
    if(ins->is_function_call())
    {
      const auto &function = ins->call_function();

      if(function.id() != ID_symbol)
      {
        log.error().source_location = ins->source_location();
        log.error() << "Function pointer used in function invoked by "
                       "function contract: "
                    << messaget::eom;
        throw 0;
      }
      else
      {
        const irep_idt &fun_name = to_symbol_expr(function).get_identifier();
        if(function_set.find(fun_name) == function_set.end())
        {
          function_set.insert(fun_name);
          auto called_fun = goto_functions.function_map.find(fun_name);
          if(called_fun == goto_functions.function_map.end())
          {
            log.warning() << "Could not find function '" << fun_name
                          << "' in goto-program." << messaget::eom;
            throw 0;
          }
          if(called_fun->second.body_available())
          {
            const goto_programt &program = called_fun->second.body;
            (*this)(program);
          }
          else
          {
            log.warning() << "No body for function: " << fun_name
                          << "invoked from function contract." << messaget::eom;
          }
        }
      }
    }
  }
}

std::set<goto_programt::targett> &find_is_fresh_calls_visitort::is_fresh_calls()
{
  return function_set;
}

void find_is_fresh_calls_visitort::clear_set()
{
  function_set.clear();
}

void find_is_fresh_calls_visitort::operator()(goto_programt &prog)
{
  Forall_goto_program_instructions(ins, prog)
  {
    if(ins->is_function_call())
    {
      const auto &function = ins->call_function();

      if(function.id() == ID_symbol)
      {
        const irep_idt &fun_name = to_symbol_expr(function).get_identifier();

        if(fun_name == (CPROVER_PREFIX + std::string("is_fresh")))
        {
          function_set.insert(ins);
        }
      }
    }
  }
}

void is_fresh_baset::update_requires(goto_programt &requires)
{
  find_is_fresh_calls_visitort requires_visitor;
  requires_visitor(requires);
  for(auto it : requires_visitor.is_fresh_calls())
  {
    create_requires_fn_call(it);
  }
}

void is_fresh_baset::update_ensures(goto_programt &ensures)
{
  find_is_fresh_calls_visitort ensures_visitor;
  ensures_visitor(ensures);
  for(auto it : ensures_visitor.is_fresh_calls())
  {
    create_ensures_fn_call(it);
  }
}

//
//
// Code largely copied from model_argc_argv.cpp
//
//

void is_fresh_baset::add_declarations(const std::string &decl_string)
{
  log.debug() << "Creating declarations: \n" << decl_string << "\n";

  std::istringstream iss(decl_string);

  ansi_c_languaget ansi_c_language;
  ansi_c_language.set_message_handler(log.get_message_handler());
  configt::ansi_ct::preprocessort pp = config.ansi_c.preprocessor;
  config.ansi_c.preprocessor = configt::ansi_ct::preprocessort::NONE;
  ansi_c_language.parse(iss, "");
  config.ansi_c.preprocessor = pp;

  symbol_tablet tmp_symbol_table;
  ansi_c_language.typecheck(tmp_symbol_table, "<built-in-library>");
  exprt value = nil_exprt();

  goto_functionst tmp_functions;

  // Add the new functions into the goto functions table.
  parent.get_goto_functions().function_map[ensures_fn_name].copy_from(
    tmp_functions.function_map[ensures_fn_name]);

  parent.get_goto_functions().function_map[requires_fn_name].copy_from(
    tmp_functions.function_map[requires_fn_name]);

  for(const auto &symbol_pair : tmp_symbol_table.symbols)
  {
    if(
      symbol_pair.first == memmap_name ||
      symbol_pair.first == ensures_fn_name ||
      symbol_pair.first == requires_fn_name || symbol_pair.first == "malloc")
    {
      this->parent.get_symbol_table().insert(symbol_pair.second);
    }
    // Parameters are stored as scoped names in the symbol table.
    else if(
      (has_prefix(
         id2string(symbol_pair.first), id2string(ensures_fn_name) + "::") ||
       has_prefix(
         id2string(symbol_pair.first), id2string(requires_fn_name) + "::")) &&
      parent.get_symbol_table().add(symbol_pair.second))
    {
      UNREACHABLE;
    }
  }

  if(parent.get_goto_functions().function_map.erase(INITIALIZE_FUNCTION) != 0)
  {
    static_lifetime_init(
      parent.get_symbol_table(),
      parent.get_symbol_table().lookup_ref(INITIALIZE_FUNCTION).location);
    goto_convert(
      INITIALIZE_FUNCTION,
      parent.get_symbol_table(),
      parent.get_goto_functions(),
      log.get_message_handler());
    parent.get_goto_functions().update();
  }
}

void is_fresh_baset::update_fn_call(
  goto_programt::targett &ins,
  const std::string &fn_name,
  bool add_address_of)
{
  // adjusting the expression for the first argument, if required
  if(add_address_of)
  {
    INVARIANT(
      as_const(*ins).call_arguments().size() > 0,
      "Function must have arguments");
    ins->call_arguments()[0] = address_of_exprt(ins->call_arguments()[0]);
  }

  // fixing the function name.
  to_symbol_expr(ins->call_function()).set_identifier(fn_name);
}

/* Declarations for contract enforcement */

is_fresh_enforcet::is_fresh_enforcet(
  code_contractst &_parent,
  messaget _log,
  irep_idt _fun_id)
  : is_fresh_baset(_parent, _log, _fun_id)
{
  std::stringstream ssreq, ssensure, ssmemmap;
  ssreq << CPROVER_PREFIX << fun_id << "_requires_is_fresh";
  this->requires_fn_name = ssreq.str();

  ssensure << CPROVER_PREFIX << fun_id << "_ensures_is_fresh";
  this->ensures_fn_name = ssensure.str();

  ssmemmap << CPROVER_PREFIX << fun_id << "_memory_map";
  this->memmap_name = ssmemmap.str();
}

void is_fresh_enforcet::create_declarations()
{
  std::ostringstream oss;
  std::string cprover_prefix(CPROVER_PREFIX);
  oss << "static _Bool " << memmap_name
      << "[" + cprover_prefix + "constant_infinity_uint]; \n"
      << "\n"
      << "_Bool " << requires_fn_name
      << "(void **elem, " + cprover_prefix + "size_t size) { \n"
      << "   *elem = malloc(size); \n"
      << "   if (!*elem || " << memmap_name
      << "[" + cprover_prefix + "POINTER_OBJECT(*elem)]) return 0; \n"
      << "   " << memmap_name << "[" + cprover_prefix
      << "POINTER_OBJECT(*elem)] = 1; \n"
      << "   return 1; \n"
      << "} \n"
      << "\n"
      << "_Bool " << ensures_fn_name
      << "(void *elem, " + cprover_prefix + "size_t size) { \n"
      << "   _Bool ok = (!" << memmap_name
      << "[" + cprover_prefix + "POINTER_OBJECT(elem)] && "
      << cprover_prefix + "r_ok(elem, size)); \n"
      << "   " << memmap_name << "[" + cprover_prefix
      << "POINTER_OBJECT(elem)] = 1; \n"
      << "   return ok; \n"
      << "}";

  add_declarations(oss.str());
}

void is_fresh_enforcet::create_requires_fn_call(goto_programt::targett &ins)
{
  update_fn_call(ins, requires_fn_name, true);
}

void is_fresh_enforcet::create_ensures_fn_call(goto_programt::targett &ins)
{
  update_fn_call(ins, ensures_fn_name, false);
}

/* Declarations for contract replacement: note that there may be several
   instances of the same function called in a particular context, so care must be taken
   that the 'call' functions and global data structure are unique for each instance.
   This is why we check that the symbols are unique for each such declaration.  */

std::string unique_symbol(const symbol_tablet &tbl, const std::string &original)
{
  auto size = tbl.next_unused_suffix(original);
  return original + std::to_string(size);
}

is_fresh_replacet::is_fresh_replacet(
  code_contractst &_parent,
  messaget _log,
  irep_idt _fun_id)
  : is_fresh_baset(_parent, _log, _fun_id)
{
  std::stringstream ssreq, ssensure, ssmemmap;
  ssreq /* << CPROVER_PREFIX */ << fun_id << "_call_requires_is_fresh";
  this->requires_fn_name =
    unique_symbol(parent.get_symbol_table(), ssreq.str());

  ssensure /* << CPROVER_PREFIX */ << fun_id << "_call_ensures_is_fresh";
  this->ensures_fn_name =
    unique_symbol(parent.get_symbol_table(), ssensure.str());

  ssmemmap /* << CPROVER_PREFIX */ << fun_id << "_memory_map";
  this->memmap_name = unique_symbol(parent.get_symbol_table(), ssmemmap.str());
}

void is_fresh_replacet::create_declarations()
{
  std::ostringstream oss;
  std::string cprover_prefix(CPROVER_PREFIX);
  oss << "static _Bool " << memmap_name
      << "[" + cprover_prefix + "constant_infinity_uint]; \n"
      << "\n"
      << "static _Bool " << requires_fn_name
      << "(void *elem, " + cprover_prefix + "size_t size) { \n"
      << "  _Bool r_ok = " + cprover_prefix + "r_ok(elem, size); \n"
      << "  if (" << memmap_name
      << "[" + cprover_prefix + "POINTER_OBJECT(elem)]"
      << " != 0 || !r_ok)  return 0; \n"
      << "  " << memmap_name << "["
      << cprover_prefix + "POINTER_OBJECT(elem)] = 1; \n"
      << "  return 1; \n"
      << "} \n"
      << " \n"
      << "_Bool " << ensures_fn_name
      << "(void **elem, " + cprover_prefix + "size_t size) { \n"
      << "  *elem = malloc(size); \n"
      << "  return (*elem != 0); \n"
      << "} \n";

  add_declarations(oss.str());
}

void is_fresh_replacet::create_requires_fn_call(goto_programt::targett &ins)
{
  update_fn_call(ins, requires_fn_name, false);
}

void is_fresh_replacet::create_ensures_fn_call(goto_programt::targett &ins)
{
  update_fn_call(ins, ensures_fn_name, true);
}
