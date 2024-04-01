/*******************************************************************\

Module: Predicates to specify memory footprint in function contracts.

Author: Felipe R. Monteiro

Date: July 2021

\*******************************************************************/

/// \file
/// Predicates to specify memory footprint in function contracts

#include "memory_predicates.h"

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/fresh_symbol.h>
#include <util/prefix.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/goto-conversion/goto_convert_functions.h>
#include <linking/static_lifetime_init.h>

#include "instrument_spec_assigns.h"
#include "utils.h"

std::set<irep_idt> &functions_in_scope_visitort::function_calls()
{
  return function_set;
}

void functions_in_scope_visitort::operator()(const goto_programt &prog)
{
  messaget log{message_handler};

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

std::set<goto_programt::targett, goto_programt::target_less_than> &
find_is_fresh_calls_visitort::is_fresh_calls()
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

void is_fresh_baset::update_requires(goto_programt &requires_)
{
  find_is_fresh_calls_visitort requires_visitor;
  requires_visitor(requires_);
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

array_typet is_fresh_baset::get_memmap_type()
{
  return array_typet(unsigned_char_type(), infinity_exprt(size_type()));
}

void is_fresh_baset::add_memory_map_decl(goto_programt &program)
{
  source_locationt source_location;
  add_pragma_disable_assigns_check(source_location);
  auto memmap_type = get_memmap_type();
  program.add(
    goto_programt::make_decl(memmap_symbol.symbol_expr(), source_location));
  program.add(goto_programt::make_assignment(
    memmap_symbol.symbol_expr(),
    array_of_exprt(
      from_integer(0, get_memmap_type().element_type()), get_memmap_type()),
    source_location));
}

void is_fresh_baset::add_memory_map_dead(goto_programt &program)
{
  source_locationt source_location;
  add_pragma_disable_assigns_check(source_location);
  program.add(
    goto_programt::make_dead(memmap_symbol.symbol_expr(), source_location));
}

void is_fresh_baset::add_declarations(const std::string &decl_string)
{
  messaget log{message_handler};
  log.debug() << "Creating declarations: \n" << decl_string << "\n";

  std::istringstream iss(decl_string);

  ansi_c_languaget ansi_c_language;
  configt::ansi_ct::preprocessort pp = config.ansi_c.preprocessor;
  config.ansi_c.preprocessor = configt::ansi_ct::preprocessort::NONE;
  ansi_c_language.parse(iss, "", log.get_message_handler());
  config.ansi_c.preprocessor = pp;

  symbol_tablet tmp_symbol_table;
  ansi_c_language.typecheck(
    tmp_symbol_table, "<built-in-library>", log.get_message_handler());
  exprt value = nil_exprt();

  goto_functionst tmp_functions;

  // Add the new functions into the goto functions table.
  goto_model.goto_functions.function_map[ensures_fn_name].copy_from(
    tmp_functions.function_map[ensures_fn_name]);

  goto_model.goto_functions.function_map[requires_fn_name].copy_from(
    tmp_functions.function_map[requires_fn_name]);

  for(const auto &symbol_pair : tmp_symbol_table.symbols)
  {
    if(
      symbol_pair.first == memmap_name ||
      symbol_pair.first == ensures_fn_name ||
      symbol_pair.first == requires_fn_name || symbol_pair.first == "malloc")
    {
      goto_model.symbol_table.insert(symbol_pair.second);
    }
    // Parameters are stored as scoped names in the symbol table.
    else if(
      (has_prefix(
         id2string(symbol_pair.first), id2string(ensures_fn_name) + "::") ||
       has_prefix(
         id2string(symbol_pair.first), id2string(requires_fn_name) + "::")) &&
      goto_model.symbol_table.add(symbol_pair.second))
    {
      UNREACHABLE;
    }
  }

  if(goto_model.can_produce_function(INITIALIZE_FUNCTION))
    recreate_initialize_function(goto_model, message_handler);
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

  // pass the memory mmap
  ins->call_arguments().push_back(address_of_exprt(
    index_exprt(memmap_symbol.symbol_expr(), from_integer(0, c_index_type()))));
}

/* Declarations for contract enforcement */

is_fresh_enforcet::is_fresh_enforcet(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const irep_idt &_fun_id)
  : is_fresh_baset(goto_model, message_handler, _fun_id)
{
  std::stringstream ssreq, ssensure, ssmemmap;
  ssreq << CPROVER_PREFIX "enforce_requires_is_fresh";
  this->requires_fn_name = ssreq.str();

  ssensure << CPROVER_PREFIX "enforce_ensures_is_fresh";
  this->ensures_fn_name = ssensure.str();

  ssmemmap << CPROVER_PREFIX "is_fresh_memory_map_" << fun_id;
  this->memmap_name = ssmemmap.str();

  const auto &mode = goto_model.symbol_table.lookup_ref(_fun_id).mode;
  this->memmap_symbol = get_fresh_aux_symbol(
    get_memmap_type(),
    "",
    this->memmap_name,
    source_locationt(),
    mode,
    goto_model.symbol_table);
}

void is_fresh_enforcet::create_declarations()
{
  // Check if symbols are already declared
  if(goto_model.symbol_table.has_symbol(requires_fn_name))
    return;

  std::ostringstream oss;
  std::string cprover_prefix(CPROVER_PREFIX);
  oss << "_Bool " << requires_fn_name
      << "(void **elem, " + cprover_prefix + "size_t size, _Bool *mmap) { \n"
      << "#pragma CPROVER check push\n"
      << "#pragma CPROVER check disable \"pointer\"\n"
      << "#pragma CPROVER check disable \"pointer-primitive\"\n"
      << "#pragma CPROVER check disable \"pointer-overflow\"\n"
      << "#pragma CPROVER check disable \"signed-overflow\"\n"
      << "#pragma CPROVER check disable \"unsigned-overflow\"\n"
      << "#pragma CPROVER check disable \"conversion\"\n"
      << "   *elem = malloc(size); \n"
      << "   if (!*elem) return 0; \n"
      << "   mmap[" + cprover_prefix + "POINTER_OBJECT(*elem)] = 1; \n"
      << "   return 1; \n"
      << "#pragma CPROVER check pop\n"
      << "} \n"
      << "\n"
      << "_Bool " << ensures_fn_name
      << "(void *elem, " + cprover_prefix + "size_t size, _Bool *mmap) { \n"
      << "#pragma CPROVER check push\n"
      << "#pragma CPROVER check disable \"pointer\"\n"
      << "#pragma CPROVER check disable \"pointer-primitive\"\n"
      << "#pragma CPROVER check disable \"pointer-overflow\"\n"
      << "#pragma CPROVER check disable \"signed-overflow\"\n"
      << "#pragma CPROVER check disable \"unsigned-overflow\"\n"
      << "#pragma CPROVER check disable \"conversion\"\n"
      << "   _Bool ok = (!mmap[" + cprover_prefix + "POINTER_OBJECT(elem)] && "
      << cprover_prefix + "r_ok(elem, size)); \n"
      << "   mmap[" + cprover_prefix << "POINTER_OBJECT(elem)] = 1; \n"
      << "   return ok; \n"
      << "#pragma CPROVER check pop\n"
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

is_fresh_replacet::is_fresh_replacet(
  goto_modelt &goto_model,
  message_handlert &message_handler,
  const irep_idt &_fun_id)
  : is_fresh_baset(goto_model, message_handler, _fun_id)
{
  std::stringstream ssreq, ssensure, ssmemmap;
  ssreq << CPROVER_PREFIX "replace_requires_is_fresh";
  this->requires_fn_name = ssreq.str();

  ssensure << CPROVER_PREFIX "replace_ensures_is_fresh";
  this->ensures_fn_name = ssensure.str();

  ssmemmap << CPROVER_PREFIX "is_fresh_memory_map_" << fun_id;
  this->memmap_name = ssmemmap.str();

  const auto &mode = goto_model.symbol_table.lookup_ref(_fun_id).mode;
  this->memmap_symbol = get_fresh_aux_symbol(
    get_memmap_type(),
    "",
    this->memmap_name,
    source_locationt(),
    mode,
    goto_model.symbol_table);
}

void is_fresh_replacet::create_declarations()
{
  // Check if symbols are already declared
  if(goto_model.symbol_table.has_symbol(requires_fn_name))
    return;

  std::ostringstream oss;
  std::string cprover_prefix(CPROVER_PREFIX);
  oss << "static _Bool " << requires_fn_name
      << "(void *elem, " + cprover_prefix + "size_t size, _Bool *mmap) { \n"
      << "#pragma CPROVER check push\n"
      << "#pragma CPROVER check disable \"pointer\"\n"
      << "#pragma CPROVER check disable \"pointer-primitive\"\n"
      << "#pragma CPROVER check disable \"pointer-overflow\"\n"
      << "#pragma CPROVER check disable \"signed-overflow\"\n"
      << "#pragma CPROVER check disable \"unsigned-overflow\"\n"
      << "#pragma CPROVER check disable \"conversion\"\n"
      << "  _Bool r_ok = " + cprover_prefix + "r_ok(elem, size); \n"
      << "  if (mmap[" + cprover_prefix + "POINTER_OBJECT(elem)]"
      << " != 0 || !r_ok)  return 0; \n"
      << "  mmap[" << cprover_prefix + "POINTER_OBJECT(elem)] = 1; \n"
      << "  return 1; \n"
      << "#pragma CPROVER check pop\n"
      << "} \n"
      << " \n"
      << "_Bool " << ensures_fn_name
      << "(void **elem, " + cprover_prefix + "size_t size, _Bool *mmap) { \n"
      << "#pragma CPROVER check push\n"
      << "#pragma CPROVER check disable \"pointer\"\n"
      << "#pragma CPROVER check disable \"pointer-primitive\"\n"
      << "#pragma CPROVER check disable \"pointer-overflow\"\n"
      << "#pragma CPROVER check disable \"signed-overflow\"\n"
      << "#pragma CPROVER check disable \"unsigned-overflow\"\n"
      << "#pragma CPROVER check disable \"conversion\"\n"
      << "  *elem = malloc(size); \n"
      << "  return (*elem != 0); \n"
      << "#pragma CPROVER check pop\n"
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
