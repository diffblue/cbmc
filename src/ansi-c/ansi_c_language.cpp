/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "ansi_c_language.h"

#include <cstring>
#include <fstream>
#include <iostream>
#include <sstream>

#include <util/config.h>
#include <util/expr_iterator.h>
#include <util/expr_util.h>
#include <util/get_base_name.h>

#include <linking/linking.h>
#include <linking/remove_internal_symbols.h>

#include "ansi_c_entry_point.h"
#include "ansi_c_typecheck.h"
#include "ansi_c_parser.h"
#include "expr2c.h"
#include "c_preprocess.h"
#include "ansi_c_internal_additions.h"
#include "type2name.h"

std::set<std::string> ansi_c_languaget::extensions() const
{
  return { "c", "i" };
}

void ansi_c_languaget::modules_provided(std::set<std::string> &modules)
{
  modules.insert(get_base_name(parse_path, true));
}

/// ANSI-C preprocessing
bool ansi_c_languaget::preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream)
{
  // stdin?
  if(path.empty())
    return c_preprocess(instream, outstream, get_message_handler());

  return c_preprocess(path, outstream, get_message_handler());
}

bool ansi_c_languaget::parse(
  std::istream &instream,
  const std::string &path)
{
  // store the path
  parse_path=path;

  // preprocessing
  std::ostringstream o_preprocessed;

  if(preprocess(instream, path, o_preprocessed))
    return true;

  std::istringstream i_preprocessed(o_preprocessed.str());

  // parsing

  std::string code;
  ansi_c_internal_additions(code);
  std::istringstream codestr(code);

  ansi_c_parser.clear();
  ansi_c_parser.set_file(ID_built_in);
  ansi_c_parser.in=&codestr;
  ansi_c_parser.set_message_handler(get_message_handler());
  ansi_c_parser.for_has_scope=config.ansi_c.for_has_scope;
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_parser.cpp98=false; // it's not C++
  ansi_c_parser.cpp11=false; // it's not C++
  ansi_c_parser.mode=config.ansi_c.mode;

  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(!result)
  {
    ansi_c_parser.set_line_no(0);
    ansi_c_parser.set_file(path);
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

bool ansi_c_languaget::typecheck(
  symbol_tablet &symbol_table,
  const std::string &module,
  const bool keep_file_local)
{
  symbol_tablet new_symbol_table;

  if(ansi_c_typecheck(
    parse_tree,
    new_symbol_table,
    module,
    get_message_handler()))
  {
    return true;
  }

  remove_internal_symbols(
    new_symbol_table, this->get_message_handler(), keep_file_local);

  if(linking(symbol_table, new_symbol_table, get_message_handler()))
    return true;

  return false;
}

bool ansi_c_languaget::generate_support_functions(
  symbol_tablet &symbol_table)
{
  // This creates __CPROVER_start and __CPROVER_initialize:
  return ansi_c_entry_point(
    symbol_table, get_message_handler(), object_factory_params);
}

// This returns true if the expression [expr] is a call to the
// function with name [function_name]. Note that this doesn't handle
// function pointers.
bool is_call_to_function_with_name(irep_idt function_name, exprt expr)
{
  if(can_cast_expr<side_effect_expr_function_callt>(expr))
  {
    const side_effect_expr_function_callt function_call =
      to_side_effect_expr_function_call(expr);
    const exprt function = function_call.function();

    if(can_cast_expr<symbol_exprt>(function))
    {
      const symbol_exprt function_symbol = to_symbol_expr(function);
      return function_symbol.get_identifier() == function_name;
    }
  }
  return false;
}

// Question: Is there a way to optimize this (Returning a balanced
// tree instead of a chain tree)? Is there a standard function that I
// can call for this?
//
// If this function returns nil expression, it means that no
// (pre/post)condition was aggregated.
exprt condition_conjunction(const exprt::operandst &nil_op)
{
  exprt::operandst op;

  // filter non nil expressions
  std::copy_if(
    nil_op.begin(), nil_op.end(), std::back_inserter(op), [](exprt e) {
      return e.is_not_nil();
    });

  if(op.empty())
  {
    // Question: What is a better way to do this?
    exprt expr = exprt(ID_nil);
    INVARIANT(
      expr.is_nil(),
      "Postcondition conjunction should be nil if no postcondition group was "
      "found.");
    return expr;
    // return make_boolean_expr(true);
  }
  else if(op.size() == 1)
  {
    return op.front();
  }
  else
  {
    // If the first op is trivially true recurse for free
    auto it = op.begin();
    exprt op0 = *it;
    ++it;
    exprt op1 = *it;
    ++it;
    exprt acc = and_exprt(op0, op1);

    for(; it != op.end(); ++it)
    {
      // Is this invariant correct?
      INVARIANT(
        it->is_not_nil(),
        "Conjunction of conditions should never be called with nil arguments");
      acc = and_exprt(acc, *it);
    }

    // This means that we didn't see any non-nil postcondition group
    INVARIANT(
      !acc.is_true(),
      "Assuming that the invariant in the loop holds this should never be the "
      "case.");

    return acc;
  }
}

exprt aggregate_function_preconditions(code_blockt function_body)
{
  exprt::operandst preconditions;
  for(depth_iteratort it = function_body.depth_begin();
      it != function_body.depth_end();
      ++it)
  {
    if(is_call_to_function_with_name(CPROVER_PREFIX "precondition", *it))
    {
      const side_effect_expr_function_callt function_call =
        to_side_effect_expr_function_call(*it);
      exprt condition = function_call.arguments().front();
      preconditions.push_back(condition);
    }
  }
  // WARNING: In order for it to make sense to return the conjunction
  // of the preconditions, they have to be in the beginning of the
  // function body before anythinf else.
  //
  // TODO: Maybe I should add a check to ensure that

  return condition_conjunction(preconditions);
}

// Extends the specified contract (requires/ensures) of the function
// declaration with the given condition.
void extend_contract(
  const irep_namet &contract_name,
  const exprt condition,
  ansi_c_declarationt *declaration)
{
  exprt old_contract =
    static_cast<const exprt &>(declaration->find(contract_name));
  exprt new_contract;
  if(old_contract.is_nil())
    new_contract = condition;
  else
    new_contract = and_exprt(old_contract, condition);
  declaration->add(contract_name, new_contract);
}

bool ansi_c_languaget::preconditions_to_contracts()
{
  for(std::list<ansi_c_declarationt>::iterator it = parse_tree.items.begin();
      it != parse_tree.items.end();
      ++it)
  {
    if(!it->declarators().empty())
    {
      ansi_c_declaratort decl = it->declarator();
      if(can_cast_expr<code_blockt>(decl.value()))
      {
        code_blockt function_body = to_code_block(to_code(decl.value()));
        exprt precondition = aggregate_function_preconditions(function_body);

        if(precondition.is_not_nil())
          extend_contract(ID_C_spec_requires, precondition, &(*it));
      }
    }
  }

  // TODO: Make a check for preconditions and ensure that they happen
  // before anything else in the code. Should this check just be that
  // the preconditions are a prefix of the function body?

  return false;
}

void ansi_c_languaget::show_parse(std::ostream &out)
{
  parse_tree.output(out);
}

std::unique_ptr<languaget> new_ansi_c_language()
{
  return util_make_unique<ansi_c_languaget>();
}

bool ansi_c_languaget::from_expr(
  const exprt &expr,
  std::string &code,
  const namespacet &ns)
{
  code=expr2c(expr, ns);
  return false;
}

bool ansi_c_languaget::from_type(
  const typet &type,
  std::string &code,
  const namespacet &ns)
{
  code=type2c(type, ns);
  return false;
}

bool ansi_c_languaget::type_to_name(
  const typet &type,
  std::string &name,
  const namespacet &ns)
{
  name=type2name(type, ns);
  return false;
}

bool ansi_c_languaget::to_expr(
  const std::string &code,
  const std::string &,
  exprt &expr,
  const namespacet &ns)
{
  expr.make_nil();

  // no preprocessing yet...

  std::istringstream i_preprocessed(
    "void __my_expression = (void) (\n"+code+"\n);");

  // parsing

  ansi_c_parser.clear();
  ansi_c_parser.set_file(irep_idt());
  ansi_c_parser.in=&i_preprocessed;
  ansi_c_parser.set_message_handler(get_message_handler());
  ansi_c_parser.mode=config.ansi_c.mode;
  ansi_c_parser.ts_18661_3_Floatn_types=config.ansi_c.ts_18661_3_Floatn_types;
  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result=true;
  else
  {
    expr=ansi_c_parser.parse_tree.items.front().declarator().value();

    // typecheck it
    result=ansi_c_typecheck(expr, get_message_handler(), ns);
  }

  // save some memory
  ansi_c_parser.clear();

  // now remove that (void) cast
  if(expr.id()==ID_typecast &&
     expr.type().id()==ID_empty &&
     expr.operands().size()==1)
    expr=expr.op0();

  return result;
}

ansi_c_languaget::~ansi_c_languaget()
{
}
