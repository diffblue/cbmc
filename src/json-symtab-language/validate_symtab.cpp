/*******************************************************************\

Module: Validation of symbol tables and goto functions read from JSON

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Validation of symbol tables and goto functions read from JSON

#include "validate_symtab.h"

#include <util/exception_utils.h>
#include <util/namespace.h>
#include <util/prefix.h>
#include <util/symbol_table.h>
#include <util/validate_expressions.h>
#include <util/validate_types.h>

#include <goto-programs/goto_functions.h>

#include <ansi-c/c_expr.h>

#include <unordered_set>

namespace
{
/// Walks a symbol's type and value, knowing for each position whether it
/// holds a type or an expression, and checks each type and expression found.
/// json_irept::convert_from_json builds whatever the input contains, so the
/// walk must not rely on expressions having a type, nor on the number of
/// operands or subtypes.
class symtab_validatort
{
public:
  /// \param ns: namespace to validate against; nullptr to only check the
  ///   structure of types and expressions, which needs no namespace
  explicit symtab_validatort(const namespacet *ns) : ns(ns)
  {
  }

  /// Check \p expr, its operands, its type, and any types and expressions
  /// in its named sub-trees.
  void expression(const exprt &expr);
  /// Check \p type, its subtypes, and any types and expressions in its named
  /// sub-trees (such as array sizes, components, parameters and contract
  /// clauses).
  void type(const typet &type);

private:
  const namespacet *const ns;
  static constexpr validation_modet vm = validation_modet::EXCEPTION;
  std::unordered_set<const void *> visited_expressions;
  std::unordered_set<const void *> visited_types;

  /// Check \p expr itself, but not its operands or type.
  void check_node(const exprt &expr) const;
  /// A contract clause is either an expression or a list of expressions.
  void clauses(const irept &irep);
  /// A position of which we do not know whether it holds an expression: treat
  /// it as one if it has a type, and otherwise look for expressions inside.
  /// Leaves are not dispatched by their id, as they may well be names such as
  /// `if` or `plus`.
  void unknown(const irept &irep);
};

/// True if \p irep only carries an id, as is the case for attributes such as
/// identifiers, widths or component names.
bool is_leaf(const irept &irep)
{
  return irep.get_sub().empty() && irep.get_named_sub().empty();
}

/// Named sub-trees holding contract clauses, which are expressions whether or
/// not they have a type.
bool is_clause(const irep_idt &name)
{
  return has_prefix(id2string(name), "#spec_");
}

/// Expressions declared in ansi-c, which the dispatch table in
/// util/validate_expressions.cpp cannot cover as util must not depend on
/// ansi-c.
void check_ansi_c_expression(const exprt &expr, const validation_modet vm)
{
  if(expr.id() == ID_conditional_target_group)
    conditional_target_group_exprt::check(expr, vm);
  else if(expr.id() == ID_shuffle_vector)
    shuffle_vector_exprt::check(expr, vm);
  else if(expr.id() == ID_bit_cast)
    bit_cast_exprt::check(expr, vm);
  else if(expr.id() == ID_enum_is_in_range)
    enum_is_in_range_exprt::check(expr, vm);
  else if(expr.id() == ID_old || expr.id() == ID_loop_entry)
    history_exprt::check(expr, vm);
}

void symtab_validatort::check_node(const exprt &expr) const
{
  check_expr(expr, vm);
  check_ansi_c_expression(expr, vm);
  if(ns != nullptr)
    validate_expr(expr, *ns, vm);
}

void symtab_validatort::expression(const exprt &expr)
{
  if(!visited_expressions.insert(&expr.read()).second)
    return;

  // Check operands and type first, as checks of this node may rely on them.
  for(const auto &op : expr.get_sub())
    expression(static_cast<const exprt &>(op));
  for(const auto &named_sub : expr.get_named_sub())
  {
    if(named_sub.second.is_nil() || is_leaf(named_sub.second))
      continue;
    else if(named_sub.first == ID_type || named_sub.first == ID_C_c_sizeof_type)
      type(static_cast<const typet &>(named_sub.second));
    else if(is_clause(named_sub.first))
      clauses(named_sub.second);
    else if(named_sub.first != ID_C_source_location)
      unknown(named_sub.second);
  }

  check_node(expr);
}

void symtab_validatort::type(const typet &type)
{
  if(!visited_types.insert(&type.read()).second)
    return;

  for(const auto &subtype : type.get_sub())
    this->type(static_cast<const typet &>(subtype));
  for(const auto &named_sub : type.get_named_sub())
  {
    if(named_sub.second.is_nil() || is_leaf(named_sub.second))
      continue;
    else if(named_sub.first == ID_size)
      expression(static_cast<const exprt &>(named_sub.second));
    else if(named_sub.first == ID_return_type)
      this->type(static_cast<const typet &>(named_sub.second));
    else if(
      named_sub.first == ID_components || named_sub.first == ID_parameters)
    {
      // struct/union components and code-type parameters: the type of each
      // is in a type position
      for(const auto &element : named_sub.second.get_sub())
      {
        for(const auto &element_sub : element.get_named_sub())
        {
          if(element_sub.second.is_nil() || is_leaf(element_sub.second))
            continue;
          else if(element_sub.first == ID_type)
            this->type(static_cast<const typet &>(element_sub.second));
          else if(element_sub.first != ID_C_source_location)
            unknown(element_sub.second);
        }
      }
    }
    else if(is_clause(named_sub.first))
      clauses(named_sub.second);
    else if(named_sub.first != ID_C_source_location)
      unknown(named_sub.second);
  }

  check_type(type, vm);
  if(ns != nullptr)
    validate_type(type, *ns, vm);
}

void symtab_validatort::clauses(const irept &irep)
{
  if(irep.find(ID_type).is_not_nil())
    expression(static_cast<const exprt &>(irep));
  else
  {
    for(const auto &clause : irep.get_sub())
      expression(static_cast<const exprt &>(clause));
  }
}

void symtab_validatort::unknown(const irept &irep)
{
  if(irep.find(ID_type).is_not_nil())
  {
    expression(static_cast<const exprt &>(irep));
    return;
  }

  for(const auto &sub : irep.get_sub())
  {
    if(!is_leaf(sub))
      unknown(sub);
  }
  for(const auto &named_sub : irep.get_named_sub())
  {
    if(named_sub.first != ID_C_source_location && !is_leaf(named_sub.second))
      unknown(named_sub.second);
  }
}

} // namespace

/// Apply \p validator to the type and the value of \p symbol, and report a
/// malformed type or expression as invalid input.
static void validate_symbol(symtab_validatort &validator, const symbolt &symbol)
{
  try
  {
    validator.type(symbol.type);
    if(symbol.value.is_not_nil())
      validator.expression(symbol.value);
  }
  catch(const incorrect_goto_program_exceptiont &e)
  {
    throw invalid_input_exceptiont{
      "malformed symbol table entry `" + id2string(symbol.name) +
      "': " + e.what()};
  }
}

void check_symbol_table_structure(const symbol_tablet &symbol_table)
{
  symtab_validatort validator{nullptr};
  for(const auto &symbol_pair : symbol_table.symbols)
    validate_symbol(validator, symbol_pair.second);
}

void validate_symbol_table(
  const symbol_tablet &symbol_table,
  const char *symbol_names_prefix)
{
  const namespacet ns{symbol_table};
  symtab_validatort validator{&ns};
  for(const auto &symbol_pair : symbol_table.symbols)
  {
    if(has_prefix(id2string(symbol_pair.first), symbol_names_prefix))
      validate_symbol(validator, symbol_pair.second);
  }
}

void validate_goto_functions(
  const goto_functionst &goto_functions,
  const namespacet &ns)
{
  symtab_validatort validator{&ns};
  for(const auto &function_pair : goto_functions.function_map)
  {
    try
    {
      for(const auto &instruction : function_pair.second.body.instructions)
      {
        if(instruction.code().is_not_nil())
          validator.expression(instruction.code());
        if(instruction.has_condition())
          validator.expression(instruction.condition());
      }
    }
    catch(const incorrect_goto_program_exceptiont &e)
    {
      throw invalid_input_exceptiont{
        "malformed goto function `" + id2string(function_pair.first) +
        "': " + e.what()};
    }
  }
}
