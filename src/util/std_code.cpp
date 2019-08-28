/*******************************************************************\

Module: Data structures representing statements in a program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Data structure representing different types of statements in a program

#include "std_code.h"

#include "arith_tools.h"
#include "c_types.h"
#include "std_expr.h"
#include "string_constant.h"

/// If this `codet` is a \ref code_blockt (i.e.\ it represents a block of
/// statements), return the unmodified input. Otherwise (i.e.\ the `codet`
/// represents a single statement), convert it to a \ref code_blockt with the
/// original statement as its only operand and return the result.
code_blockt &codet::make_block()
{
  if(get_statement()==ID_block)
    return static_cast<code_blockt &>(*this);

  exprt tmp;
  tmp.swap(*this);

  *this = codet(ID_block);
  add_to_operands(std::move(tmp));

  return static_cast<code_blockt &>(*this);
}

/// In the case of a `codet` type that represents multiple statements, return
/// the first of them. Otherwise return the `codet` itself.
codet &codet::first_statement()
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(op0()).first_statement();
    else if(statement==ID_label)
      return to_code(op0()).first_statement();
  }

  return *this;
}

/// \copydoc first_statement()
const codet &codet::first_statement() const
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(op0()).first_statement();
    else if(statement==ID_label)
      return to_code(op0()).first_statement();
  }

  return *this;
}

/// In the case of a `codet` type that represents multiple statements, return
/// the last of them. Otherwise return the `codet` itself.
codet &codet::last_statement()
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(operands().back()).last_statement();
    else if(statement==ID_label)
      return to_code(operands().back()).last_statement();
  }

  return *this;
}

/// \copydoc last_statement()
const codet &codet::last_statement() const
{
  const irep_idt &statement=get_statement();

  if(has_operands())
  {
    if(statement==ID_block)
      return to_code(operands().back()).last_statement();
    else if(statement==ID_label)
      return to_code(operands().back()).last_statement();
  }

  return *this;
}

/// Add all the codets from extra_block to the current code_blockt
/// \param extra_block: The input code_blockt
void code_blockt::append(const code_blockt &extra_block)
{
  statements().reserve(statements().size() + extra_block.statements().size());

  for(const auto &statement : extra_block.statements())
  {
    add(statement);
  }
}

codet &code_blockt::find_last_statement()
{
  codet *last=this;

  while(true)
  {
    const irep_idt &statement=last->get_statement();

    if(statement==ID_block &&
       !to_code_block(*last).statements().empty())
    {
      last=&to_code_block(*last).statements().back();
    }
    else if(statement==ID_label)
    {
      last = &(to_code_label(*last).code());
    }
    else
      break;
  }

  return *last;
}

code_blockt create_fatal_assertion(
  const exprt &condition, const source_locationt &loc)
{
  code_blockt result({code_assertt(condition), code_assumet(condition)});

  for(auto &op : result.statements())
    op.add_source_location() = loc;

  result.add_source_location() = loc;

  return result;
}

std::vector<irep_idt> code_function_bodyt::get_parameter_identifiers() const
{
  const auto &sub = find(ID_parameters).get_sub();
  std::vector<irep_idt> result;
  result.reserve(sub.size());
  for(const auto &s : sub)
    result.push_back(s.get(ID_identifier));
  return result;
}

void code_function_bodyt::set_parameter_identifiers(
  const std::vector<irep_idt> &parameter_identifiers)
{
  auto &sub = add(ID_parameters).get_sub();
  sub.reserve(parameter_identifiers.size());
  for(const auto &id : parameter_identifiers)
  {
    sub.push_back(irept(ID_parameter));
    sub.back().set(ID_identifier, id);
  }
}

code_inputt::code_inputt(
  std::vector<exprt> arguments,
  optionalt<source_locationt> location)
  : codet{ID_input, std::move(arguments)}
{
  if(location)
    add_source_location() = std::move(*location);
  check(*this, validation_modet::INVARIANT);
}

code_inputt::code_inputt(
  const irep_idt &description,
  exprt expression,
  optionalt<source_locationt> location)
  : code_inputt{{address_of_exprt(index_exprt(
                   string_constantt(description),
                   from_integer(0, index_type()))),
                 std::move(expression)},
                std::move(location)}
{
}

void code_inputt::check(const codet &code, const validation_modet vm)
{
  DATA_CHECK(
    vm, code.operands().size() >= 2, "input must have at least two operands");
}

code_outputt::code_outputt(
  std::vector<exprt> arguments,
  optionalt<source_locationt> location)
  : codet{ID_output, std::move(arguments)}
{
  if(location)
    add_source_location() = std::move(*location);
  check(*this, validation_modet::INVARIANT);
}

code_outputt::code_outputt(
  const irep_idt &description,
  exprt expression,
  optionalt<source_locationt> location)
  : code_outputt{{address_of_exprt(index_exprt(
                    string_constantt(description),
                    from_integer(0, index_type()))),
                  std::move(expression)},
                 std::move(location)}
{
}

void code_outputt::check(const codet &code, const validation_modet vm)
{
  DATA_CHECK(
    vm, code.operands().size() >= 2, "output must have at least two operands");
}

code_fort code_fort::from_index_bounds(
  exprt start_index,
  exprt end_index,
  symbol_exprt loop_index,
  codet body,
  source_locationt location)
{
  PRECONDITION(start_index.type() == loop_index.type());
  PRECONDITION(end_index.type() == loop_index.type());
  side_effect_expr_assignt inc(
    loop_index,
    plus_exprt(loop_index, from_integer(1, loop_index.type())),
    location);

  return code_fort{
    code_assignt{loop_index, std::move(start_index)},
    binary_relation_exprt{loop_index, ID_lt, std::move(end_index)},
    std::move(inc),
    std::move(body)};
}
