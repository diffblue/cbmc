/*******************************************************************\

Module: Inline assembly: lowering context

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// The state of lowering one inline assembly statement

#include <util/arith_tools.h>
#include <util/bitvector_expr.h>
#include <util/bitvector_types.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/fresh_symbol.h>
#include <util/pointer_expr.h>
#include <util/pointer_offset_size.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

#include "asm_semantics.h"

#include <algorithm>
#include <set>

asm_lowering_contextt::asm_lowering_contextt(
  symbol_table_baset &_symbol_table,
  const irep_idt &_function_id,
  const source_locationt &_source_location,
  asm_operandst &_operands,
  const asm_semanticst &_semantics)
  : ns(_symbol_table),
    operands(_operands),
    semantics(_semantics),
    goto_target(nil_exprt{}),
    symbol_table(_symbol_table),
    function_id(_function_id),
    statement_location(_source_location),
    location(_source_location)
{
  // The generated code models the hardware, where arithmetic wraps around
  // and shifts are defined for all distances: the checks for undefined
  // behaviour of C do not apply. Checks of memory accesses still do.
  for(const char *check :
      {"signed-overflow-check",
       "unsigned-overflow-check",
       "pointer-overflow-check",
       "conversion-check",
       "undefined-shift-check",
       "float-overflow-check",
       "nan-check"})
  {
    location.add_pragma(std::string{"disable:"} + check);
  }

  const symbolt *function_symbol = symbol_table.lookup(function_id);
  mode = function_symbol == nullptr || function_symbol->mode.empty()
           ? ID_C
           : function_symbol->mode;
}

symbol_exprt
asm_lowering_contextt::temporary(const typet &type, const std::string &suffix)
{
  const symbolt &symbol = get_fresh_aux_symbol(
    type,
    id2string(function_id),
    "asm_" + suffix,
    location,
    mode,
    symbol_table);
  declared.push_back(symbol.symbol_expr());
  return symbol.symbol_expr();
}

symbol_exprt
asm_lowering_contextt::hardware_register(const std::string &canonical)
{
  auto it = registers.find(canonical);
  if(it != registers.end())
    return it->second;

  const symbol_exprt reg =
    temporary(unsignedbv_typet{semantics.register_width()}, canonical);
  registers.emplace(canonical, reg);
  return reg;
}

symbol_exprt asm_lowering_contextt::flag(const std::string &name)
{
  auto it = flags.find(name);
  if(it != flags.end())
    return it->second;

  const symbol_exprt f = temporary(bool_typet{}, "flag_" + name);
  flags.emplace(name, f);
  return f;
}

const symbol_exprt &
asm_lowering_contextt::operand_storage(std::size_t index) const
{
  return storage.at(index);
}

const symbol_exprt &
asm_lowering_contextt::operand_address(std::size_t index) const
{
  return addresses.at(index);
}

const exprt &asm_lowering_contextt::operand_immediate(std::size_t index) const
{
  return immediates.at(index);
}

std::size_t asm_lowering_contextt::operand_width(std::size_t index) const
{
  return width(operands.operands.at(index).expr.type());
}

void asm_lowering_contextt::assign(const exprt &lhs, const exprt &rhs)
{
  for(const auto &entry : registers)
  {
    if(lhs == entry.second)
      written_registers.insert(entry.first);
  }
  body.add(goto_programt::make_assignment(lhs, rhs, location));
}

void asm_lowering_contextt::begin_instruction()
{
  atomic = false;
  if(body.instructions.empty())
    instruction_start.reset();
  else
    instruction_start = std::prev(body.instructions.end());
}

void asm_lowering_contextt::end_instruction()
{
  if(!atomic)
    return;
  atomic = false;

  const goto_programt::targett first = instruction_start.has_value()
                                         ? std::next(*instruction_start)
                                         : body.instructions.begin();
  body.insert_before(first, goto_programt::make_atomic_begin(location));
  body.add(goto_programt::make_atomic_end(location));
}

void asm_lowering_contextt::assume(const exprt &condition)
{
  body.add(goto_programt::make_assumption(condition, location));
}

void asm_lowering_contextt::add(goto_programt::instructiont instruction)
{
  body.add(std::move(instruction));
}

void asm_lowering_contextt::fence(
  bool ww,
  bool rr,
  bool rw,
  bool wr,
  bool cumulative)
{
  codet code_fence(ID_fence);
  code_fence.add_source_location() = location;
  if(ww)
    code_fence.set(ID_WWfence, true);
  if(rr)
    code_fence.set(ID_RRfence, true);
  if(rw)
    code_fence.set(ID_RWfence, true);
  if(wr)
    code_fence.set(ID_WRfence, true);
  if(cumulative)
  {
    if(ww)
      code_fence.set(ID_WWcumul, true);
    if(rr)
      code_fence.set(ID_RRcumul, true);
    if(rw)
      code_fence.set(ID_RWcumul, true);
    if(wr)
      code_fence.set(ID_WRcumul, true);
  }
  body.add(goto_programt::make_other(code_fence, location));
}

void asm_lowering_contextt::call(
  const irep_idt &function,
  const exprt::operandst &arguments)
{
  const typet void_pointer = pointer_type(empty_typet{});

  exprt::operandst args;
  for(const auto &arg : arguments)
    args.push_back(typecast_exprt::conditional_cast(arg, void_pointer));

  code_typet type{
    code_typet::parameterst{args.size(), code_typet::parametert{void_pointer}},
    empty_typet{}};

  if(!symbol_table.has_symbol(function))
  {
    symbolt symbol{function, type, ID_C};
    symbol.base_name = function;
    symbol_table.add(symbol);
  }

  called_functions.push_back(function);

  body.add(goto_programt::make_function_call(
    code_function_callt{
      symbol_exprt{function, type}.with_source_location(location),
      std::move(args)},
    location));
}

exprt asm_lowering_contextt::nondet(const typet &type) const
{
  return side_effect_expr_nondett{type, location};
}

exprt asm_lowering_contextt::memory(const exprt &address, std::size_t w) const
{
  const pointer_typet target = pointer_type(unsignedbv_typet{w});
  exprt pointer = address;
  if(address.type().id() != ID_pointer)
  {
    // an address held in a register
    pointer = typecast_exprt{
      typecast_exprt::conditional_cast(
        address, unsignedbv_typet{config.ansi_c.pointer_width}),
      target};
  }
  else
    pointer = typecast_exprt::conditional_cast(address, target);

  return dereference_exprt{pointer};
}

std::size_t asm_lowering_contextt::width(const typet &type) const
{
  const typet &t =
    type.id() == ID_c_enum_tag ? ns.follow_tag(to_c_enum_tag_type(type)) : type;

  if(t.id() == ID_pointer)
    return config.ansi_c.pointer_width;

  if(t.id() == ID_bool)
    return 1;

  if(
    t.id() == ID_unsignedbv || t.id() == ID_signedbv || t.id() == ID_c_bool ||
    t.id() == ID_bv || t.id() == ID_c_bit_field || t.id() == ID_c_enum)
  {
    const auto bits = pointer_offset_bits(t, ns);
    if(bits.has_value())
      return numeric_cast_v<std::size_t>(*bits);
  }

  return 0;
}

exprt asm_lowering_contextt::to_bits(const exprt &value, std::size_t w) const
{
  const std::size_t own = width(value.type());
  if(own == 0)
    return nil_exprt{};

  exprt bits;
  if(value.type().id() == ID_bool)
  {
    bits = if_exprt{
      value,
      from_integer(1, unsignedbv_typet{1}),
      from_integer(0, unsignedbv_typet{1})};
  }
  else
    bits = typecast_exprt::conditional_cast(value, unsignedbv_typet{own});

  return typecast_exprt::conditional_cast(bits, unsignedbv_typet{w});
}

exprt asm_lowering_contextt::from_bits(const exprt &bits, const typet &type)
  const
{
  const std::size_t own = width(type);
  PRECONDITION(own != 0);

  const exprt resized =
    typecast_exprt::conditional_cast(bits, unsignedbv_typet{own});

  if(type.id() == ID_bool)
    return notequal_exprt{resized, from_integer(0, resized.type())};

  return typecast_exprt::conditional_cast(resized, type);
}

bool asm_lowering_contextt::prepare(
  const std::vector<asm_instructiont> &instructions)
{
  const std::size_t register_width = semantics.register_width();

  // Which input operands are read above their natural width by some
  // reference: those must keep non-deterministic upper bits (see below).
  std::set<std::size_t> widened;
  for(const auto &instruction : instructions)
  {
    for(const auto &tokens : instruction.operands)
    {
      for(const auto &token : tokens)
      {
        if(
          token.kind == asm_tokent::kindt::OPERAND &&
          token.index < operands.operands.size())
        {
          const std::size_t w =
            width(operands.operands[token.index].expr.type());
          if(w != 0 && semantics.reference_widens(token.modifier, w))
            widened.insert(token.index);
        }
      }
    }
  }

  if(goto_target.is_not_nil())
  {
    prologue.add(goto_programt::make_assignment(
      goto_target, from_integer(0, goto_target.type()), location));
  }

  for(std::size_t i = 0; i < operands.operands.size(); ++i)
  {
    const asm_operandt &operand = operands.operands[i];

    switch(operand.kind)
    {
    case asm_operandt::kindt::REGISTER:
    {
      const std::size_t w = width(operand.expr.type());
      if(w == 0 || w > register_width)
      {
        return fail(
          "operand " + std::to_string(i) +
          " does not fit into a general-purpose register");
      }

      symbol_exprt s =
        operand.tied_output.has_value() ? storage.at(*operand.tied_output)
        : !operand.fixed_register.empty()
          ? hardware_register(operand.fixed_register)
          : temporary(
              unsignedbv_typet{register_width}, "op" + std::to_string(i));
      storage.emplace(i, s);

      if(operand.is_read)
      {
        // evaluate the C expression, with the checks that apply to it
        code_expressiont evaluate{operand.expr};
        evaluate.add_source_location() = statement_location;
        prologue.add(goto_programt::make_other(evaluate, statement_location));

        // The value, zero-extended to the register width.
        const exprt value = to_bits(operand.expr, register_width);

        if(w < register_width && widened.count(i) != 0)
        {
          // Some reference reads this operand above its natural width, where
          // the bits are unspecified. Model them non-deterministically by
          // keeping the (uninitialised) upper bits of the register.
          const mp_integer mask = power(2, w) - 1;
          prologue.add(goto_programt::make_assignment(
            s,
            bitor_exprt{
              bitand_exprt{
                s, from_integer(power(2, register_width) - 1 - mask, s.type())},
              value},
            location));
        }
        else
        {
          // No reference reads above the operand's width, so zero-extension is
          // exact. Unlike the merge above, the register is then a plain
          // function of the input, so when the input is a constant the
          // register stays a constant and symex constant propagation keeps
          // working. (The merge would make, for example, a spinlock word
          // written through the operand symbolic, forcing symex to unwind the
          // lock's spin loops to the unwinding bound.)
          prologue.add(goto_programt::make_assignment(s, value, location));
        }
      }
      break;
    }

    case asm_operandt::kindt::MEMORY:
    {
      const symbol_exprt a = temporary(
        pointer_type(operand.expr.type()), "addr" + std::to_string(i));
      addresses.emplace(i, a);
      prologue.add(goto_programt::make_assignment(
        a, address_of_exprt{operand.expr}, location));
      break;
    }

    case asm_operandt::kindt::IMMEDIATE:
      if(width(operand.expr.type()) == 0)
        return fail("immediate operand " + std::to_string(i) + " not scalar");
      immediates.emplace(i, operand.expr);
      break;

    case asm_operandt::kindt::FLAG_OUTPUT:
      break;
    }
  }

  return true;
}

void asm_lowering_contextt::define_label(const std::string &name)
{
  const auto t = body.add(goto_programt::make_skip(location));
  if(
    !name.empty() &&
    std::all_of(
      name.begin(), name.end(), [](char c) { return c >= '0' && c <= '9'; }))
  {
    numeric_labels[name].push_back(t);
  }
  else
    label_definitions[name] = t;
}

bool asm_lowering_contextt::branch(
  const asm_tokent &target,
  const exprt &condition)
{
  if(target.kind == asm_tokent::kindt::C_LABEL)
  {
    if(goto_target.is_nil())
      return fail("branch to a C label without asm goto");

    assign(
      goto_target,
      if_exprt{
        condition,
        from_integer(target.index + 1, goto_target.type()),
        goto_target});
    exit_branches.push_back(
      body.add(goto_programt::make_incomplete_goto(condition, location)));
    return true;
  }

  if(target.kind == asm_tokent::kindt::LOCAL_LABEL)
  {
    const auto &definitions = numeric_labels[target.text];
    if(target.backward)
    {
      if(definitions.empty())
        return fail("undefined label " + target.text + "b");
      body.add(
        goto_programt::make_goto(definitions.back(), condition, location));
      return true;
    }

    pending.push_back(
      {body.add(goto_programt::make_incomplete_goto(condition, location)),
       target.text,
       definitions.size(),
       true,
       true});
    return true;
  }

  if(target.kind == asm_tokent::kindt::IDENTIFIER)
  {
    pending.push_back(
      {body.add(goto_programt::make_incomplete_goto(condition, location)),
       target.text,
       0,
       true,
       false});
    return true;
  }

  return fail("unsupported branch target");
}

goto_programt::targett
asm_lowering_contextt::begin_conditional(const exprt &condition)
{
  return body.add(
    goto_programt::make_incomplete_goto(not_exprt{condition}, location));
}

void asm_lowering_contextt::end_conditional(goto_programt::targett begin)
{
  begin->complete_goto(body.add(goto_programt::make_skip(location)));
}

bool asm_lowering_contextt::finish(goto_programt &dest)
{
  exit_label = body.add(goto_programt::make_skip(location));

  for(auto &branch : pending)
  {
    goto_programt::targett target;
    if(branch.numeric)
    {
      const auto &definitions = numeric_labels[branch.label];
      if(branch.definitions_before >= definitions.size())
        return fail("undefined label " + branch.label + "f");
      target = definitions[branch.definitions_before];
    }
    else
    {
      auto it = label_definitions.find(branch.label);
      if(it == label_definitions.end())
        return fail("undefined label " + branch.label);
      target = it->second;
    }
    branch.instruction->complete_goto(target);
  }

  for(auto &branch : exit_branches)
    branch->complete_goto(exit_label);

  // GCC binds a register variable (`register long x asm("rax")`) used as a
  // register operand to its register. The operand storage does not model
  // that, so a write to a named register that is neither an operand nor
  // clobbered may be a write to such a variable, and is not modeled.
  std::set<std::string> bound;
  for(const auto &operand : operands.operands)
  {
    if(!operand.fixed_register.empty())
      bound.insert(operand.fixed_register);
  }
  for(const auto &clobber : operands.clobbers)
  {
    const std::string canonical = semantics.canonical_register(clobber);
    if(!canonical.empty())
      bound.insert(canonical);
  }
  for(const auto &reg : written_registers)
  {
    if(bound.count(reg) == 0)
    {
      return fail(
        "writes register " + reg +
        ", which is neither an operand nor clobbered (and may hold a register "
        "variable)");
    }
  }

  for(std::size_t i = 0; i < operands.operands.size(); ++i)
  {
    const asm_operandt &operand = operands.operands[i];
    if(!operand.is_output)
      continue;

    if(operand.kind == asm_operandt::kindt::REGISTER)
    {
      epilogue.add(goto_programt::make_assignment(
        operand.expr, from_bits(storage.at(i), operand.expr.type()), location));
    }
    else if(operand.kind == asm_operandt::kindt::FLAG_OUTPUT)
    {
      const exprt value = semantics.condition(operand.flag_condition, *this);
      if(value.is_nil())
        return fail("unsupported flag output " + operand.flag_condition);
      epilogue.add(goto_programt::make_assignment(
        operand.expr,
        typecast_exprt::conditional_cast(value, operand.expr.type()),
        location));
    }
  }

  for(const auto &symbol : declared)
    dest.add(goto_programt::make_decl(symbol, location));

  dest.destructive_append(prologue);
  dest.destructive_append(body);
  dest.destructive_append(epilogue);

  for(const auto &symbol : declared)
    dest.add(goto_programt::make_dead(symbol, location));

  return true;
}
