/*******************************************************************\

Module: Remove 'asm' statements by compiling them into suitable
        standard goto program instructions

Author: Daniel Kroening

Date:   December 2014

\*******************************************************************/

/// \file
/// Remove 'asm' statements by compiling them into suitable standard goto
/// program instructions

#include "remove_asm.h"

#include <util/c_types.h>
#include <util/message.h>
#include <util/pointer_expr.h>
#include <util/prefix.h>
#include <util/range.h>
#include <util/std_code.h>
#include <util/string_constant.h>
#include <util/suffix.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include "assembler_parser.h"

#include <cctype>
#include <functional>
#include <optional>

class remove_asmt
{
public:
  remove_asmt(
    symbol_tablet &_symbol_table,
    goto_functionst &_goto_functions,
    message_handlert &message_handler)
    : symbol_table(_symbol_table),
      goto_functions(_goto_functions),
      message_handler(message_handler),
      log(message_handler)
  {
  }

  void operator()()
  {
    for(auto &f : goto_functions.function_map)
      process_function(f.first, f.second);
  }

protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;
  message_handlert &message_handler;
  messaget log;

  using instructionst = std::list<assembler_parsert::instructiont>;

  using handle_commandt = std::function<bool(
    const irep_idt &command,
    std::size_t pos,
    const assembler_parsert::instructiont &instruction,
    goto_programt &tmp_dest)>;

  void process_function(const irep_idt &, goto_functionst::goto_functiont &);

  void process_instruction(
    const irep_idt &function_id,
    goto_programt::instructiont &instruction,
    goto_programt &dest);

  void process_instruction_gcc(const code_asm_gcct &, goto_programt &dest);

  void process_instruction_msc(
    const irep_idt &function_id,
    const code_asmt &,
    goto_programt &dest);

  instructionst parse(const irep_idt &assembly);

  std::optional<irep_idt> process_asm(
    const code_asmt &code,
    const instructionst &instructions,
    goto_programt &dest,
    const handle_commandt &handle_command);

  void warn_dropped(const code_asmt &code);

  bool handle_gcc_command(
    const irep_idt &command,
    std::size_t pos,
    const assembler_parsert::instructiont &instruction,
    const code_asm_gcct &code,
    goto_programt &tmp_dest);

  bool handle_msc_command(
    const irep_idt &command,
    std::size_t pos,
    const assembler_parsert::instructiont &instruction,
    const irep_idt &function_id,
    const code_asmt &code,
    goto_programt &tmp_dest);

  void asm_function_call(
    const irep_idt &function_base_name,
    const exprt::operandst &operands,
    const source_locationt &source_location,
    goto_programt &dest);
};

/// Adds a call to a library function that implements an inline assembly
/// instruction. The function is declared if it does not exist yet; the
/// library provides its body.
///
/// \param function_base_name: Name of the function to call
/// \param operands: Arguments to be passed to the function, each of which is
///   converted to `void *`
/// \param source_location: Location of the inline assembly statement
/// \param dest: Goto program to append the function call to
void remove_asmt::asm_function_call(
  const irep_idt &function_base_name,
  const exprt::operandst &operands,
  const source_locationt &source_location,
  goto_programt &dest)
{
  const irep_idt &function_identifier = function_base_name;

  code_function_callt::argumentst arguments;

  const typet void_pointer = pointer_type(empty_typet{});

  for(const auto &op : operands)
    arguments.push_back(typecast_exprt::conditional_cast(op, void_pointer));

  code_typet fkt_type{
    code_typet::parameterst{
      arguments.size(), code_typet::parametert{void_pointer}},
    empty_typet{}};

  auto fkt = symbol_exprt{function_identifier, fkt_type}.with_source_location(
    source_location);

  dest.add(goto_programt::make_function_call(
    code_function_callt{std::move(fkt), std::move(arguments)},
    source_location));

  // do we have it?
  if(!symbol_table.has_symbol(function_identifier))
  {
    symbolt symbol{function_identifier, fkt_type, ID_C};
    symbol.base_name = function_base_name;

    symbol_table.add(symbol);

    goto_functions.function_map.emplace(function_identifier, goto_functiont());
  }
  else
  {
    DATA_INVARIANT_WITH_DIAGNOSTICS(
      symbol_table.lookup_ref(function_identifier).type == fkt_type,
      "types of function " + id2string(function_identifier) + " should match",
      symbol_table.lookup_ref(function_identifier).type.pretty(),
      fkt_type.pretty());
  }
}

/// Translates the given inline assembly code (which must be in either gcc or
/// msc style) to non-assembly goto program instructions
///
/// \param function_id: Name of function being processed
/// \param instruction: The goto program instruction containing the inline
///   assembly statements
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction(
  const irep_idt &function_id,
  goto_programt::instructiont &instruction,
  goto_programt &dest)
{
  const code_asmt &code = to_code_asm(instruction.get_other());

  const irep_idt &flavor = code.get_flavor();

  if(flavor == ID_gcc)
    process_instruction_gcc(to_code_asm_gcc(code), dest);
  else if(flavor == ID_msc)
    process_instruction_msc(function_id, code, dest);
  else
    DATA_INVARIANT(false, "unexpected assembler flavor");
}

/// Builds a `fence` codet with the requested orderings.
/// \param source_location: Location of the fence
/// \param ww: Whether writes are ordered before later writes
/// \param rr: Whether reads are ordered before later reads
/// \param rw: Whether reads are ordered before later writes
/// \param wr: Whether writes are ordered before later reads
/// \param cumulative: Whether each of the requested orderings is cumulative,
///   i.e., also applies to the accesses of other threads that were observed
///   before the fence
static codet make_fence(
  const source_locationt &source_location,
  bool ww,
  bool rr,
  bool rw,
  bool wr,
  bool cumulative)
{
  codet code_fence{ID_fence};
  code_fence.add_source_location() = source_location;
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
    if(rw)
      code_fence.set(ID_RWcumul, true);
    if(rr)
      code_fence.set(ID_RRcumul, true);
    if(wr)
      code_fence.set(ID_WRcumul, true);
  }
  return code_fence;
}

/// Parses the text of an inline assembly statement.
/// \param assembly: The assembly text
/// \return The instructions, each a sequence of tokens
remove_asmt::instructionst remove_asmt::parse(const irep_idt &assembly)
{
  std::istringstream str(id2string(assembly));
  assembler_parsert assembler_parser{message_handler};
  assembler_parser.in = &str;
  assembler_parser.parse();
  return std::move(assembler_parser.instructions);
}

/// Shared scaffolding for translating gcc-style and msc-style inline assembly.
/// For each instruction in \p instructions, handles the `lock` prefix and
/// `xchg` (which start an atomic section containing a full fence), delegates
/// the actual command translation to \p handle_command, and closes the atomic
/// section. The translation is appended to \p dest only if all instructions
/// are recognized by \p handle_command.
///
/// \param code: The inline assembly code statement being translated
/// \param instructions: The parsed assembly text
/// \param dest: The goto program to append the new instructions to
/// \param handle_command: Translates a single command into \p tmp_dest and
///   returns whether the command was recognized
/// \return The first command that is not recognized, if any; nothing is
///   appended to \p dest in this case.
std::optional<irep_idt> remove_asmt::process_asm(
  const code_asmt &code,
  const instructionst &instructions,
  goto_programt &dest,
  const handle_commandt &handle_command)
{
  goto_programt tmp_dest;
  bool x86_32_locked_atomic = false;

  for(const auto &instruction : instructions)
  {
    if(instruction.empty())
      continue;

    // deal with prefixes
    irep_idt command;
    std::size_t pos = 0;

    if(
      instruction.front().id() == ID_symbol &&
      instruction.front().get(ID_identifier) == "lock")
    {
      x86_32_locked_atomic = true;
      pos++;
    }

    // done?
    if(pos == instruction.size())
      continue;

    if(instruction[pos].id() == ID_symbol)
    {
      command = instruction[pos].get(ID_identifier);
      pos++;
    }

    if(command == "xchg" || command == "xchgl")
      x86_32_locked_atomic = true;

    if(x86_32_locked_atomic)
    {
      tmp_dest.add(goto_programt::make_atomic_begin(code.source_location()));
      tmp_dest.add(goto_programt::make_other(
        make_fence(code.source_location(), true, true, true, true, false),
        code.source_location()));
    }

    if(!handle_command(command, pos, instruction, tmp_dest))
      return command;

    if(x86_32_locked_atomic)
    {
      tmp_dest.add(goto_programt::make_atomic_end(code.source_location()));

      x86_32_locked_atomic = false;
    }
  }

  dest.destructive_append(tmp_dest);
  return {};
}

/// Warns that the inline assembly statement \p code is dropped.
/// \param code: The inline assembly code statement
void remove_asmt::warn_dropped(const code_asmt &code)
{
  // The entire inline-assembly statement is dropped when any of its
  // instructions is not recognized; warn so that the user is not left
  // silently relying on un-modeled assembly.
  log.warning() << "dropping inline assembly statement at "
                << code.source_location()
                << ": it contains an instruction that is not modeled, so the "
                   "whole statement (including any modeled instructions) is "
                   "removed"
                << messaget::eom;
}

/// Translates the given inline assembly code (in gcc style) to non-assembly
/// goto program instructions, dropping it if it contains an instruction
/// that is not modeled.
///
/// \param code: The inline assembly code statement to translate
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction_gcc(
  const code_asm_gcct &code,
  goto_programt &dest)
{
  const instructionst instructions =
    parse(to_string_constant(code.asm_text()).value());

  const auto unknown = process_asm(
    code,
    instructions,
    dest,
    [this, &code](
      const irep_idt &command,
      std::size_t pos,
      const assembler_parsert::instructiont &instruction,
      goto_programt &tmp_dest)
    { return handle_gcc_command(command, pos, instruction, code, tmp_dest); });

  if(unknown.has_value())
    warn_dropped(code);
}

/// \return The operand of \p code referred to as `%N` by the tokens of
///   \p instruction starting at \p pos, if these are the only remaining
///   tokens. Operands are numbered as in gcc: outputs first, then inputs.
static std::optional<exprt> gcc_operand(
  const code_asm_gcct &code,
  std::size_t pos,
  const assembler_parsert::instructiont &instruction)
{
  if(pos + 1 >= instruction.size() || instruction[pos].id() != "%")
    return {};

  std::size_t index = 0;
  for(++pos; pos < instruction.size(); ++pos)
  {
    const std::string &digit = id2string(instruction[pos].id());
    if(digit.size() != 1 || !isdigit(digit[0]))
      return {};
    index = index * 10 + static_cast<std::size_t>(digit[0] - '0');
  }

  for(const auto *list : {&code.outputs(), &code.inputs()})
  {
    for(const auto &operand : list->operands())
    {
      if(operand.operands().size() != 2)
        return {};
      if(index == 0)
        return to_binary_expr(operand).op1();
      --index;
    }
  }

  return {};
}

/// Translates a single recognized gcc-style command into \p tmp_dest.
///
/// \param command: The instruction mnemonic to translate
/// \param pos: Index of the token following the command in \p instruction
/// \param instruction: The parsed instruction tokens
/// \param code: The inline assembly code statement being translated
/// \param tmp_dest: The goto program to append the translation to
/// \return Whether the command was recognized (and hence modeled)
bool remove_asmt::handle_gcc_command(
  const irep_idt &command,
  std::size_t pos,
  const assembler_parsert::instructiont &instruction,
  const code_asm_gcct &code,
  goto_programt &tmp_dest)
{
  const source_locationt &source_location = code.source_location();
  const bool no_operands = pos == instruction.size();

  auto fence = [&](bool ww, bool rr, bool rw, bool wr, bool cumulative)
  {
    tmp_dest.add(goto_programt::make_other(
      make_fence(source_location, ww, rr, rw, wr, cumulative),
      source_location));
    return true;
  };

  if(command == "fstcw" || command == "fnstcw" || command == "fldcw") // x86
  {
    const auto operand = gcc_operand(code, pos, instruction);
    if(!operand.has_value())
      return false;
    asm_function_call(
      "__asm_" + id2string(command),
      {address_of_exprt{*operand}},
      source_location,
      tmp_dest);
    return true;
  }

  if(command == "dmb" || command == "dsb") // ARM
  {
    if(no_operands)
      return fence(true, true, true, true, true);

    // the barrier option selects the accesses being ordered
    if(pos + 1 != instruction.size() || instruction[pos].id() != ID_symbol)
      return false;
    const std::string &option = id2string(instruction[pos].get(ID_identifier));
    if(option == "sy" || option == "ish" || option == "osh" || option == "nsh")
      return fence(true, true, true, true, true);
    else if(has_suffix(option, "ld")) // loads before loads and stores
      return fence(false, true, true, false, true);
    else if(has_suffix(option, "st")) // stores before stores
      return fence(true, false, false, false, true);
    else
      return false;
  }

  if(command == "isb") // ARM
  {
    if(
      !no_operands &&
      (pos + 1 != instruction.size() || instruction[pos].id() != ID_symbol ||
       instruction[pos].get(ID_identifier) != "sy"))
    {
      return false;
    }
    // doesn't do anything by itself, needs to be combined with branch
    return fence(false, false, false, false, false);
  }

  // all other modeled instructions have no operands
  if(!no_operands)
    return false;

  if(command == "mfence" || command == "lfence" || command == "sfence") // x86
  {
    asm_function_call(
      "__asm_" + id2string(command), {}, source_location, tmp_dest);
    return true;
  }
  else if(command == "nop" || command == "pause" || command == "yield")
  {
    // no effect on the C program state
    return true;
  }
  else if(command == ID_sync || command == "hwsync") // Power
    return fence(true, true, true, true, true);
  else if(command == ID_lwsync) // Power: everything but store-load
    return fence(true, true, true, false, true);
  else if(command == "eieio") // Power: orders stores
    return fence(true, false, false, false, true);
  else if(command == ID_isync) // Power
  {
    // doesn't do anything by itself, needs to be combined with branch
    return fence(false, false, false, false, false);
  }
  else
    return false;
}

/// Translates the given inline assembly code (in msc style) to non-assembly
/// goto program instructions, dropping it if it contains an instruction
/// that is not modeled.
///
/// \param function_id: Name of function being processed
/// \param code: The inline assembly code statement to translate
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction_msc(
  const irep_idt &function_id,
  const code_asmt &code,
  goto_programt &dest)
{
  const instructionst instructions =
    parse(to_string_constant(code.op0()).value());

  const auto unknown = process_asm(
    code,
    instructions,
    dest,
    [this, &code, &function_id](
      const irep_idt &command,
      std::size_t pos,
      const assembler_parsert::instructiont &instruction,
      goto_programt &tmp_dest)
    {
      return handle_msc_command(
        command, pos, instruction, function_id, code, tmp_dest);
    });

  if(unknown.has_value())
    warn_dropped(code);
}

/// Translates a single recognized msc-style command into \p tmp_dest.
///
/// \param command: The instruction mnemonic to translate
/// \param pos: Index of the token following the command in \p instruction
/// \param instruction: The parsed instruction tokens
/// \param function_id: Name of function being processed
/// \param code: The inline assembly code statement being translated
/// \param tmp_dest: The goto program to append the translation to
/// \return Whether the command was recognized (and hence modeled)
bool remove_asmt::handle_msc_command(
  const irep_idt &command,
  std::size_t pos,
  const assembler_parsert::instructiont &instruction,
  const irep_idt &function_id,
  const code_asmt &code,
  goto_programt &tmp_dest)
{
  const bool no_operands = pos == instruction.size();

  if(command == "fstcw" || command == "fnstcw" || command == "fldcw") // x86
  {
    if(pos + 1 != instruction.size() || instruction[pos].id() != ID_symbol)
      return false;

    // a local variable (or parameter) takes precedence over a global one;
    // if several local variables of that name exist (shadowing), it is not
    // known which one is meant
    const irep_idt &name = instruction[pos].get(ID_identifier);
    const std::string local_prefix = id2string(function_id) + "::";
    std::optional<irep_idt> global, local;
    for(const auto &entry : equal_range(symbol_table.symbol_base_map, name))
    {
      if(entry.second == name)
        global = entry.second;
      else if(has_prefix(id2string(entry.second), local_prefix))
      {
        if(local.has_value())
          return false;
        local = entry.second;
      }
    }

    if(!local.has_value() && !global.has_value())
      return false;

    const exprt arg = address_of_exprt{
      symbol_table.lookup_ref(local.has_value() ? *local : *global)
        .symbol_expr()};

    asm_function_call(
      "__asm_" + id2string(command), {arg}, code.source_location(), tmp_dest);
  }
  else if(
    no_operands &&
    (command == "mfence" || command == "lfence" || command == "sfence")) // x86
  {
    asm_function_call(
      "__asm_" + id2string(command), {}, code.source_location(), tmp_dest);
  }
  else if(no_operands && (command == "nop" || command == "pause"))
  {
    // no effect on the C program state
  }
  else
    return false;

  return true;
}

/// Replaces inline assembly instructions in the goto function by non-assembly
/// goto program instructions
///
/// \param function_id: Name of function being processed
/// \param goto_function: The goto function
void remove_asmt::process_function(
  const irep_idt &function_id,
  goto_functionst::goto_functiont &goto_function)
{
  bool did_something = false;

  Forall_goto_program_instructions(it, goto_function.body)
  {
    if(it->is_other() && it->get_other().get_statement() == ID_asm)
    {
      goto_programt tmp_dest;
      process_instruction(function_id, *it, tmp_dest);
      it->turn_into_skip();
      did_something = true;

      goto_programt::targett next = it;
      next++;

      goto_function.body.destructive_insert(next, tmp_dest);
    }
  }

  if(did_something)
    remove_skip(goto_function.body);
}

/// \copybrief remove_asm(goto_modelt &, message_handlert &)
///
/// \param goto_functions: The goto functions
/// \param symbol_table: The symbol table
/// \param message_handler: Message handler
void remove_asm(
  goto_functionst &goto_functions,
  symbol_tablet &symbol_table,
  message_handlert &message_handler)
{
  remove_asmt rem(symbol_table, goto_functions, message_handler);
  rem();
}

/// Replaces inline assembly instructions in the goto program (i.e.,
/// instructions of kind `OTHER` with a `code` member of type `code_asmt`) with
/// an appropriate (sequence of) non-assembly goto program instruction(s).
/// At present only a small number of x86, ARM, and Power instructions are
/// supported. Statements that contain an unrecognised instruction are
/// removed.
///
/// \param goto_model: The goto model
/// \param message_handler: Message handler
void remove_asm(goto_modelt &goto_model, message_handlert &message_handler)
{
  remove_asm(
    goto_model.goto_functions, goto_model.symbol_table, message_handler);
}

bool has_asm(const goto_functionst &goto_functions)
{
  for(auto &function_it : goto_functions.function_map)
    for(auto &instruction : function_it.second.body.instructions)
      if(
        instruction.is_other() &&
        instruction.get_other().get_statement() == ID_asm)
      {
        return true;
      }

  return false;
}

bool has_asm(const goto_modelt &goto_model)
{
  return has_asm(goto_model.goto_functions);
}
