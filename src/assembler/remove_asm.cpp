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

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include "assembler_parser.h"

#include <functional>

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

  void process_function(const irep_idt &, goto_functionst::goto_functiont &);

  void process_instruction(
    const irep_idt &function_id,
    goto_programt::instructiont &instruction,
    goto_programt &dest);

  void process_instruction_gcc(const code_asm_gcct &, goto_programt &dest);

  void process_instruction_msc(
    const irep_idt &,
    const code_asmt &,
    goto_programt &dest);

  // Shared scaffolding for the gcc and msc flavors: parse the assembly text,
  // handle the lock prefix and xchg, wrap locked instructions in an atomic
  // section with a full fence, and either append the translation to \p dest or
  // drop the whole statement (emitting a warning) if \p handle_command reports
  // an unrecognized instruction.
  void process_asm(
    const code_asmt &code,
    const irep_idt &assembly,
    goto_programt &dest,
    const std::function<bool(
      const irep_idt &command,
      std::size_t pos,
      const assembler_parsert::instructiont &instruction,
      goto_programt &tmp_dest)> &handle_command);

  // Translates a single recognized gcc-style command, returning false if the
  // command is not modeled.
  bool handle_gcc_command(
    const irep_idt &command,
    const code_asm_gcct &code,
    goto_programt &tmp_dest);

  // Translates a single recognized msc-style command, returning false if the
  // command is not modeled.
  bool handle_msc_command(
    const irep_idt &command,
    std::size_t pos,
    const assembler_parsert::instructiont &instruction,
    const irep_idt &function_id,
    const code_asmt &code,
    goto_programt &tmp_dest);

  void gcc_asm_function_call(
    const irep_idt &function_base_name,
    const code_asm_gcct &code,
    std::size_t n_args,
    goto_programt &dest);

  void msc_asm_function_call(
    const irep_idt &function_base_name,
    const exprt::operandst &operands,
    const code_asmt &code,
    goto_programt &dest);
};

/// Adds a call to a library function that implements the given gcc-style inline
/// assembly statement
///
/// \param function_base_name: Name of the function to call
/// \param code: gcc-style inline assembly statement to translate to function
///   call
/// \param n_args: Number of arguments required by \p function_base_name
/// \param dest: Goto program to append the function call to
void remove_asmt::gcc_asm_function_call(
  const irep_idt &function_base_name,
  const code_asm_gcct &code,
  std::size_t n_args,
  goto_programt &dest)
{
  irep_idt function_identifier = function_base_name;

  code_function_callt::argumentst arguments;

  const typet void_pointer = pointer_type(empty_typet());

  // outputs
  forall_operands(it, code.outputs())
  {
    if(it->operands().size() == 2)
    {
      arguments.push_back(typecast_exprt(
        address_of_exprt(to_binary_expr(*it).op1()), void_pointer));
    }
  }

  // inputs
  forall_operands(it, code.inputs())
  {
    if(it->operands().size() == 2)
    {
      arguments.push_back(typecast_exprt(
        address_of_exprt(to_binary_expr(*it).op1()), void_pointer));
    }
  }

  // An inline asm statement may consist of multiple commands, not all of which
  // use all of the inputs/outputs of the inline asm statement.
  DATA_INVARIANT_WITH_DIAGNOSTICS(
    arguments.size() >= n_args,
    "insufficient number of arguments for calling " +
      id2string(function_identifier),
    "required arguments: " + std::to_string(n_args),
    code.pretty());
  arguments.resize(n_args);

  code_typet fkt_type{
    code_typet::parameterst{
      arguments.size(), code_typet::parametert{void_pointer}},
    empty_typet()};

  auto fkt = symbol_exprt{function_identifier, fkt_type}.with_source_location(
    code.source_location());

  code_function_callt function_call(std::move(fkt), std::move(arguments));

  dest.add(
    goto_programt::make_function_call(function_call, code.source_location()));

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
      code.pretty(),
      symbol_table.lookup_ref(function_identifier).type.pretty(),
      fkt_type.pretty());
  }
}

/// Adds a call to a library function that implements the given msc-style inline
/// assembly statement
///
/// \param function_base_name: Name of the function to call
/// \param operands: Arguments to be passed to function
/// \param code: msc-style inline assembly statement to translate to function
///   call
/// \param dest: Goto program to append the function call to
void remove_asmt::msc_asm_function_call(
  const irep_idt &function_base_name,
  const exprt::operandst &operands,
  const code_asmt &code,
  goto_programt &dest)
{
  irep_idt function_identifier = function_base_name;

  code_function_callt::argumentst arguments;

  const typet void_pointer = pointer_type(empty_typet());

  for(const auto &op : operands)
    arguments.push_back(typecast_exprt::conditional_cast(op, void_pointer));

  code_typet fkt_type{
    code_typet::parameterst{
      arguments.size(), code_typet::parametert{void_pointer}},
    empty_typet()};

  auto fkt = symbol_exprt{function_identifier, fkt_type}.with_source_location(
    code.source_location());
  code_function_callt function_call(std::move(fkt), std::move(arguments));

  dest.add(
    goto_programt::make_function_call(function_call, code.source_location()));

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
    DATA_INVARIANT(
      symbol_table.lookup_ref(function_identifier).type == fkt_type,
      "function types should match");
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

/// Builds a `fence` codet with the requested ordering and cumulativity flags.
/// Only the flags set to true are added, matching the ireps that the individual
/// fence instructions used to construct by hand.
static codet make_fence(
  const source_locationt &source_location,
  bool ww,
  bool rr,
  bool rw,
  bool wr,
  bool ww_cumul = false,
  bool rw_cumul = false,
  bool rr_cumul = false,
  bool wr_cumul = false)
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
  if(ww_cumul)
    code_fence.set(ID_WWcumul, true);
  if(rw_cumul)
    code_fence.set(ID_RWcumul, true);
  if(rr_cumul)
    code_fence.set(ID_RRcumul, true);
  if(wr_cumul)
    code_fence.set(ID_WRcumul, true);
  return code_fence;
}

/// Shared scaffolding for translating gcc-style and msc-style inline assembly.
/// Parses \p assembly, and for each parsed instruction handles the `lock`
/// prefix and `xchg` (which start an atomic section containing a full fence),
/// delegates the actual command translation to \p handle_command, and closes
/// the atomic section. If any instruction is not recognized by
/// \p handle_command, the whole statement is dropped (a warning is emitted and
/// nothing is appended to \p dest); otherwise the translation is appended.
///
/// \param code: The inline assembly code statement being translated
/// \param assembly: The assembly text to parse
/// \param dest: The goto program to append the new instructions to
/// \param handle_command: Translates a single command into \p tmp_dest and
///   returns whether the command was recognized
void remove_asmt::process_asm(
  const code_asmt &code,
  const irep_idt &assembly,
  goto_programt &dest,
  const std::function<bool(
    const irep_idt &command,
    std::size_t pos,
    const assembler_parsert::instructiont &instruction,
    goto_programt &tmp_dest)> &handle_command)
{
  std::istringstream str(id2string(assembly));
  assembler_parsert assembler_parser{message_handler};
  assembler_parser.in = &str;
  assembler_parser.parse();

  goto_programt tmp_dest;
  bool unknown = false;
  bool x86_32_locked_atomic = false;

  for(const auto &instruction : assembler_parser.instructions)
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
        make_fence(code.source_location(), true, true, true, true),
        code.source_location()));
    }

    if(!handle_command(command, pos, instruction, tmp_dest))
      unknown = true; // give up

    if(x86_32_locked_atomic)
    {
      tmp_dest.add(goto_programt::make_atomic_end(code.source_location()));

      x86_32_locked_atomic = false;
    }
  }

  if(unknown)
  {
    // The entire inline-assembly statement is dropped (turned into skip below)
    // when any of its instructions is not recognized; warn so that the user is
    // not left silently relying on un-modeled assembly.
    log.warning() << "dropping inline assembly statement at "
                  << code.source_location()
                  << ": it contains an instruction that is not modeled, so the "
                     "whole statement (including any modeled instructions) is "
                     "removed"
                  << messaget::eom;
  }
  else
    dest.destructive_append(tmp_dest);
}

/// Translates the given inline assembly code (in gcc style) to non-assembly
/// goto program instructions
///
/// \param code: The inline assembly code statement to translate
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction_gcc(
  const code_asm_gcct &code,
  goto_programt &dest)
{
  process_asm(
    code,
    to_string_constant(code.asm_text()).value(),
    dest,
    [this, &code](
      const irep_idt &command,
      std::size_t,
      const assembler_parsert::instructiont &,
      goto_programt &tmp_dest)
    { return handle_gcc_command(command, code, tmp_dest); });
}

/// Translates a single recognized gcc-style command into \p tmp_dest.
///
/// \param command: The instruction mnemonic to translate
/// \param code: The inline assembly code statement being translated
/// \param tmp_dest: The goto program to append the translation to
/// \return Whether the command was recognized (and hence modeled)
bool remove_asmt::handle_gcc_command(
  const irep_idt &command,
  const code_asm_gcct &code,
  goto_programt &tmp_dest)
{
  const source_locationt &source_location = code.source_location();

  if(command == "fstcw" || command == "fnstcw" || command == "fldcw") // x86
  {
    gcc_asm_function_call("__asm_" + id2string(command), code, 1, tmp_dest);
  }
  else if(
    command == "mfence" || command == "lfence" || command == "sfence") // x86
  {
    gcc_asm_function_call("__asm_" + id2string(command), code, 0, tmp_dest);
  }
  else if(command == ID_sync) // Power
  {
    tmp_dest.add(goto_programt::make_other(
      make_fence(
        source_location, true, true, true, true, true, true, true, true),
      source_location));
  }
  else if(command == ID_lwsync) // Power
  {
    tmp_dest.add(goto_programt::make_other(
      make_fence(
        source_location, true, true, true, false, true, true, true, false),
      source_location));
  }
  else if(command == ID_isync) // Power
  {
    // doesn't do anything by itself, needs to be combined with branch
    tmp_dest.add(goto_programt::make_other(
      make_fence(source_location, false, false, false, false),
      source_location));
  }
  else if(command == "dmb" || command == "dsb") // ARM
  {
    tmp_dest.add(goto_programt::make_other(
      make_fence(
        source_location, true, true, true, true, true, true, true, true),
      source_location));
  }
  else if(command == "isb") // ARM
  {
    // doesn't do anything by itself, needs to be combined with branch
    tmp_dest.add(goto_programt::make_other(
      make_fence(source_location, false, false, false, false),
      source_location));
  }
  else
    return false;

  return true;
}

/// Translates the given inline assembly code (in msc style) to non-assembly
/// goto program instructions
///
/// \param function_id: Name of function being processed
/// \param code: The inline assembly code statement to translate
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction_msc(
  const irep_idt &function_id,
  const code_asmt &code,
  goto_programt &dest)
{
  process_asm(
    code,
    to_string_constant(code.op0()).value(),
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
  if(command == "fstcw" || command == "fnstcw" || command == "fldcw") // x86
  {
    exprt::operandst args{null_pointer_exprt{pointer_type(empty_typet{})}};
    // try to typecheck the argument
    if(pos != instruction.size() && instruction[pos].id() == ID_symbol)
    {
      const irep_idt &name = instruction[pos].get(ID_identifier);
      for(const auto &entry : equal_range(symbol_table.symbol_base_map, name))
      {
        // global scope symbol, don't replace a local one
        if(entry.second == name && args[0].id() != ID_address_of)
        {
          args[0] =
            address_of_exprt{symbol_table.lookup_ref(name).symbol_expr()};
        }
        // parameter or symbol in local scope
        else if(has_prefix(
                  id2string(entry.second), id2string(function_id) + "::"))
        {
          args[0] = address_of_exprt{
            symbol_table.lookup_ref(entry.second).symbol_expr()};
        }
      }
    }
    msc_asm_function_call("__asm_" + id2string(command), args, code, tmp_dest);
  }
  else if(
    command == "mfence" || command == "lfence" || command == "sfence") // x86
  {
    msc_asm_function_call("__asm_" + id2string(command), {}, code, tmp_dest);
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
/// an appropriate (sequence of) non-assembly goto program instruction(s). At
/// present only a small number of x86 and Power instructions are supported.
/// Unrecognised assembly instructions are ignored.
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
