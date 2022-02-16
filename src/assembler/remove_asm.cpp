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
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/string_constant.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

#include "assembler_parser.h"

class remove_asmt
{
public:
  remove_asmt(symbol_tablet &_symbol_table, goto_functionst &_goto_functions)
    : symbol_table(_symbol_table), goto_functions(_goto_functions)
  {
  }

  void operator()()
  {
    for(auto &f : goto_functions.function_map)
      process_function(f.second);
  }

protected:
  symbol_tablet &symbol_table;
  goto_functionst &goto_functions;

  void process_function(goto_functionst::goto_functiont &);

  void process_instruction(
    goto_programt::instructiont &instruction,
    goto_programt &dest);

  void process_instruction_gcc(const code_asm_gcct &, goto_programt &dest);

  void process_instruction_msc(const code_asmt &, goto_programt &dest);

  void gcc_asm_function_call(
    const irep_idt &function_base_name,
    const code_asm_gcct &code,
    goto_programt &dest);

  void msc_asm_function_call(
    const irep_idt &function_base_name,
    const code_asmt &code,
    goto_programt &dest);
};

/// Adds a call to a library function that implements the given gcc-style inline
/// assembly statement
///
/// \param function_base_name: Name of the function to call
/// \param code: gcc-style inline assembly statement to translate to function
///   call
/// \param dest: Goto program to append the function call to
void remove_asmt::gcc_asm_function_call(
  const irep_idt &function_base_name,
  const code_asm_gcct &code,
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

  code_typet fkt_type({}, empty_typet());

  symbol_exprt fkt(function_identifier, fkt_type);

  code_function_callt function_call(std::move(fkt), std::move(arguments));

  dest.add(
    goto_programt::make_function_call(function_call, code.source_location()));

  // do we have it?
  if(!symbol_table.has_symbol(function_identifier))
  {
    symbolt symbol;

    symbol.name = function_identifier;
    symbol.type = fkt_type;
    symbol.base_name = function_base_name;
    symbol.value = nil_exprt();
    symbol.mode = ID_C;

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

/// Adds a call to a library function that implements the given msc-style inline
/// assembly statement
///
/// \param function_base_name: Name of the function to call
/// \param code: msc-style inline assembly statement to translate to function
///   call
/// \param dest: Goto program to append the function call to
void remove_asmt::msc_asm_function_call(
  const irep_idt &function_base_name,
  const code_asmt &code,
  goto_programt &dest)
{
  irep_idt function_identifier = function_base_name;

  const typet void_pointer = pointer_type(empty_typet());

  code_typet fkt_type({}, empty_typet());

  symbol_exprt fkt(function_identifier, fkt_type);

  code_function_callt function_call(fkt);

  dest.add(
    goto_programt::make_function_call(function_call, code.source_location()));

  // do we have it?
  if(!symbol_table.has_symbol(function_identifier))
  {
    symbolt symbol;

    symbol.name = function_identifier;
    symbol.type = fkt_type;
    symbol.base_name = function_base_name;
    symbol.value = nil_exprt();
    symbol.mode = ID_C;

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
/// \param instruction: The goto program instruction containing the inline
///   assembly statements
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction(
  goto_programt::instructiont &instruction,
  goto_programt &dest)
{
  const code_asmt &code = to_code_asm(instruction.get_other());

  const irep_idt &flavor = code.get_flavor();

  if(flavor == ID_gcc)
    process_instruction_gcc(to_code_asm_gcc(code), dest);
  else if(flavor == ID_msc)
    process_instruction_msc(code, dest);
  else
    DATA_INVARIANT(false, "unexpected assembler flavor");
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
  const irep_idt &i_str = to_string_constant(code.asm_text()).get_value();

  std::istringstream str(id2string(i_str));
  assembler_parser.clear();
  assembler_parser.in = &str;
  assembler_parser.parse();

  goto_programt tmp_dest;
  bool unknown = false;
  bool x86_32_locked_atomic = false;

  for(const auto &instruction : assembler_parser.instructions)
  {
    if(instruction.empty())
      continue;

#if 0
    std::cout << "A ********************\n";
    for(const auto &ins : instruction)
    {
      std::cout << "XX: " << ins.pretty() << '\n';
    }

    std::cout << "B ********************\n";
#endif

    // deal with prefixes
    irep_idt command;
    unsigned pos = 0;

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

      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();
      code_fence.set(ID_WWfence, true);
      code_fence.set(ID_RRfence, true);
      code_fence.set(ID_RWfence, true);
      code_fence.set(ID_WRfence, true);

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
    }

    if(command == "fstcw" || command == "fnstcw" || command == "fldcw") // x86
    {
      gcc_asm_function_call("__asm_" + id2string(command), code, tmp_dest);
    }
    else if(
      command == "mfence" || command == "lfence" || command == "sfence") // x86
    {
      gcc_asm_function_call("__asm_" + id2string(command), code, tmp_dest);
    }
    else if(command == ID_sync) // Power
    {
      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();
      code_fence.set(ID_WWfence, true);
      code_fence.set(ID_RRfence, true);
      code_fence.set(ID_RWfence, true);
      code_fence.set(ID_WRfence, true);
      code_fence.set(ID_WWcumul, true);
      code_fence.set(ID_RWcumul, true);
      code_fence.set(ID_RRcumul, true);
      code_fence.set(ID_WRcumul, true);

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
    }
    else if(command == ID_lwsync) // Power
    {
      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();
      code_fence.set(ID_WWfence, true);
      code_fence.set(ID_RRfence, true);
      code_fence.set(ID_RWfence, true);
      code_fence.set(ID_WWcumul, true);
      code_fence.set(ID_RWcumul, true);
      code_fence.set(ID_RRcumul, true);

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
    }
    else if(command == ID_isync) // Power
    {
      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
      // doesn't do anything by itself,
      // needs to be combined with branch
    }
    else if(command == "dmb" || command == "dsb") // ARM
    {
      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();
      code_fence.set(ID_WWfence, true);
      code_fence.set(ID_RRfence, true);
      code_fence.set(ID_RWfence, true);
      code_fence.set(ID_WRfence, true);
      code_fence.set(ID_WWcumul, true);
      code_fence.set(ID_RWcumul, true);
      code_fence.set(ID_RRcumul, true);
      code_fence.set(ID_WRcumul, true);

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
    }
    else if(command == "isb") // ARM
    {
      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
      // doesn't do anything by itself,
      // needs to be combined with branch
    }
    else
      unknown = true; // give up

    if(x86_32_locked_atomic)
    {
      tmp_dest.add(goto_programt::make_atomic_end(code.source_location()));

      x86_32_locked_atomic = false;
    }
  }

  if(unknown)
  {
    // we give up; we should perhaps print a warning
  }
  else
    dest.destructive_append(tmp_dest);
}

/// Translates the given inline assembly code (in msc style) to non-assembly
/// goto program instructions
///
/// \param code: The inline assembly code statement to translate
/// \param dest: The goto program to append the new instructions to
void remove_asmt::process_instruction_msc(
  const code_asmt &code,
  goto_programt &dest)
{
  const irep_idt &i_str = to_string_constant(code.op0()).get_value();

  std::istringstream str(id2string(i_str));
  assembler_parser.clear();
  assembler_parser.in = &str;
  assembler_parser.parse();

  goto_programt tmp_dest;
  bool unknown = false;
  bool x86_32_locked_atomic = false;

  for(const auto &instruction : assembler_parser.instructions)
  {
    if(instruction.empty())
      continue;

#if 0
    std::cout << "A ********************\n";
    for(const auto &ins : instruction)
    {
      std::cout << "XX: " << ins.pretty() << '\n';
    }

    std::cout << "B ********************\n";
#endif

    // deal with prefixes
    irep_idt command;
    unsigned pos = 0;

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

      codet code_fence(ID_fence);
      code_fence.add_source_location() = code.source_location();
      code_fence.set(ID_WWfence, true);
      code_fence.set(ID_RRfence, true);
      code_fence.set(ID_RWfence, true);
      code_fence.set(ID_WRfence, true);

      tmp_dest.add(
        goto_programt::make_other(code_fence, code.source_location()));
    }

    if(command == "fstcw" || command == "fnstcw" || command == "fldcw") // x86
    {
      msc_asm_function_call("__asm_" + id2string(command), code, tmp_dest);
    }
    else if(
      command == "mfence" || command == "lfence" || command == "sfence") // x86
    {
      msc_asm_function_call("__asm_" + id2string(command), code, tmp_dest);
    }
    else
      unknown = true; // give up

    if(x86_32_locked_atomic)
    {
      tmp_dest.add(goto_programt::make_atomic_end(code.source_location()));

      x86_32_locked_atomic = false;
    }
  }

  if(unknown)
  {
    // we give up; we should perhaps print a warning
  }
  else
    dest.destructive_append(tmp_dest);
}

/// Replaces inline assembly instructions in the goto function by non-assembly
/// goto program instructions
///
/// \param goto_function: The goto function
void remove_asmt::process_function(
  goto_functionst::goto_functiont &goto_function)
{
  bool did_something = false;

  Forall_goto_program_instructions(it, goto_function.body)
  {
    if(it->is_other() && it->get_other().get_statement() == ID_asm)
    {
      goto_programt tmp_dest;
      process_instruction(*it, tmp_dest);
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

/// \copybrief remove_asm(goto_modelt &)
///
/// \param goto_functions: The goto functions
/// \param symbol_table: The symbol table
void remove_asm(goto_functionst &goto_functions, symbol_tablet &symbol_table)
{
  remove_asmt rem(symbol_table, goto_functions);
  rem();
}

/// Replaces inline assembly instructions in the goto program (i.e.,
/// instructions of kind `OTHER` with a `code` member of type `code_asmt`) with
/// an appropriate (sequence of) non-assembly goto program instruction(s). At
/// present only a small number of x86 and Power instructions are supported.
/// Unrecognised assembly instructions are ignored.
///
/// \param goto_model: The goto model
void remove_asm(goto_modelt &goto_model)
{
  remove_asm(goto_model.goto_functions, goto_model.symbol_table);
}
