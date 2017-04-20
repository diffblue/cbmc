/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/cegis-util/string_helper.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/instructionset/processor_symbols.h>
#include <cegis/refactor/instructionset/execute_cegis_program.h>

void declare_cegis_program(symbol_tablet &st, goto_functionst &gf,
    const std::string &processor, const std::string &program_name)
{
  const typet size_type(signed_int_type());
  const constant_exprt sz_expr(from_integer(0, size_type));
  const code_typet &code_type=to_code_type(st.lookup(processor).type);
  const typet &type=code_type.parameters().front().type().subtype();
  const array_typet array_type(type, sz_expr);
  declare_global_meta_variable(st, program_name, array_type);
}

std::string declare_cegis_program(symbol_tablet &st, goto_functionst &gf,
    const std::string &processor)
{
  std::string prog_name(processor);
  prog_name+=CEGIS_REFACTOR_PROG_SUFFIX;
  declare_cegis_program(st, gf, processor, prog_name);
  return prog_name;
}

namespace
{
const exprt &get_size(const symbolt &prog)
{
  return to_array_type(prog.type).size();
}
}

void call_processor(const symbol_tablet &st, goto_programt::instructiont &instr,
    const std::string &processor, const std::string &program_name)
{
  instr.type=goto_program_instruction_typet::FUNCTION_CALL;
  code_function_callt call;
  call.function()=st.lookup(processor).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  const symbolt &prog_symbol=st.lookup(program_name);
  const symbol_exprt prog(prog_symbol.symbol_expr());
  const index_exprt first_instr(prog, from_integer(0, signed_int_type()));
  args.push_back(address_of_exprt(first_instr));
  const bv_arithmetict bv(get_size(prog_symbol));
  const mp_integer sz_val(bv.to_integer());
  args.push_back(from_integer(sz_val, cegis_size_type()));
  instr.code=call;
  instr.source_location=default_cegis_source_location();
}

goto_programt::targett call_processor(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos,
    const std::string &processor, const std::string &program_name)
{
  pos=body.insert_after(pos);
  call_processor(st, *pos, processor, program_name);
  return pos;
}

void set_cegis_processor_sizes(symbol_tablet &st, const size_t size)
{
  const constant_exprt sz_expr(from_integer(size, signed_int_type()));
  for(symbol_tablet::symbolst::value_type &entry : st.symbols)
  {
    typet &type=entry.second.type;
    if(ID_array != type.id()) continue;
    array_typet &array_type=to_array_type(type);
    const typet &elem_type=array_type.subtype();
    if(ID_symbol != elem_type.id()) continue;
    const symbol_typet &symbol_type=to_symbol_type(elem_type);
    const std::string &type_name=id2string(symbol_type.get_identifier());
    if(ends_with(type_name, INSTR_TYPE_SUFFIX)) array_type.size()=sz_expr;
  }
}

#define NUM_PROC_CALL_ARGS 2u

void set_cegis_processor_sizes(const symbol_tablet &st,
    goto_programt::targett first, const goto_programt::const_targett last,
    const size_t size)
{
  const constant_exprt sz_expr(from_integer(size, cegis_size_type()));
  for(; first != last; ++first)
  {
    if(goto_program_instruction_typet::FUNCTION_CALL != first->type) continue;
    code_function_callt &call=to_code_function_call(first->code);
    const exprt &func=call.function();
    if(ID_symbol != func.id()) continue;
    const irep_idt &func_name=to_symbol_expr(func).get_identifier();
    if(!st.has_symbol(func_name)) continue;
    const symbolt &symbol=st.lookup(func_name);
    const code_typet &code_type=to_code_type(symbol.type);
    const code_typet::parameterst &params=code_type.parameters();
    if(params.size() != NUM_PROC_CALL_ARGS) continue;
    const typet &param_ptr_type=params.front().type();
    if(ID_pointer != param_ptr_type.id()) continue;
    const typet &param_type=param_ptr_type.subtype();
    if(ID_symbol != param_type.id()) continue;
    const irep_idt &param_id=to_symbol_type(param_type).get_identifier();
    if(!ends_with(id2string(param_id), INSTR_TYPE_SUFFIX)) continue;
    assert(call.arguments().size() == NUM_PROC_CALL_ARGS);
    call.arguments().back()=sz_expr;
  }
}

void instrument_cegis_operand(const symbol_tablet &st,
    goto_programt::instructiont &instr, const size_t index,
    const irep_idt &var_name)
{
  const symbol_exprt var(st.lookup(var_name).symbol_expr());
  const std::string array_name(cegis_operand_array_name(st, var.type()));
  const symbol_exprt array(st.lookup(array_name).symbol_expr());
  const constant_exprt index_expr(from_integer(index, signed_int_type()));
  const index_exprt lhs(array, index_expr);
  const address_of_exprt rhs(var);
  instr.type=goto_program_instruction_typet::ASSIGN;
  instr.source_location=default_cegis_source_location();
  instr.code=code_assignt(lhs, rhs);
}

goto_programt::targett instrument_cegis_operand(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos, size_t index,
    const irep_idt &var_name)
{
  pos=body.insert_after(pos);
  instrument_cegis_operand(st, *pos, index, var_name);
  return pos;
}
