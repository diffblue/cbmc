#include <util/expr_util.h>

#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/refactor/instructionset/processor_types.h>
#include <cegis/refactor/instructionset/execute_cegis_program.h>

#define SIZE_SUFFIX "_size"
namespace
{
std::string get_size_name(std::string program_name)
{
  return program_name+=SIZE_SUFFIX;
}
}

void declare_cegis_program(symbol_tablet &st, goto_functionst &gf,
    const std::string &processor, const std::string &program_name,
    const size_t size)
{
  const code_typet &code_type=to_code_type(st.lookup(processor).type);
  const typet &type=code_type.parameters().front().type();
  declare_global_meta_variable(st, program_name, type);
  const typet size_type(cegis_size_type());
  const std::string program_size(get_size_name(program_name));
  declare_global_meta_variable(st, gf, program_size, gen_zero(size_type));
}

goto_programt::targett call_processor(const symbol_tablet &st,
    goto_programt &body, goto_programt::targett pos,
    const std::string &processor, const std::string &program_name)
{
  pos=body.insert_after(pos);
  pos->type=goto_program_instruction_typet::FUNCTION_CALL;
  code_function_callt call;
  call.function()=st.lookup(processor).symbol_expr();
  code_function_callt::argumentst &args=call.arguments();
  args.push_back(st.lookup(program_name).symbol_expr());
  const std::string program_size(get_size_name(program_name));
  args.push_back(st.lookup(program_size).symbol_expr());
  pos->code=call;
  pos->source_location=default_cegis_source_location();
  return pos;
}
