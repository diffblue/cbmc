#include <ansi-c/expr2c.h>
#include <util/namespace.h>
#include <util/symbol_table.h>

#include <cegis/instrument/literals.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/refactor/instructionset/processor_symbols.h>

#define VARIABLE_ARRAY_PREFIX CEGIS_PREFIX "variable_array_"

std::string cegis_operand_array_name(const symbol_tablet &st, const typet &type)
{
  std::string result(VARIABLE_ARRAY_PREFIX);
  return result+=type2c(type, namespacet(st));
}

#define OPERAND_ID_MEMBER_NAME_PREFIX "op_"

std::string cegis_operand_base_name(const size_t op)
{
  std::string name(OPERAND_ID_MEMBER_NAME_PREFIX);
  return name+=std::to_string(op);
}

namespace
{
index_exprt cegis_instr(const symbol_tablet &st, const std::string &func_name)
{
  const char * const prog_base_name=CEGIS_PROC_PROGRAM_PARAM_ID;
  const std::string prog_name(get_local_meta_name(func_name, prog_base_name));
  const symbol_exprt prog(st.lookup(prog_name).symbol_expr());
  const char * const index_base_name=CEGIS_PROC_INSTR_INDEX;
  const std::string index_name(get_local_meta_name(func_name, index_base_name));
  const symbol_exprt index(st.lookup(index_name).symbol_expr());
  return index_exprt(prog, index);
}
}

member_exprt cegis_opcode(const symbol_tablet &st, const std::string &func_name)
{
  const index_exprt instr(cegis_instr(st, func_name));
  return member_exprt(instr, CEGIS_PROC_OPCODE_MEMBER_NAME);
}

member_exprt cegis_operand_id(const symbol_tablet &st,
    const std::string &func_name, const size_t op)
{
  const index_exprt instr(cegis_instr(st, func_name));
  const std::string member_name(cegis_operand_base_name(op));
  return member_exprt(instr, member_name);
}

dereference_exprt cegis_operand(const symbol_tablet &st,
    const std::string &func_name, const typet &type, const size_t op)
{
  const member_exprt operand_id(cegis_operand_id(st, func_name, op));
  const std::string array_name(cegis_operand_array_name(st, type));
  const symbol_exprt array(st.lookup(array_name).symbol_expr());
  return dereference_exprt(index_exprt(array, operand_id), type);
}
