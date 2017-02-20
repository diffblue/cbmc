/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/c_types.h>

#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/instrument/instrument_var_ops.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/instrument/literals.h>
#include <cegis/danger/meta/literals.h>
#include <cegis/danger/options/danger_program.h>

namespace
{
const char PROG_SUFFIX[]="_prog";
}

std::string get_prog_var_name(const symbol_tablet &st,
    const goto_programt::targett &decl)
{
  const irep_idt &base_id=st.lookup(get_affected_variable(*decl)).base_name;
  std::string base_name(id2string(base_id));
  return base_name+=PROG_SUFFIX;
}

void execute_inv_prog(const symbol_tablet &st, goto_functionst &gf,
    const size_t max_solution_size, const goto_programt::targett &decl,
    const std::string &prog_base_name)
{
  goto_programt &body=get_entry_body(gf);
  goto_programt::targett pos=decl;
  goto_programt::targett execution=body.insert_after(++pos);
  execution->type=goto_program_instruction_typet::FUNCTION_CALL;
  execution->source_location=default_cegis_source_location();
  code_function_callt call;
  call.function()=st.lookup(DANGER_EXECUTE).symbol_expr();
  const std::string prog_name(get_cegis_meta_name(prog_base_name));
  const symbol_exprt prog_symbol(st.lookup(prog_name).symbol_expr());
  const typet size_type(unsigned_int_type());
  const constant_exprt index(from_integer(0u, size_type));
  const index_exprt first_elem(prog_symbol, index);
  call.arguments().push_back(address_of_exprt(first_elem));
  const typet size_arg_type(unsigned_char_type());
  const constant_exprt size(from_integer(max_solution_size, size_arg_type));
  call.arguments().push_back(size);
  execution->code=call;
}

void execute_inv_prog(const symbol_tablet &st, goto_functionst &gf,
    const size_t max_solution_size, const goto_programt::targett &decl)
{
  execute_inv_prog(st, gf, max_solution_size, decl,
      get_prog_var_name(st, decl));
}

goto_programt::targett add_inv_prog(invariant_programt &prog,
    goto_programt::targett pos, const size_t max_solution_size,
    const goto_programt::targett &decl)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  const std::string base_name(get_prog_var_name(st, decl));
  const typet size_type(unsigned_int_type());
  const constant_exprt size(from_integer(max_solution_size, size_type));
  const symbol_typet instr_type(CEGIS_INSTRUCTION_TYPE_NAME);
  const array_typet prog_type(instr_type, size);
  pos=declare_cegis_meta_variable(st, gf, pos, base_name, prog_type);
  execute_inv_prog(st, gf, max_solution_size, decl);
  return pos;
}

namespace
{
class declare_programst
{
  invariant_programt &prog;
  const size_t max_solution_size;
  goto_programt::targett pos;
public:
  declare_programst(invariant_programt &prog, const size_t max_solution_size,
      const goto_programt::targett &pos) :
      prog(prog), max_solution_size(max_solution_size), pos(pos)
  {
  }

  void operator()(const invariant_programt::invariant_loopt * const loop)
  {
    const symbol_tablet &st=prog.st;
    goto_functionst &gf=prog.gf;
    const invariant_programt::meta_vars_positionst &im=loop->meta_variables;
    pos=add_inv_prog(prog, pos, max_solution_size, im.Ix);
    const std::string dx_prog_name=get_prog_var_name(st, im.Ix);
    execute_inv_prog(st, gf, max_solution_size, im.Ix_prime, dx_prog_name);
  }

  const goto_programt::targett &get_pos() const
  {
    return pos;
  }
};
}

goto_programt::targett add_invariant_progs_to_learn(invariant_programt &prog,
    const size_t max_sol_sz)
{
  const invariant_programt::invariant_loopst loops(prog.get_loops());
  goto_programt::targett pos=prog.invariant_range.begin;
  if(loops.empty()) return pos;
  const declare_programst declare_progs(prog, max_sol_sz, --pos);
  return std::for_each(loops.begin(), loops.end(), declare_progs).get_pos();
}
