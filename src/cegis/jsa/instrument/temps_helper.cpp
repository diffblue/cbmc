#include <util/expr_util.h>

#include <cegis/jsa/options/jsa_program.h>
#include <cegis/jsa/instrument/jsa_meta_data.h>
#include <cegis/jsa/preprocessing/add_constraint_meta_variables.h>

goto_programt::targett zero_jsa_temps(jsa_programt &prog, goto_programt::targett pos)
{
  symbol_tablet &st=prog.st;
  goto_functionst &gf=prog.gf;
  for (const symbol_tablet::symbolst::value_type &symbol : st.symbols)
  {
    if (std::string::npos == id2string(symbol.first).find(JSA_TMP_PREFIX))
      continue;
    const symbol_exprt lhs(symbol.second.symbol_expr());
    pos=jsa_assign(st, gf, pos, lhs, gen_zero(lhs.type()));
  }
  return pos;
}
