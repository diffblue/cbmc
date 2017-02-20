/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <cegis/invariant/util/copy_instructions.h>
#include <cegis/invariant/symex/verify/insert_program.h>

namespace
{
class replace_name_visitort: public expr_visitort
{
  const replacementst &repl;
public:
  explicit replace_name_visitort(const replacementst &repl) :
      repl(repl)
  {
  }

  virtual ~replace_name_visitort()
  {
  }

  virtual void operator()(exprt &expr)
  {
    if(ID_symbol != expr.id()) return;
    symbol_exprt &symbol=to_symbol_expr(expr);
    for(replacementst::const_iterator it=repl.begin(); it != repl.end(); ++it)
      if(symbol.get_identifier() == it->first)
        symbol.set_identifier(it->second);
  }
};

class insert_instrt
{
  copy_instructionst &copy_instr;
  goto_programt &body;
  goto_programt::targett &pos;
  replace_name_visitort visitor;
public:
  insert_instrt(copy_instructionst &copy_instr, goto_programt &body,
      goto_programt::targett &pos, const replacementst &replacements) :
      copy_instr(copy_instr), body(body), pos(pos), visitor(replacements)
  {
  }

  void operator()(const goto_programt::const_targett &target)
  {
    copy_instr(pos=body.insert_after(pos), target);
    pos->guard.visit(visitor);
    pos->code.visit(visitor);
  }
};
}

void insert_program(goto_programt &body, goto_programt::targett pos,
    const goto_programt::instructionst &prog, const replacementst &replacements)
{
  copy_instructionst copy_instr;
  insert_instrt insert_instr(copy_instr, body, pos, replacements);
  goto_programt::const_targett first=prog.begin();
  goto_programt::const_targett last=prog.end();
  if(first == last) return;
  --last;
  for(; first != last; ++first)
    insert_instr(first);
  copy_instr.finalize(++pos, last);
}

void insert_program(goto_programt &body, const goto_programt::targett &pos,
    const goto_programt::instructionst &prog, const irep_idt &org_name,
    const irep_idt &new_name)
{
  replacementst repl;
  repl.insert(std::make_pair(org_name, new_name));
  insert_program(body, pos, prog, repl);
}

void insert_program(goto_programt &body, const goto_programt::targett &pos,
    const goto_programt::instructionst &prog)
{
  const replacementst replacements;
  insert_program(body, pos, prog, replacements);
}
