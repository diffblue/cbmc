/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <ansi-c/c_types.h>
#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/cegis-util/program_helper.h>

namespace
{
class compare_constantt
{
  const namespacet ns;
public:
  compare_constantt(const symbol_tablet &st) :
      ns(st)
  {
  }

  bool operator()(const constant_exprt &lhs, const constant_exprt &rhs) const
  {
    return lhs.get_value() < rhs.get_value();
  }
};

typedef std::set<constant_exprt, compare_constantt> constant_sett;

class constant_expr_visitort: public const_expr_visitort
{
  const namespacet ns;
  const typet type;
  constant_sett &constants;
public:
  constant_expr_visitort(const symbol_tablet &st, constant_sett &constants) :
      ns(st), type(unsigned_int_type()), constants(constants)
  {
  }

  virtual void operator()(const exprt &expr)
  {
    if (ID_constant != expr.id()) return;
    const typet &expr_type=expr.type();
    const irep_idt &type_id=expr_type.id();
    if (ID_unsignedbv != type_id && ID_signedbv != type_id) return;
    const constant_exprt constant(to_constant_expr(expr));
    const bv_arithmetict bv(constant);
    const mp_integer::llong_t value=bv.to_integer().to_long();
    constants.insert(from_integer(static_cast<unsigned int>(value), type));
  }

  void operator()(const goto_programt::instructiont &instr)
  {
    if (is_builtin(instr.source_location)) return;
    instr.code.visit(*this);
    instr.guard.visit(*this);
  }
};
}

std::vector<constant_exprt> collect_integer_literals(const symbol_tablet &st,
    const goto_functionst &gf)
{
  const compare_constantt compare(st);
  constant_sett constants(compare);
  const constant_expr_visitort visitor(st, constants);
  const goto_programt::instructionst &instrs=get_entry_body(gf).instructions;
  std::for_each(instrs.begin(), instrs.end(), visitor);
  return std::vector<constant_exprt>(constants.begin(), constants.end());
}
