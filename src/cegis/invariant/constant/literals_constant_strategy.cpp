/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>

#include <cegis/cegis-util/constant_width.h>
#include <cegis/instrument/meta_variables.h>
#include <cegis/invariant/options/invariant_program.h>
#include <cegis/invariant/constant/add_constant.h>
#include <cegis/invariant/constant/literals_constant_strategy.h>

namespace
{
class compare_constantt
{
  const namespacet ns;
public:
  explicit compare_constantt(const invariant_programt &program) :
      ns(program.st)
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
  virtual ~constant_expr_visitort()
  {
  }

  virtual void operator()(const exprt &expr)
  {
    if(ID_constant != expr.id()) return;
    const typet &expr_type=expr.type();
    const irep_idt &type_id=expr_type.id();
    if(ID_unsignedbv != type_id && ID_signedbv != type_id) return;
    const constant_exprt constant(to_constant_expr(expr));
    const bv_arithmetict bv(constant);
    const mp_integer value=bv.to_integer();
    constants.insert(from_integer(value, type));
    // XXX: Add constant +/- 1?
    // constants.insert(from_integer(value + 1, type));
    // constants.insert(from_integer(value - 1, type));
  }

  void operator()(const goto_programt::instructiont &instr)
  {
    instr.code.visit(*this);
    instr.guard.visit(*this);
  }

  void operator()(const invariant_programt::invariant_loopt *loop)
  {
    loop->guard.visit(*this);
  }

  constant_expr_visitort(const invariant_programt &prog,
      constant_sett &constants) :
      ns(prog.st), type(cegis_default_integer_type()), constants(constants)
  {
    const invariant_programt::const_invariant_loopst loops=prog.get_loops();
    constant_expr_visitort &op=*this;
    std::for_each(loops.begin(), loops.end(), op);
    prog.assertion.visit(op);
  }
};
}

std::vector<constant_exprt> collect_literal_constants(
    const invariant_programt &program)
{
  const compare_constantt compare(program);
  constant_sett constants(compare);
  const constant_expr_visitort visitor(program, constants);
  const invariant_programt::program_ranget &range=program.invariant_range;
  std::for_each(range.begin, range.end, visitor);
  return std::vector<constant_exprt>(constants.begin(), constants.end());
}

size_t literals_constant_strategy(invariant_programt &program,
    const size_t max_length)
{
  const std::vector<constant_exprt> lit(collect_literal_constants(program));
  size_t max_word_width=0u;
  for(const constant_exprt &expr : lit)
  {
    add_danger_constant(program, expr);
    // XXX: Add negation of every constant?
    // if (!expr.is_zero()) add_danger_constant(program, unary_minus_exprt(expr));
    max_word_width=std::max(max_word_width, get_min_word_width(expr));
  }
  return max_word_width;
}
