#include <algorithm>

#include <util/arith_tools.h>
#include <util/bv_arithmetic.h>
#include <util/namespace_utils.h>

#include <cegis/danger/options/danger_program.h>
#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/instrument/meta_variables.h>
#include <cegis/danger/constant/add_constant.h>
#include <cegis/danger/constant/literals_constant_strategy.h>

namespace
{
class compare_constantt
{
  const namespacet ns;
public:
  compare_constantt(const danger_programt &program) :
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
    if (ID_constant != expr.id()) return;
    const typet &expr_type=expr.type();
    const irep_idt &type_id=expr_type.id();
    if (ID_unsignedbv != type_id && ID_signedbv != type_id) return;
    const constant_exprt constant(to_constant_expr(expr));
    const bv_arithmetict bv(constant);
    const mp_integer::ullong_t value=bv.to_integer().to_ulong();
    constants.insert(from_integer(value, type));
    constants.insert(from_integer(value + 1, type));
    constants.insert(from_integer(value - 1, type));
  }

  void operator()(const goto_programt::instructiont &instr)
  {
    instr.code.visit(*this);
  }

  void operator()(const danger_programt::loopt &loop)
  {
    loop.guard.visit(*this);
  }

  constant_expr_visitort(const danger_programt &prog, constant_sett &constants) :
      ns(prog.st), type(danger_meta_type()), constants(constants)
  {
    const danger_programt::loopst &loops=prog.loops;
    constant_expr_visitort &op=*this;
    std::for_each(loops.begin(), loops.end(), op);
    prog.assertion.visit(op);
  }
};

class add_constantt
{
  danger_programt &program;
public:
  add_constantt(danger_programt &program) :
      program(program)
  {
  }

  void operator()(const constant_exprt &expr) const
  {
    add_danger_constant(program, expr);
    // XXX: Add negation of every constant?
    // if (!expr.is_zero()) add_danger_constant(program, unary_minus_exprt(expr));
  }
};
}

size_t literals_constant_strategy(danger_programt &program,
    const size_t max_length)
{
  const compare_constantt compare(program);
  constant_sett constants(compare);
  const constant_expr_visitort visitor(program, constants);
  const danger_programt::program_ranget &range=program.danger_range;
  std::for_each(range.begin, range.end, visitor);
  const add_constantt add_constant(program);
  std::for_each(constants.begin(), constants.end(), add_constant);
  return constants.size();
}
