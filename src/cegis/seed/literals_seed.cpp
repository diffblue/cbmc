/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <iterator>

#include <util/arith_tools.h>

#include <cegis/cegis-util/program_helper.h>
#include <cegis/invariant/util/invariant_constraint_variables.h>
#include <cegis/invariant/util/invariant_program_helper.h>
#include <cegis/seed/literals_seed.h>

danger_literals_seedt::danger_literals_seedt(const danger_programt &prog) :
    prog(prog), seeded(false)
{
}

danger_literals_seedt::~danger_literals_seedt()
{
}

namespace
{
class is_same_symbolt
{
  const irep_idt &name;
public:
  explicit is_same_symbolt(const irep_idt &name) :
      name(name)
  {
  }

  bool operator()(const exprt &expr) const
  {
    if(ID_symbol != expr.id()) return false;
    return name == to_symbol_expr(expr).get_identifier();
  }
};

typedef std::set<irep_idt> keyst;
typedef std::deque<constant_exprt> valuest;

class add_symbolt
{
  keyst &keys;
public:
  explicit add_symbolt(keyst &keys) :
      keys(keys)
  {
  }

  void operator()(const exprt &expr) const
  {
    if(ID_symbol != expr.id()) return;
    keys.insert(to_symbol_expr(expr).get_identifier());
  }
};

class compare_literalt
{
  const constant_exprt &literal;
public:
  explicit compare_literalt(const constant_exprt &literal) :
      literal(literal)
  {
  }

  bool operator()(const constant_exprt &expr) const
  {
    return literal.get_value() == expr.get_value();
  }
};

class add_literalt
{
  valuest &values;
public:
  explicit add_literalt(valuest &values) :
      values(values)
  {
  }

  void operator()(const exprt &expr) const
  {
    if(ID_constant != expr.id()) return;
    const constant_exprt &new_literal=to_constant_expr(expr);
    const compare_literalt compare(new_literal);
    if(values.end() != std::find_if(values.begin(), values.end(), compare))
      return;
    values.push_back(new_literal);
  }
};

class init_pool_keyst: public const_expr_visitort
{
  keyst &keys;
  const irep_idt &var;
public:
  init_pool_keyst(keyst &keys, const irep_idt &var) :
      keys(keys), var(var)
  {
  }

  virtual ~init_pool_keyst()
  {
  }

  virtual void operator()(const exprt &expr)
  {
    exprt::operandst ops(expr.operands());
    if(ops.size() < 2u) return;
    const is_same_symbolt pred(var);
    if(ops.end() == std::find_if(ops.begin(), ops.end(), pred)) return;
    const add_symbolt add(keys);
    std::for_each(ops.begin(), ops.end(), add);
  }

  void operator()(const goto_programt::instructiont &instr)
  {
    const_expr_visitort &visitor=*this;
    instr.guard.visit(visitor);
    instr.code.visit(visitor);
  }
};

typedef std::map<keyst, valuest> pool_storaget;

pool_storaget::const_iterator find(const pool_storaget &pool,
    const irep_idt &id)
{
  for(pool_storaget::const_iterator it=pool.begin(); it != pool.end(); ++it)
  {
    const keyst &keys=it->first;
    if(std::find(keys.begin(), keys.end(), id) == keys.end()) continue;
    return it;
  }
  return pool.end();
}

class create_pool_keyst
{
  const danger_programt &prog;
  pool_storaget &pool;
public:
  create_pool_keyst(const danger_programt &prog, pool_storaget &pool) :
      prog(prog), pool(pool)
  {
  }

  void operator()(const symbol_exprt &var)
  {
    const irep_idt &id=var.get_identifier();
    pool_storaget::const_iterator it=find(pool, id);
    if(pool.end() != it) return;
    keyst newKey;
    newKey.insert(id);
    const init_pool_keyst add(newKey, id);
    const goto_programt &body=get_entry_body(prog.gf);
    const goto_programt::instructionst &instrs=body.instructions;
    std::for_each(instrs.begin(), instrs.end(), add);
    it=pool.insert(std::make_pair(newKey, valuest())).first;
  }
};

const keyst &get_first(const std::pair<keyst, valuest> &pair)
{
  return pair.first;
}

class is_keyt
{
  const exprt::operandst &ops;
public:
  explicit is_keyt(const exprt::operandst &ops) :
      ops(ops)
  {
  }

  bool operator()(const irep_idt &key) const
  {
    for(exprt::operandst::const_iterator it=ops.begin(); ops.end() != it; ++it)
    {
      const exprt &op=*it;
      if(ID_symbol != op.id()) continue;
      if(key == to_symbol_expr(op).get_identifier()) return true;
    }
    return false;
  }

  bool operator()(const keyst &keys) const
  {
    return keys.end() != std::find_if(keys.begin(), keys.end(), *this);
  }
};

std::deque<keyst>::const_iterator find_key(const std::deque<keyst> &keys,
    const exprt::operandst &ops)
{
  const is_keyt is_key(ops);
  return std::find_if(keys.begin(), keys.end(), is_key);
}

class scrape_literalst: public const_expr_visitort
{
  std::deque<keyst> keys;
  pool_storaget &pool;
public:
  explicit scrape_literalst(pool_storaget &p) :
      pool(p)
  {
    std::transform(p.begin(), p.end(), std::back_inserter(keys), &get_first);
  }

  virtual ~scrape_literalst()
  {
  }

  virtual void operator()(const exprt &expr)
  {
    const exprt::operandst &ops=expr.operands();
    if(ops.size() < 2u) return;
    std::deque<keyst>::const_iterator it=find_key(keys, ops);
    if(keys.end() == it) return;
    const add_literalt add(pool[*it]);
    std::for_each(ops.begin(), ops.end(), add);
  }

  void operator()(const goto_programt::instructiont &instr)
  {
    const_expr_visitort &visitor=*this;
    instr.code.visit(visitor);
    instr.guard.visit(visitor);
  }
};

class value_poolt
{
  const constraint_varst &vs;
  pool_storaget pool;
public:
  value_poolt(const danger_programt &prog, const constraint_varst &vars) :
      vs(vars)
  {
    const create_pool_keyst create_keys(prog, pool);
    std::for_each(vars.begin(), vars.end(), create_keys);
    const goto_programt &body=get_entry_body(prog.gf);
    const goto_programt::instructionst &instr=body.instructions;
    const scrape_literalst scrape(pool);
    std::for_each(instr.begin(), instr.end(), scrape);
  }

  const valuest &operator[](const irep_idt &id) const
  {
    pool_storaget::const_iterator it=find(pool, id);
    assert(pool.end() != it);
    return it->second;
  }

  size_t size() const
  {
    size_t size=0;
    for(pool_storaget::const_iterator it=pool.begin(); it != pool.end(); ++it)
      size=std::max(size, it->second.size());
    return size;
  }

  valuest::value_type get_value(const irep_idt &id, const typet &type,
      const size_t index) const
  {
    const valuest &values=operator[](id);
    if(values.empty())
      return from_integer(0, type);
    return values.at(index % values.size());
  }

  void seed(danger_verify_configt::counterexamplest &counterexamples) const
  {
    const size_t sz=size();
    for(size_t i=0; i < sz; ++i)
    {
      danger_verify_configt::counterexamplet ce;
      for(constraint_varst::const_iterator v=vs.begin(); v != vs.end(); ++v)
      {
        const irep_idt &id=v->get_identifier();
        const typet &type=v->type();
        ce.insert(std::make_pair(id, get_value(id, type, i)));
      }
      counterexamples.push_back(ce);
    }
  }
};
}

void danger_literals_seedt::operator()(
    danger_verify_configt::counterexamplest &counterexamples)
{
  if(seeded) return;
  constraint_varst vars;
  get_invariant_constraint_vars(vars, prog);
  const value_poolt pool(prog, vars);
  pool.seed(counterexamples);
  seeded=true;
}
