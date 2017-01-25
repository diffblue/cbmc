/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>
#include <cassert>
#include <cstdlib>

#include <cegis/genetic/random_individual.h>
#include <cegis/genetic/random_cross.h>

random_crosst::random_crosst(random_individualt &random) :
    random(random)
{
}

random_crosst::~random_crosst()
{
}

namespace
{
void fix_result_ops(random_crosst::programt::value_type &instr,
    const size_t org_index, const size_t new_index, const size_t num_vars)
{
  for (random_crosst::programt::value_type::opt &op : instr.ops)
  {
    if (op < num_vars) continue;
    if (org_index > new_index) op-=(org_index - new_index);
    else op+=(new_index - org_index);
    op%=(num_vars + new_index);
  }
}
}

void random_crosst::operator ()(const individualst &parents,
    const individualst &children)
{
  assert(parents.size() >= 2 && children.size() >= 2);
  const populationt::value_type &father=*parents.front();
  const populationt::value_type &mother=*parents[1u];
  populationt::value_type &son=*children.front();
  populationt::value_type &daughter=*children[1u];

  const populationt::value_type::x0t &f_x0=father.x0;
  const populationt::value_type::x0t &m_x0=mother.x0;
  populationt::value_type::x0t &s_x0=son.x0;
  populationt::value_type::x0t &d_x0=daughter.x0;
  const size_t x0_offset=random.rand() % (f_x0.size() + 1);
  std::copy(f_x0.begin(), f_x0.begin() + x0_offset, s_x0.begin());
  std::copy(m_x0.begin() + x0_offset, m_x0.end(), s_x0.begin() + x0_offset);
  std::copy(m_x0.begin(), m_x0.begin() + x0_offset, d_x0.begin());
  std::copy(f_x0.begin() + x0_offset, f_x0.end(), d_x0.begin() + x0_offset);

  const size_t prog_limit=parents.front()->programs.size();
  const size_t target_prog_index=random.rand() % prog_limit;
  // XXX: Use two two prog_indexes?
  const programt &f_prog=father.programs[target_prog_index];
  const programt &m_prog=mother.programs[target_prog_index];
  programt &s_prog=son.programs[target_prog_index];
  programt &d_prog=daughter.programs[target_prog_index];

  const size_t min_prog_sz=random.get_min_prog_size(target_prog_index);
  const size_t max_prog_sz=random.get_max_prog_size(target_prog_index);
  const size_t f_sz=f_prog.size();
  const size_t m_sz=m_prog.size();
  if (f_sz < min_prog_sz || m_sz < min_prog_sz) return;
  const size_t all_instrs=f_sz + m_sz;
  const size_t child_max=std::min(max_prog_sz, all_instrs - min_prog_sz);
  const size_t father_offset=random.rand() % (f_sz + 1);
  size_t mo_lower=father_offset + m_sz;
  mo_lower=mo_lower <= child_max ? 0u : mo_lower - child_max;
  const size_t mo_upper=std::min(m_sz, child_max + father_offset - f_sz);
  assert(mo_upper >= mo_lower);
  const size_t mo_range=mo_upper - mo_lower + 1;
  const size_t mother_offset=
      mo_range ? mo_lower + random.rand() % mo_range : 0u;

  s_prog.resize(father_offset + m_sz - mother_offset);
  d_prog.resize(mother_offset + f_sz - father_offset);
  assert(!s_prog.empty());
  assert(!d_prog.empty());
  std::copy(f_prog.begin(), f_prog.begin() + father_offset, s_prog.begin());
  std::copy(m_prog.begin(), m_prog.begin() + mother_offset, d_prog.begin());
  const size_t num_vars=random.get_num_vars();
  for (size_t f=father_offset, m=mother_offset; m < m_sz; ++f, ++m)
    fix_result_ops(s_prog[f]=m_prog[m], m, f, num_vars);
  for (size_t m=mother_offset, f=father_offset; f < f_sz; ++m, ++f)
    fix_result_ops(d_prog[m]=f_prog[f], f, m, num_vars);
}
