/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#include <algorithm>

#include <cegis/invariant/util/copy_instructions.h>

void copy_instructionst::operator()(const goto_programt::targett &new_target,
    const goto_programt::const_targett &old_target)
{
  *new_target=*old_target;
  target_mapping.insert(std::make_pair(old_target, new_target));
}

void copy_instructionst::operator()(goto_programt::instructionst &new_instrs,
    const goto_programt::instructionst &old_instrs)
{
  for (goto_programt::const_targett pos=old_instrs.begin();
      pos != old_instrs.end(); ++pos)
  {
    new_instrs.push_back(goto_programt::instructiont());
    operator()(std::prev(new_instrs.end()), pos);
  }
}

goto_programt::targett copy_instructionst::operator()(
    goto_programt::instructionst &new_instrs,
    goto_programt::targett insert_after,
    const goto_programt::instructionst &old_instrs)
{
  assert(!old_instrs.empty());
  ++insert_after;
  for (goto_programt::const_targett pos=old_instrs.begin();
      pos != old_instrs.end(); ++pos)
  {
    insert_after=new_instrs.insert(insert_after, goto_programt::instructiont());
    operator()(insert_after++, pos);
  }
  return std::prev(insert_after);
}

namespace
{
typedef std::map<goto_programt::const_targett, goto_programt::targett> target_mapt;

class fix_targetst
{
  const target_mapt &target_mapping;
public:
  fix_targetst(
      const std::map<goto_programt::const_targett, goto_programt::targett> &target_mapping) :
      target_mapping(target_mapping)
  {
  }

  void operator()(goto_programt::targett &target) const
  {
    const target_mapt::const_iterator it=target_mapping.find(target);
    assert(target_mapping.end() != it);
    target=it->second;
  }

  void operator()(
      const std::pair<goto_programt::const_targett, goto_programt::targett> &entry) const
  {
    goto_programt::targetst &targets=entry.second->targets;
    std::for_each(targets.begin(), targets.end(), *this);
  }
};
}

void copy_instructionst::finalize()
{
  const fix_targetst fix_targets(target_mapping);
  std::for_each(target_mapping.begin(), target_mapping.end(), fix_targets);
  target_mapping.clear();
}

namespace
{
const char DANGER_SKIP_LABEL[]="__CPROVER_danger_skip";
}

void copy_instructionst::finalize(const goto_programt::targett &new_target,
    const goto_programt::const_targett &old_target)
{
  new_target->labels.push_back(DANGER_SKIP_LABEL);
  new_target->target_number=0;
  target_mapping.insert(std::make_pair(old_target, new_target));
  finalize();
}

namespace
{
class skip_removert
{
  goto_programt::instructionst &instrs;
  typedef std::map<goto_programt::targett, goto_programt::targett> skipst;
  skipst skips;
public:
  explicit skip_removert(goto_programt::instructionst &instrs) :
      instrs(instrs)
  {
  }

  void operator()(const goto_programt::targett &target)
  {
    const goto_programt::instructiont::labelst &labels=target->labels;
    if (labels.empty()) return;
    if (id2string(labels.front()) != DANGER_SKIP_LABEL) return;
    goto_programt::targett next(target);
    skips.insert(std::make_pair(target, ++next));
  }

  void operator()(goto_programt::targett first,
      const goto_programt::targett &last)
  {
    for (; first != last; ++first)
      this->operator()(first);
  }

  void replace_targets(goto_programt::instructiont &instr) const
  {
    goto_programt::targetst &targets=instr.targets;
    goto_programt::targetst::iterator it;
    for (it=targets.begin(); it != targets.end(); ++it)
    {
      skipst::const_iterator e=skips.find(*it);
      if (skips.end() == e) continue;
      *it=e->second;
    }
  }

  void remove()
  {
    for (goto_programt::instructiont &instr : instrs)
      replace_targets(instr);
    for (const skipst::value_type &skip : skips)
      instrs.erase(skip.first);
  }
};
}

void invariant_make_presentable(goto_programt::instructionst &instrs)
{
  const goto_programt::targett &begin=instrs.begin();
  const goto_programt::targett &last=instrs.end();
  if (begin == last) return;
  skip_removert op(instrs);
  op(begin, std::prev(last));
  op.remove();
}

void copy_instructions(goto_programt::instructionst &target,
    const goto_programt::instructionst &source)
{
  copy_instructionst copy;
  copy(target, source);
  copy.finalize();
}

goto_programt::targett copy_instructions(goto_programt::instructionst &target,
    goto_programt::targett pos, const goto_programt::instructionst &source)
{
  copy_instructionst copy;
  goto_programt::targett result=copy(target, pos, source);
  copy.finalize();
  return result;
}
