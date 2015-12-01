#include <algorithm>

#include <cegis/danger/util/danger_program_helper.h>
#include <cegis/danger/options/danger_program.h>

namespace
{
void store_skolem_choices_for_loop(danger_programt::loopt &loop)
{
  const danger_programt::program_ranget &range=loop.body;
  const goto_programt::targett &end=range.end;
  for (goto_programt::targett it=range.begin; it != end; ++it)
    if (is_nondet(it, end)) loop.skolem_choices.push_back(it);
}
}

void store_skolem_choices(danger_programt &program)
{
  danger_programt::loopst &loops=program.loops;
  std::for_each(loops.begin(), loops.end(), &store_skolem_choices_for_loop);
}

namespace
{
void store_x0_choices_for_range(danger_programt &program,
    const goto_programt::targett &begin, const goto_programt::targett &end)
{
  for (goto_programt::targett it=begin; it != end; ++it)
    if (is_nondet(it, end)) program.x0_choices.push_back(it);
}
}

void store_x0_choices(danger_programt &program)
{
  goto_programt::targett begin=program.danger_range.begin;
  goto_programt::targett end;
  typedef danger_programt::loopst loopst;
  const loopst &loops=program.loops;
  for (loopst::const_iterator it=loops.begin(); it != loops.end(); ++it)
  {
    end=it->body.begin;
    store_x0_choices_for_range(program, begin, end);
    begin=it->body.end;
  }
  end=program.danger_range.end;
  store_x0_choices_for_range(program, begin, end);
}
