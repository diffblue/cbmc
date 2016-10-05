#include <cegis/refactor/environment/instrument_state_vars.h>

void instrument_state_vars(goto_programt &body,
    const goto_programt::targett &first, const goto_programt::targett &last,
    const std::function<bool(const typet &)> predicate)
{
  // TODO: Implement
  assert(false);
}

namespace
{
bool yes(const typet &instr)
{
  return true;
}
}

void instrument_state_vars(goto_programt &body,
    const goto_programt::targett &first, const goto_programt::targett &last)
{
  instrument_state_vars(body, first, last, yes);
}
