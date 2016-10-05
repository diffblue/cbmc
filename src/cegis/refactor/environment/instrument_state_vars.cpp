#include <cegis/refactor/environment/instrument_state_vars.h>

void instrument_state_vars(goto_programt &body,
    const goto_programt::targett &first, const goto_programt::targett &last,
    std::function<bool(const goto_programt::instructiont &)> predicate)
{
  // TODO: Implement
  assert(false);
}

namespace
{
bool yes(const goto_programt::instructiont &instr)
{
  return true;
}
}

void instrument_state_vars(goto_programt &body,
    const goto_programt::targett &first, const goto_programt::targett &last)
{
  instrument_state_vars(body, first, last, yes);
}
