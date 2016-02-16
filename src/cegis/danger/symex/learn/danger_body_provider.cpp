#include <util/message.h>

#include <cegis/danger/meta/literals.h>
#include <cegis/danger/symex/learn/danger_library.h>
#include <cegis/danger/symex/learn/danger_body_provider.h>

danger_body_providert::danger_body_providert(const danger_programt &prog) :
    original_prog(prog), initialised(false)
{
}

danger_body_providert::~danger_body_providert()
{
}

const goto_programt &danger_body_providert::operator ()()
{
  if (!initialised)
  {
    prog=original_prog;
    null_message_handlert msg;
    add_danger_library(prog, msg, 0u, 0u, 1u);
    initialised=true;
  }
  const irep_idt id(DANGER_EXECUTE);
  const goto_functionst::function_mapt &function_map=prog.gf.function_map;
  const goto_functionst::function_mapt::const_iterator it=function_map.find(id);
  assert(function_map.end() != it);
  const goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available());
  return f.body;
}
