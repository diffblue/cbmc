#include <util/message.h>

#include <cegis/invariant/symex/learn/invariant_library.h>

template<class inv_progt>
invariant_exec_body_providert<inv_progt>::invariant_exec_body_providert(
    const std::string &exec_func_name, const inv_progt &prog) :
    exec_func_name(exec_func_name), original_prog(prog), initialised(false)
{
}

template<class inv_progt>
invariant_exec_body_providert<inv_progt>::~invariant_exec_body_providert()
{
}

template<class inv_progt>
const goto_programt &invariant_exec_body_providert<inv_progt>::operator ()()
{
  if (!initialised)
  {
    prog=original_prog;
    null_message_handlert msg;
    add_invariant_library(prog, msg, 0u, 0u, 1u, exec_func_name);
    initialised=true;
  }
  const irep_idt id(exec_func_name);
  const goto_functionst::function_mapt &function_map=prog.gf.function_map;
  const goto_functionst::function_mapt::const_iterator it=function_map.find(id);
  assert(function_map.end() != it);
  const goto_function_templatet<goto_programt> &f=it->second;
  assert(f.body_available());
  return f.body;
}
