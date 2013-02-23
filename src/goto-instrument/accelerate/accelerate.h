#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include <namespace.h>

#include "path.h"

class acceleratet {
 public:
  acceleratet(goto_programt &_program,
              goto_functionst &_goto_functions,
              namespacet &_ns) :
      program(_program),
      goto_functions(_goto_functions),
      ns(_ns)
  {
    natural_loops(program);
  }

  int accelerate_loop(goto_programt::targett &loop_header);
  int accelerate_loops();

  bool accelerate(patht &path, goto_programt &accelerator);

 protected:
  void find_paths(goto_programt::targett &loop_header,
                  pathst &loop_paths,
                  pathst &exit_paths);

  void extend_path(goto_programt::targett &t,
                   goto_programt::targett &loop_header,
                   natural_loopst::natural_loopt &loop,
                   patht &prefix,
                   pathst &loop_paths,
                   pathst &exit_paths);

  void add_accelerator(goto_programt::targett &loop_header,
                       goto_programt &accelerator);

  goto_programt &program;
  goto_functionst &goto_functions;
  namespacet &ns;
  natural_loopst natural_loops;

  typedef map<patht, goto_programt> accelerator_mapt;
};

void accelerate_functions(goto_functionst &functions, namespacet &ns);
