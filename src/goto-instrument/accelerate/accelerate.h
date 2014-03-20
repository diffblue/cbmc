#include <util/namespace.h>

#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include "path.h"
#include "accelerator.h"
#include "trace_automaton.h"
#include "subsumed.h"

class acceleratet {
 public:
  acceleratet(goto_programt &_program,
              goto_functionst &_goto_functions,
              const namespacet &_ns) :
      program(_program),
      goto_functions(_goto_functions),
      ns(_ns)
  {
    natural_loops(program);
  }

  int accelerate_loop(goto_programt::targett &loop_header);
  int accelerate_loops();

  bool accelerate_path(patht &path, path_acceleratort &accelerator);

  void restrict_traces();

 protected:
  void find_paths(goto_programt::targett &loop_header,
                  pathst &loop_paths,
                  pathst &exit_paths,
                  goto_programt::targett &back_jump);

  void extend_path(goto_programt::targett &t,
                   goto_programt::targett &loop_header,
                   natural_loops_mutablet::natural_loopt &loop,
                   patht &prefix,
                   pathst &loop_paths,
                   pathst &exit_paths,
                   goto_programt::targett &back_jump);

  void insert_looping_path(goto_programt::targett &loop_header,
                           goto_programt::targett &back_jump,
                           goto_programt &looping_path,
                           patht &inserted_path);
  void insert_accelerator(goto_programt::targett &loop_header,
                          goto_programt::targett &back_jump,
                          path_acceleratort &accelerator,
                          subsumed_patht &subsumed);

  void insert_automaton(trace_automatont &automaton);

  goto_programt &program;
  goto_functionst &goto_functions;
  const namespacet &ns;
  natural_loops_mutablet natural_loops;
  subsumed_pathst subsumed;

  typedef map<patht, goto_programt> accelerator_mapt;
};

void accelerate_functions(
  goto_functionst &functions,
  const namespacet &ns);
