#include <util/namespace.h>
#include <util/hash_cont.h>
#include <util/expr.h>

#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include "path.h"
#include "accelerator.h"
#include "trace_automaton.h"
#include "subsumed.h"
#include "scratch_program.h"
#include "acceleration_utils.h"

class acceleratet {
 public:
  acceleratet(goto_programt &_program,
              goto_functionst &_goto_functions,
              symbol_tablet &_symbol_table,
              bool _use_z3) :
      program(_program),
      goto_functions(_goto_functions),
      symbol_table(_symbol_table),
      ns(symbol_table),
      utils(symbol_table, goto_functions),
      use_z3(_use_z3)
  {
    natural_loops(program);
  }

  int accelerate_loop(goto_programt::targett &loop_header);
  int accelerate_loops();

  bool accelerate_path(patht &path, path_acceleratort &accelerator);

  void restrict_traces();

  static const int accelerate_limit = -1;

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

  goto_programt::targett find_back_jump(goto_programt::targett loop_header);

  void insert_looping_path(goto_programt::targett &loop_header,
                           goto_programt::targett &back_jump,
                           goto_programt &looping_path,
                           patht &inserted_path);
  void insert_accelerator(goto_programt::targett &loop_header,
                          goto_programt::targett &back_jump,
                          path_acceleratort &accelerator,
                          subsumed_patht &subsumed);

  void set_dirty_vars(path_acceleratort &accelerator);
  void add_dirty_checks();
  bool is_underapproximate(path_acceleratort &accelerator);

  void make_overflow_loc(goto_programt::targett loop_header,
                         goto_programt::targett &loop_end,
                         goto_programt::targett &overflow_loc);

  void insert_automaton(trace_automatont &automaton);
  void build_state_machine(trace_automatont::sym_mapt::iterator p,
                           trace_automatont::sym_mapt::iterator end,
                           state_sett &accept_states,
                           symbol_exprt state,
                           symbol_exprt next_state,
                           scratch_programt &state_machine);

  symbolt make_symbol(string name, typet type);
  void decl(symbol_exprt &sym, goto_programt::targett t);
  void decl(symbol_exprt &sym, goto_programt::targett t, exprt init);

  bool contains_nested_loops(goto_programt::targett &loop_header);

  goto_programt &program;
  goto_functionst &goto_functions;
  symbol_tablet &symbol_table;
  namespacet ns;
  natural_loops_mutablet natural_loops;
  subsumed_pathst subsumed;
  acceleration_utilst utils;

  typedef map<goto_programt::targett, goto_programt::targetst> overflow_mapt;
  overflow_mapt overflow_locs;

  expr_mapt dirty_vars_map;

  bool use_z3;
};

void accelerate_functions(
  goto_functionst &functions,
  symbol_tablet &ns,
  bool use_z3);
