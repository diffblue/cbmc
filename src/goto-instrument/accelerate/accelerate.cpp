#include <analyses/natural_loops.h>

#include <goto-programs/goto_functions.h>

#include <util/std_expr.h>

#include <iostream>
#include <list>

#include "accelerate.h"
#include "path.h"
#include "polynomial_accelerator.h"
//#include "symbolic_accelerator.h"

//#define DEBUG

using namespace std;


void acceleratet::find_paths(goto_programt::targett &loop_header,
                             pathst &loop_paths,
                             pathst &exit_paths) {
  patht empty_path;
  natural_loops_mutablet::natural_loopt loop;

  if (natural_loops.loop_map.find(loop_header) == natural_loops.loop_map.end()) {
    throw "Couldn't find loop";
  }

  loop = natural_loops.loop_map.find(loop_header)->second;

  return extend_path(loop_header, loop_header, loop, empty_path, loop_paths,
                         exit_paths);
}

void acceleratet::extend_path(goto_programt::targett &t,
                              goto_programt::targett &loop_header,
                              natural_loops_mutablet::natural_loopt &loop,
                              patht &prefix,
                              pathst &loop_paths,
                              pathst &exit_paths) {
  if (t == loop_header && !prefix.empty()) {
    // We've expanded a path that has returned to the loop header -- 
    // store this as a looping path.
    patht path(prefix);
    path.push_back(path_nodet(t));
    loop_paths.push_back(path);

    return;
  }

  if (loop.find(t) == loop.end()) {
    // We've dropped out of the loop -- accumulate this as a loop-exiting path.
    patht path(prefix);
    path.push_back(path_nodet(t));
    exit_paths.push_back(path);

    return;
  }

  // We're still in the loop -- see what we need to do to extend the path.
  if (t->is_goto()) {
    goto_programt::targett next = t;
    ++next;

    patht taken_prefix(prefix);
    taken_prefix.push_back(path_nodet(t, t->guard));

    patht not_taken_prefix(prefix);
    not_taken_prefix.push_back(path_nodet(t, not_exprt(t->guard)));

    for (goto_programt::targetst::iterator it = t->targets.begin();
         it != t->targets.end();
         ++it) {
      goto_programt::targett x = *it;

      if (x->location_number < t->location_number && x != loop_header) {
        // This is a back edge that isn't to the loop header -- it's an inner
        // loop, which we're just ignoring for the moment...
        // XXX - deal with nested loops
        continue;
      }

      extend_path(x, loop_header, loop, taken_prefix, loop_paths, exit_paths);
    }

    extend_path(next, loop_header, loop, not_taken_prefix, loop_paths, exit_paths);
  } else if (t->is_assert()) {
    // The assertion failing is an exit path, the assertion passing is a looping
    // path.
    goto_programt::targett next = t;
    ++next;

    patht pass_prefix(prefix);
    pass_prefix.push_back(path_nodet(t, t->guard));

    extend_path(next, loop_header, loop, pass_prefix, loop_paths, exit_paths);

    patht fail_path(prefix);
    fail_path.push_back(path_nodet(t, not_exprt(t->guard)));
    exit_paths.push_back(fail_path);
  } else {
    goto_programt::targetst succs;
    program.get_successors(t, succs);

    patht new_prefix(prefix);
    new_prefix.push_back(path_nodet(t));

    for (goto_programt::targetst::iterator it = succs.begin();
         it != succs.end();
         ++it) {
      extend_path(*it, loop_header, loop, new_prefix, loop_paths, exit_paths);
    }
  }
}

int acceleratet::accelerate_loop(goto_programt::targett &loop_header) {
  pathst loop_paths, exit_paths;
  int num_accelerated = 0;

  goto_programt::instructiont skip(SKIP);
  program.insert_before_swap(loop_header, skip);

  goto_programt::targett new_inst = loop_header;
  ++new_inst;

  natural_loops.loop_map.find(loop_header)->second.insert(new_inst);

  find_paths(loop_header, loop_paths, exit_paths);

  for (pathst::iterator it = loop_paths.begin();
       it != loop_paths.end();
       ++it) {
    goto_programt accelerator;

    if (accelerate(*it, accelerator)) {
      add_accelerator(loop_header, accelerator);
      num_accelerated++;
    }
  }

  return num_accelerated;
}

void acceleratet::add_accelerator(goto_programt::targett &loop_header,
                                  goto_programt &accelerator) {
  goto_programt::targett loop_body = loop_header;
  ++loop_body;

  goto_programt::targett jump = program.insert_before(loop_body);
  jump->make_goto();
  jump->guard = nondet_exprt(bool_typet());
  jump->targets.push_back(loop_body);

  program.destructive_insert(loop_body, accelerator);

  jump = program.insert_before(loop_body);
  jump->make_goto();
  jump->guard = true_exprt();
  jump->targets.push_back(loop_header);
}

int acceleratet::accelerate_loops()
{
  int num_accelerated = 0;

  for (natural_loops_mutablet::loop_mapt::iterator it =
          natural_loops.loop_map.begin();
       it != natural_loops.loop_map.end();
       ++it) {
    goto_programt::targett t = it->first;
    num_accelerated += accelerate_loop(t);
  }

  return num_accelerated;
}

bool acceleratet::accelerate(patht &path, goto_programt &accelerator) {
#ifdef DEBUG
  cout << "Accelerating:" << endl;

  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    program.output_instruction(ns, "OMG", cout, it->loc);
  }
#endif

  polynomial_acceleratort polynomial_accelerator(ns.get_symbol_table(), goto_functions);

  if (polynomial_accelerator.accelerate(path, accelerator)) {
#ifdef DEBUG
    cout << "Accelerated!" << endl;
    accelerator.output(ns, "accelerator", cout);
#endif

    return true;
  } else {
    return false;
  }
}

void accelerate_functions(
  goto_functionst &functions,
  const namespacet &ns)
{
  Forall_goto_functions (it, functions)
  {
    cout << "Accelerating function " << it->first << endl;
    acceleratet accelerate(it->second.body, functions, ns);

    int num_accelerated = accelerate.accelerate_loops();

    if (num_accelerated > 0) {
      cout << "Added " << num_accelerated << " accelerator(s)" << endl;
    }
  }
}
