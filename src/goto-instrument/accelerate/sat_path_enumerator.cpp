#include <iostream>
#include <map>
#include <set>
#include <string>
#include <sstream>
#include <algorithm>
#include <ctime>

#include <goto-programs/goto_program.h>
#include <goto-programs/wp.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_functions.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>

#include <analyses/goto_check.h>

#include <ansi-c/expr2c.h>

#include <util/symbol_table.h>
#include <util/options.h>
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/i2string.h>
#include <util/find_symbols.h>
#include <util/rename.h>
#include <util/simplify_expr.h>
#include <util/replace_expr.h>
#include <util/arith_tools.h>

#include "sat_path_enumerator.h"
#include "polynomial_accelerator.h"
#include "accelerator.h"
#include "util.h"
#include "overflow_instrumenter.h"

#define DEBUG


bool sat_path_enumeratort::next(patht &path) {
  scratch_programt program(symbol_table);

  program.append(fixed);
  program.append(fixed);

  // Let's make sure that we get a path we have not seen before.
  for (list<distinguish_valuest>::iterator it = accelerated_paths.begin();
       it != accelerated_paths.end();
       ++it) {
    exprt new_path = false_exprt();

    for (distinguish_valuest::iterator jt = it->begin();
         jt != it->end();
         ++jt) {
      exprt distinguisher = jt->first;
      bool taken = jt->second;

      if (taken) {
        not_exprt negated(distinguisher);
        distinguisher.swap(negated);
      }

      or_exprt disjunct(new_path, distinguisher);
      new_path.swap(disjunct);
    }

    program.assume(new_path);
  }

  program.add_instruction(ASSERT)->guard = false_exprt();

  try {
    if (program.check_sat()) {
#ifdef DEBUG
      std::cout << "Found a path" << std::endl;
#endif
      build_path(program, path);
      record_path(program);

      return true;
    }
  } catch (string s) {
    std::cout << "Error in fitting polynomial SAT check: " << s << endl;
  } catch (const char *s) {
    std::cout << "Error in fitting polynomial SAT check: " << s << endl;
  }

  return false;
}

void sat_path_enumeratort::find_distinguishing_points() {
  for (natural_loops_mutablet::natural_loopt::iterator it = loop.begin();
       it != loop.end();
       ++it) {
    goto_programt::targetst succs;

    goto_program.get_successors(*it, succs);

    if (succs.size() > 1) {
      // This location has multiple successors -- each successor is a
      // distinguishing point.
      for (goto_programt::targetst::iterator jt = succs.begin();
           jt != succs.end();
           ++jt) {
        symbolt distinguisher_sym =
          utils.fresh_symbol("polynomial::distinguisher", bool_typet());
        symbol_exprt distinguisher = distinguisher_sym.symbol_expr();

        distinguishing_points[*jt] = distinguisher;
        distinguishers.push_back(distinguisher);
      }
    }
  }
}

void sat_path_enumeratort::build_path(
    scratch_programt &scratch_program, patht &path) {
  goto_programt::targett t = loop_header;

  do {
    goto_programt::targett next;
    goto_programt::targetst succs;

    goto_program.get_successors(t, succs);

    // We should have a looping path, so we should never hit a location
    // with no successors.
    assert(succs.size() > 0);

    if (succs.size() == 1) {
      // Only one successor -- accumulate it and move on.
      path.push_back(path_nodet(t));
      t = succs.front();
      continue;
    }

    // We have multiple successors.  Examine the distinguisher variables
    // to see which branch was taken.
    bool found_branch = false;

    for (goto_programt::targetst::iterator it = succs.begin();
         it != succs.end();
         ++it) {
      exprt &distinguisher = distinguishing_points[*it];
      bool taken = scratch_program.eval(distinguisher).is_true();

      if (taken) {
        if (!found_branch ||
            ((*it)->location_number < next->location_number)) {
          next = *it;
        }

        found_branch = true;
      }
    }

    assert(found_branch);

    exprt cond = nil_exprt();

    if (t->is_goto()) {
      // If this was a conditional branch (it probably was), figure out
      // if we hit the "taken" or "not taken" branch & accumulate the
      // appropriate guard.
      cond = not_exprt(t->guard);

      for (goto_programt::targetst::iterator it = t->targets.begin();
           it != t->targets.end();
           ++it) {
        if (next == *it) {
          cond = t->guard;
          break;
        }
      }
    }

    path.push_back(path_nodet(t, cond));

    t = next;
  } while (t != loop_header && (loop.find(t) != loop.end()));
}

/*
 * Take the body of the loop we are accelerating and produce a fixed-path
 * version of that body, suitable for use in the fixed-path acceleration we
 * will be doing later.
 */
void sat_path_enumeratort::build_fixed() {
  scratch_programt scratch(symbol_table);
  map<exprt, exprt> shadow_distinguishers;

  fixed.copy_from(goto_program);

  Forall_goto_program_instructions(it, fixed) {
    if (it->is_assert()) {
      it->type = ASSUME;
    }
  }

  // We're only interested in paths that loop back to the loop header.
  // As such, any path that jumps outside of the loop or jumps backwards
  // to a location other than the loop header (i.e. a nested loop) is not
  // one we're interested in, and we'll redirect it to this assume(false).
  goto_programt::targett kill = fixed.add_instruction(ASSUME);
  kill->guard = false_exprt();

  // Make a sentinel instruction to mark the end of the loop body.
  // We'll use this as the new target for any back-jumps to the loop
  // header.
  goto_programt::targett end = fixed.add_instruction(SKIP);

  // A pointer to the start of the fixed-path body.  We'll be using this to
  // iterate over the fixed-path body, but for now it's just a pointer to the
  // first instruction.
  goto_programt::targett fixedt = fixed.instructions.begin();

  // Create shadow distinguisher variables.  These guys identify the path that
  // is taken through the fixed-path body.
  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    exprt &distinguisher = *it;
    symbolt shadow_sym = utils.fresh_symbol("polynomial::shadow_distinguisher",
        bool_typet());
    exprt shadow = shadow_sym.symbol_expr();
    shadow_distinguishers[distinguisher] = shadow;

    goto_programt::targett assign = fixed.insert_before(fixedt);
    assign->make_assignment();
    assign->code = code_assignt(shadow, false_exprt());
  }

  // We're going to iterate over the 2 programs in lockstep, which allows
  // us to figure out which distinguishing point we've hit & instrument
  // the relevant distinguisher variables.
  for (goto_programt::targett t = goto_program.instructions.begin();
       t != goto_program.instructions.end();
       ++t, ++fixedt) {
    distinguish_mapt::iterator d = distinguishing_points.find(t);

    if (loop.find(t) == loop.end()) {
      // This instruction isn't part of the loop...  Just remove it.
      fixedt->make_skip();
      continue;
    }
    
    if (d != distinguishing_points.end()) {
      // We've hit a distinguishing point.  Set the relevant shadow
      // distinguisher to true.
      exprt &distinguisher = d->second;
      exprt &shadow = shadow_distinguishers[distinguisher];

      goto_programt::targett assign = fixed.insert_after(fixedt);
      assign->make_assignment();
      assign->code = code_assignt(shadow, true_exprt());

      assign->swap(*fixedt);
      fixedt = assign;
    }

    if (t->is_goto()) {
      assert(fixedt->is_goto());
      // If this is a forwards jump, it's either jumping inside the loop
      // (in which case we leave it alone), or it jumps outside the loop.
      // If it jumps out of the loop, it's on a path we don't care about
      // so we kill it.
      //
      // Otherwise, it's a backwards jump.  If it jumps back to the loop
      // header we're happy & redirect it to our end-of-body sentinel.
      // If it jumps somewhere else, it's part of a nested loop and we
      // kill it.
      for (goto_programt::targetst::iterator target = t->targets.begin();
           target != t->targets.end();
           ++target) {
        if ((*target)->location_number > t->location_number) {
          // A forward jump...
          if (loop.find(*target) != loop.end()) {
            // Case 1: a forward jump within the loop.  Do nothing.
            continue;
          } else {
            // Case 2: a forward jump out of the loop.  Kill.
            fixedt->targets.clear();
            fixedt->targets.push_back(kill);
          }
        } else {
          // A backwards jump...
          if (*target == loop_header) {
            // Case 3: a backwards jump to the loop header.  Redirect to sentinel.
            fixedt->targets.clear();
            fixedt->targets.push_back(end);
          } else {
            // Case 4: a nested loop.  Kill.
            fixedt->targets.clear();
            fixedt->targets.push_back(kill);
          }
        }
      }
    }
  }

  // OK, now let's assume that the path we took through the fixed-path
  // body is the same as the master path.  We do this by assuming that
  // each of the shadow-distinguisher variables is equal to its corresponding
  // master-distinguisher.
  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    exprt &shadow = shadow_distinguishers[*it];

    fixed.insert_after(end)->make_assumption(equal_exprt(*it, shadow));
  }

  // Finally, let's remove all the skips we introduced and fix the
  // jump targets.
  fixed.update();
  remove_skip(fixed);
}

void sat_path_enumeratort::record_path(scratch_programt &program) {
  distinguish_valuest path_val;

  for (list<exprt>::iterator it = distinguishers.begin();
       it != distinguishers.end();
       ++it) {
    path_val[*it] = program.eval(*it).is_true();
  }

  accelerated_paths.push_back(path_val);
}
