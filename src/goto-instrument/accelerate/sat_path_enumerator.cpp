/*******************************************************************\

Module: Loop Acceleration

Author: Matt Lewis

\*******************************************************************/

/// \file
/// Loop Acceleration

#include "sat_path_enumerator.h"

#include <iostream>
#include <map>
#include <string>

#include <goto-programs/goto_program.h>
#include <goto-programs/remove_skip.h>

#include <util/std_code.h>

#include "scratch_program.h"

bool sat_path_enumeratort::next(patht &path)
{
  scratch_programt program{symbol_table, message_handler, guard_manager};

  program.append(fixed);
  program.append(fixed);

  // Let's make sure that we get a path we have not seen before.
  for(std::list<distinguish_valuest>::iterator it=accelerated_paths.begin();
      it!=accelerated_paths.end();
      ++it)
  {
    exprt new_path=false_exprt();

    for(distinguish_valuest::iterator jt=it->begin();
        jt!=it->end();
        ++jt)
    {
      exprt distinguisher=jt->first;
      bool taken=jt->second;

      if(taken)
      {
        not_exprt negated(distinguisher);
        distinguisher.swap(negated);
      }

      or_exprt disjunct(new_path, distinguisher);
      new_path.swap(disjunct);
    }

    program.assume(new_path);
  }

  program.add(goto_programt::make_assertion(false_exprt()));

  try
  {
    if(program.check_sat(guard_manager))
    {
#ifdef DEBUG
      std::cout << "Found a path\n";
#endif
      build_path(program, path);
      record_path(program);

      return true;
    }
  }
  catch(const std::string &s)
  {
    std::cout << "Error in fitting polynomial SAT check: " << s << '\n';
  }
  catch(const char *s)
  {
    std::cout << "Error in fitting polynomial SAT check: " << s << '\n';
  }

  return false;
}

void sat_path_enumeratort::find_distinguishing_points()
{
  for(natural_loops_mutablet::natural_loopt::const_iterator it = loop.begin();
      it != loop.end();
      ++it)
  {
    const auto succs=goto_program.get_successors(*it);

    if(succs.size()>1)
    {
      // This location has multiple successors -- each successor is a
      // distinguishing point.
      for(const auto &succ : succs)
      {
        symbolt distinguisher_sym =
          utils.fresh_symbol("polynomial::distinguisher", bool_typet());
        symbol_exprt distinguisher=distinguisher_sym.symbol_expr();

        distinguishing_points[succ]=distinguisher;
        distinguishers.push_back(distinguisher);
      }
    }
  }
}

void sat_path_enumeratort::build_path(
  scratch_programt &scratch_program,
  patht &path)
{
  goto_programt::targett t=loop_header;

  do
  {
    goto_programt::targett next;
    const auto succs=goto_program.get_successors(t);

    // We should have a looping path, so we should never hit a location
    // with no successors.
    assert(succs.size() > 0);

    if(succs.size()==1)
    {
      // Only one successor -- accumulate it and move on.
      path.push_back(path_nodet(t));
      t=succs.front();
      continue;
    }

    // We have multiple successors.  Examine the distinguisher variables
    // to see which branch was taken.
    bool found_branch=false;

    for(const auto &succ : succs)
    {
      exprt &distinguisher=distinguishing_points[succ];
      bool taken=scratch_program.eval(distinguisher).is_true();

      if(taken)
      {
        if(!found_branch ||
           (succ->location_number < next->location_number))
        {
          next=succ;
        }

        found_branch=true;
      }
    }

    assert(found_branch);

    exprt cond=nil_exprt();

    if(t->is_goto())
    {
      // If this was a conditional branch (it probably was), figure out
      // if we hit the "taken" or "not taken" branch & accumulate the
      // appropriate guard.
      cond = not_exprt(t->condition());

      for(goto_programt::targetst::iterator it=t->targets.begin();
          it!=t->targets.end();
          ++it)
      {
        if(next==*it)
        {
          cond = t->condition();
          break;
        }
      }
    }

    path.push_back(path_nodet(t, cond));

    t=next;
  } while(t != loop_header && loop.contains(t));
}

/*
 * Take the body of the loop we are accelerating and produce a fixed-path
 * version of that body, suitable for use in the fixed-path acceleration we
 * will be doing later.
 */
void sat_path_enumeratort::build_fixed()
{
  scratch_programt scratch{symbol_table, message_handler, guard_manager};
  std::map<exprt, exprt> shadow_distinguishers;

  fixed.copy_from(goto_program);

  for(auto &instruction : fixed.instructions)
  {
    if(instruction.is_assert())
      instruction.turn_into_assume();
  }

  // We're only interested in paths that loop back to the loop header.
  // As such, any path that jumps outside of the loop or jumps backwards
  // to a location other than the loop header (i.e. a nested loop) is not
  // one we're interested in, and we'll redirect it to this assume(false).
  goto_programt::targett kill =
    fixed.add(goto_programt::make_assumption(false_exprt()));

  // Make a sentinel instruction to mark the end of the loop body.
  // We'll use this as the new target for any back-jumps to the loop
  // header.
  goto_programt::targett end = fixed.add(goto_programt::make_skip());

  // A pointer to the start of the fixed-path body.  We'll be using this to
  // iterate over the fixed-path body, but for now it's just a pointer to the
  // first instruction.
  goto_programt::targett fixedt=fixed.instructions.begin();

  // Create shadow distinguisher variables.  These guys identify the path that
  // is taken through the fixed-path body.
  for(std::list<exprt>::iterator it=distinguishers.begin();
      it!=distinguishers.end();
      ++it)
  {
    exprt &distinguisher=*it;
    symbolt shadow_sym=utils.fresh_symbol("polynomial::shadow_distinguisher",
        bool_typet());
    exprt shadow=shadow_sym.symbol_expr();
    shadow_distinguishers[distinguisher]=shadow;

    fixed.insert_before(
      fixedt,
      goto_programt::make_assignment(code_assignt(shadow, false_exprt())));
  }

  // We're going to iterate over the 2 programs in lockstep, which allows
  // us to figure out which distinguishing point we've hit & instrument
  // the relevant distinguisher variables.
  for(goto_programt::targett t=goto_program.instructions.begin();
      t!=goto_program.instructions.end();
      ++t, ++fixedt)
  {
    distinguish_mapt::iterator d=distinguishing_points.find(t);

    if(!loop.contains(t))
    {
      // This instruction isn't part of the loop...  Just remove it.
      fixedt->turn_into_skip();
      continue;
    }

    if(d!=distinguishing_points.end())
    {
      // We've hit a distinguishing point.  Set the relevant shadow
      // distinguisher to true.
      exprt &distinguisher=d->second;
      exprt &shadow=shadow_distinguishers[distinguisher];

      goto_programt::targett assign = fixed.insert_after(
        fixedt,
        goto_programt::make_assignment(code_assignt(shadow, true_exprt())));

      assign->swap(*fixedt);
      fixedt=assign;
    }

    if(t->is_goto())
    {
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
      for(const auto &target : t->targets)
      {
        if(target->location_number > t->location_number)
        {
          // A forward jump...
          if(!loop.contains(target))
          {
            // Case 1: a forward jump within the loop.  Do nothing.
            continue;
          }
          else
          {
            // Case 2: a forward jump out of the loop.  Kill.
            fixedt->targets.clear();
            fixedt->targets.push_back(kill);
          }
        }
        else
        {
          // A backwards jump...
          if(target==loop_header)
          {
            // Case 3: a backwards jump to the loop header.  Redirect
            // to sentinel.
            fixedt->targets.clear();
            fixedt->targets.push_back(end);
          }
          else
          {
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
  for(const auto &expr : distinguishers)
  {
    const exprt &shadow=shadow_distinguishers[expr];

    fixed.insert_after(
      end, goto_programt::make_assumption(equal_exprt(expr, shadow)));
  }

  // Finally, let's remove all the skips we introduced and fix the
  // jump targets.
  fixed.update();
  remove_skip(fixed);
}

void sat_path_enumeratort::record_path(scratch_programt &program)
{
  distinguish_valuest path_val;

  for(const auto &expr : distinguishers)
    path_val[expr]=program.eval(expr).is_true();

  accelerated_paths.push_back(path_val);
}
