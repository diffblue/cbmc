/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include "remove_skip.h"
#include "goto_model.h"

/// Determine whether the instruction is semantically equivalent to a skip
/// (no-op).  This includes a skip, but also if(false) goto ..., goto next;
///  next: ..., and (void)0.
/// \param body: goto program containing the instruction
/// \param it: instruction iterator that is tested for being a skip (or
///   equivalent)
/// \param ignore_labels: If the caller takes care of moving labels, then even
///   skip statements carrying labels can be treated as skips (even though they
///   may carry key information such as error labels).
/// \return True, iff it is equivalent to a skip.
bool is_skip(
  const goto_programt &body,
  goto_programt::const_targett it,
  bool ignore_labels)
{
  if(!ignore_labels && !it->labels.empty())
    return false;

  if(it->is_skip())
    return !it->code.get_bool(ID_explicit);

  if(it->is_goto())
  {
    if(it->guard.is_false())
      return true;

    goto_programt::const_targett next_it = it;
    next_it++;

    if(next_it == body.instructions.end())
      return false;

    // A branch to the next instruction is a skip
    // We also require the guard to be 'true'
    return it->guard.is_true() &&
           it->get_target()==next_it;
  }

  if(it->is_other())
  {
    if(it->code.is_nil())
      return true;

    const irep_idt &statement=it->code.get_statement();

    if(statement==ID_skip)
      return true;
    else if(statement==ID_expression)
    {
      const code_expressiont &code_expression=to_code_expression(it->code);
      const exprt &expr=code_expression.expression();
      if(expr.id()==ID_typecast &&
         expr.type().id()==ID_empty &&
         to_typecast_expr(expr).op().is_constant())
      {
        // something like (void)0
        return true;
      }
    }

    return false;
  }

  return false;
}

/// remove unnecessary skip statements
/// \param goto_program: goto program containing the instructions to be cleaned
///   in the range [begin, end)
/// \param begin: iterator pointing to first instruction to be considered
/// \param end: iterator pointing beyond last instruction to be considered
void remove_skip(
  goto_programt &goto_program,
  goto_programt::targett begin,
  goto_programt::targett end)
{
  // This needs to be a fixed-point, as
  // removing a skip can turn a goto into a skip.
  std::size_t old_size;

  do
  {
    old_size=goto_program.instructions.size();

    // maps deleted instructions to their replacement
    typedef std::map<goto_programt::targett, goto_programt::targett>
      new_targetst;
    new_targetst new_targets;

    // remove skip statements

    for(goto_programt::instructionst::iterator it = begin; it != end;)
    {
      goto_programt::targett old_target=it;

      // for collecting labels
      std::list<irep_idt> labels;

      while(is_skip(goto_program, it, true))
      {
        // don't remove the last skip statement,
        // it could be a target
        if(
          it == std::prev(end) ||
          (std::next(it)->is_end_function() &&
           (!labels.empty() || !it->labels.empty())))
        {
          break;
        }

        // save labels
        labels.splice(labels.end(), it->labels);
        it++;
      }

      goto_programt::targett new_target=it;

      // save labels
      it->labels.splice(it->labels.begin(), labels);

      if(new_target!=old_target)
      {
        for(; old_target!=new_target; ++old_target)
          new_targets[old_target]=new_target; // remember the old targets
      }
      else
        it++;
    }

    // adjust gotos across the full goto program body
    for(auto &ins : goto_program.instructions)
    {
      if(ins.is_goto() || ins.is_start_thread() || ins.is_catch())
      {
        for(auto &target : ins.targets)
        {
          new_targetst::const_iterator result = new_targets.find(target);

          if(result!=new_targets.end())
            target = result->second;
        }
      }
    }

    while(new_targets.find(begin) != new_targets.end())
      ++begin;

    // now delete the skips -- we do so after adjusting the
    // gotos to avoid dangling targets
    for(const auto &new_target : new_targets)
      goto_program.instructions.erase(new_target.first);

    // remove the last skip statement unless it's a target
    goto_program.compute_target_numbers();

    if(begin != end)
    {
      goto_programt::targett last = std::prev(end);
      if(begin == last)
        ++begin;

      if(is_skip(goto_program, last) && !last->is_target())
        goto_program.instructions.erase(last);
    }
  }
  while(goto_program.instructions.size()<old_size);
}

/// remove unnecessary skip statements
void remove_skip(goto_programt &goto_program)
{
  remove_skip(
    goto_program,
    goto_program.instructions.begin(),
    goto_program.instructions.end());

  goto_program.update();
}

/// remove unnecessary skip statements
void remove_skip(goto_functionst &goto_functions)
{
  Forall_goto_functions(f_it, goto_functions)
    remove_skip(
      f_it->second.body,
      f_it->second.body.instructions.begin(),
      f_it->second.body.instructions.end());

  // we may remove targets
  goto_functions.update();
}

void remove_skip(goto_modelt &goto_model)
{
  remove_skip(goto_model.goto_functions);
}
