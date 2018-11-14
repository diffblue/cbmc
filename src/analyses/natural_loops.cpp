/*******************************************************************\

Module: Dominators

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Dominators

#include "natural_loops.h"

#ifdef DEBUG
#include <iostream>
#endif

/// Finds all back-edges and computes the natural
std::map<goto_programt::const_targett, std::set<goto_programt::const_targett>>
natural_loops_baset::compute(const goto_programt &program)
{
  std::map<targett, std::set<targett>> result;

  cfg_dominators(program);

#ifdef DEBUG
  cfg_dominators.output(std::cout);
#endif

  // find back-edges m->n
  for(auto m_it=program.instructions.begin();
      m_it!=program.instructions.end();
      ++m_it)
  {
    if(m_it->is_backwards_goto())
    {
      const auto &target=m_it->get_target();

      if(target->location_number<=m_it->location_number)
      {
        const nodet &node=
          cfg_dominators.cfg[cfg_dominators.cfg.entry_map[m_it]];

        #ifdef DEBUG
        std::cout << "Computing loop for "
                  << m_it->location_number << " -> "
                  << target->location_number << "\n";
        #endif

        if(node.dominators.find(target)!=node.dominators.end())
          result[target] = compute_natural_loop(m_it, target);
      }
    }
  }

  return result;
}

/// Computes the natural loop for a given back-edge (see Muchnick section 7.4)

std::set<goto_programt::const_targett>
natural_loops_baset::compute_natural_loop(targett m, targett n)
{
  assert(n->location_number<=m->location_number);

  std::stack<targett> stack;

  std::set<targett> loop;

  loop.insert(n);
  loop.insert(m);

  if(n!=m)
    stack.push(m);

  while(!stack.empty())
  {
    targett p=stack.top();
    stack.pop();

    const nodet &node=
      cfg_dominators.cfg[cfg_dominators.cfg.entry_map[p]];

    for(const auto &edge : node.in)
    {
      targett q = cfg_dominators.cfg[edge.first].PC;
      auto result = loop.insert(q);
      if(result.second)
        stack.push(q);
    }
  }

  return loop;
}

void show_natural_loops(
  const goto_modelt &goto_model,
  std::ostream &out)
{
  forall_goto_functions(it, goto_model.goto_functions)
  {
    out << "*** " << it->first << '\n';

    natural_loopst natural_loops;
    natural_loops(it->second.body);
    natural_loops.output(out);

    out << '\n';
  }
}
