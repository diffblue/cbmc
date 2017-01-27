/*******************************************************************\

Module: Compute natural loops in a goto_function

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

#ifndef CPROVER_ANALYSES_NATURAL_LOOPS_H
#define CPROVER_ANALYSES_NATURAL_LOOPS_H

#include <stack>
#include <iosfwd>
#include <set>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

#include "cfg_dominators.h"

template<class P, class T>
class natural_loops_templatet
{
public:
  typedef std::set<T> natural_loopt;

  // map loop headers to loops
  typedef std::map<T, natural_loopt> loop_mapt;

  loop_mapt loop_map;

  void operator()(P &program)
  {
    compute(program);
  }

  void output(std::ostream &) const;

  const cfg_dominators_templatet<P, T, false> &get_dominator_info() const
  {
    return cfg_dominators;
  }

  natural_loops_templatet()
  {
  }

  explicit natural_loops_templatet(P &program)
  {
    compute(program);
  }

protected:
  cfg_dominators_templatet<P, T, false> cfg_dominators;
  typedef typename cfg_dominators_templatet<P, T, false>::cfgt::nodet nodet;

  void compute(P &program);
  void compute_natural_loop(T, T);
};

class natural_loopst:
    public natural_loops_templatet<const goto_programt,
                                   goto_programt::const_targett>
{
};

typedef natural_loops_templatet<goto_programt, goto_programt::targett>
    natural_loops_mutablet;

void show_natural_loops(const goto_functionst &goto_functions);

/*******************************************************************\

Function: natural_loops_templatet::compute

  Inputs:

 Outputs:

 Purpose: Finds all back-edges and computes the natural loops

\*******************************************************************/

// #define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

template<class P, class T>
void natural_loops_templatet<P, T>::compute(P &program)
{
  cfg_dominators(program);

#ifdef DEBUG
  cfg_dominators.output(std::cout);
#endif

  // find back-edges m->n
  for(T m_it=program.instructions.begin();
      m_it!=program.instructions.end();
      ++m_it)
  {
    if(m_it->is_backwards_goto())
    {
      for(const auto &target : m_it->targets)
      {
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
          {
            compute_natural_loop(m_it, target);
          }
        }
      }
    }
  }
}

/*******************************************************************\

Function: natural_loops_templatet::compute_natural_loop

  Inputs:

 Outputs:

 Purpose: Computes the natural loop for a given back-edge
          (see Muchnick section 7.4)

\*******************************************************************/

template<class P, class T>
void natural_loops_templatet<P, T>::compute_natural_loop(T m, T n)
{
  assert(n->location_number<=m->location_number);

  std::stack<T> stack;

  natural_loopt &loop=loop_map[n];

  loop.insert(n);
  loop.insert(m);

  if(n!=m)
    stack.push(m);

  while(!stack.empty())
  {
    T p=stack.top();
    stack.pop();

    const nodet &node=
      cfg_dominators.cfg[cfg_dominators.cfg.entry_map[p]];

    for(const auto &edge : node.in)
    {
      T q=cfg_dominators.cfg[edge.first].PC;
      std::pair<typename natural_loopt::const_iterator, bool> result=
          loop.insert(q);
      if(result.second)
        stack.push(q);
    }
  }
}

/*******************************************************************\

Function: natural_loops_templatet::output

  Inputs:

 Outputs:

 Purpose: Print all natural loops that were found

\*******************************************************************/

template<class P, class T>
void natural_loops_templatet<P, T>::output(std::ostream &out) const
{
  for(const auto &loop : loop_map)
  {
    unsigned n=loop.first->location_number;

    out << n << " is head of { ";
    for(typename natural_loopt::const_iterator l_it=loop.second.begin();
        l_it!=loop.second.end(); ++l_it)
    {
      if(l_it!=loop.second.begin())
        out << ", ";
      out << (*l_it)->location_number;
    }
    out << " }\n";
  }
}

#endif // CPROVER_ANALYSES_NATURAL_LOOPS_H
