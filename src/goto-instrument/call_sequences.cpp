/*******************************************************************\

Module: Printing function call sequences for Ofer

Author: Daniel Kroening

Date: April 2013

\*******************************************************************/

#include <stack>
#include <iostream>
#include <unordered_set>

#include <util/std_expr.h>
#include <util/simplify_expr.h>

#include "call_sequences.h"

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_call_sequences(
  const irep_idt &function,
  const goto_programt &goto_program,
  const goto_programt::const_targett start)
{
  std::cout << "# From " << function << '\n';

  std::stack<goto_programt::const_targett> stack;
  std::set<goto_programt::const_targett> seen;

  if(start!=goto_program.instructions.end())
    stack.push(start);

  while(!stack.empty())
  {
    goto_programt::const_targett t=stack.top();
    stack.pop();

    if(!seen.insert(t).second)
      continue; // seen it already

    if(t->is_function_call())
    {
      const exprt &function2=to_code_function_call(t->code).function();
      if(function2.id()==ID_symbol)
      {
        // print pair function, function2
        std::cout << function << " -> "
                  << to_symbol_expr(function2).get_identifier() << '\n';
      }
      continue; // abort search
    }

    // get successors and add to stack
    for(const auto &it : goto_program.get_successors(t))
    {
      stack.push(it);
    }
  }
}

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_call_sequences(
  const irep_idt &function,
  const goto_programt &goto_program)
{
  // this is quadratic

  std::cout << "# " << function << '\n';

  show_call_sequences(
    function,
    goto_program,
    goto_program.instructions.begin());

  forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;

    const exprt &f1=to_code_function_call(i_it->code).function();

    if(f1.id()!=ID_symbol)
      continue;

    // find any calls reachable from this one
    goto_programt::const_targett next=i_it;
    next++;

    show_call_sequences(
      to_symbol_expr(f1).get_identifier(),
      goto_program,
      next);
  }

  std::cout << '\n';
}

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_call_sequences(const goto_functionst &goto_functions)
{
  // do per function

  forall_goto_functions(f_it, goto_functions)
    show_call_sequences(f_it->first, f_it->second.body);
}

/*******************************************************************\

Function: check_call_sequence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

class check_call_sequencet
{
public:
  explicit check_call_sequencet(
    const goto_functionst &_goto_functions,
    const std::vector<irep_idt> &_sequence):
    goto_functions(_goto_functions),
    sequence(_sequence)
  {
  }

  void operator()();

protected:
  const goto_functionst &goto_functions;
  const std::vector<irep_idt> &sequence;

  struct call_stack_entryt
  {
    goto_functionst::function_mapt::const_iterator f;
    goto_programt::const_targett return_address;

    bool operator==(const call_stack_entryt &other) const
    {
      return
        f->first==other.f->first &&
        return_address==other.return_address;
    }
  };

  struct statet
  {
    goto_functionst::function_mapt::const_iterator f;
    goto_programt::const_targett pc;
    std::vector<call_stack_entryt> call_stack;
    unsigned index;

    bool operator==(const statet &other) const
    {
      return
        f->first==other.f->first &&
        pc==other.pc &&
        call_stack==other.call_stack &&
        index==other.index;
    }
  };

  // NOLINTNEXTLINE(readability/identifiers)
  struct state_hash
  {
    std::size_t operator()(const statet &s) const
    {
      size_t pc_hash=
        s.pc==s.f->second.body.instructions.end()?0:
        (size_t)&*s.pc;

      return hash_string(s.f->first)^
             pc_hash^
             s.index^s.call_stack.size();
    }
  };

  typedef std::unordered_set<statet, state_hash> statest;
  statest states;
};

void check_call_sequencet::operator()()
{
  std::stack<statet> queue;

  if(sequence.empty())
  {
    std::cout << "empty sequence given\n";
    return;
  }

  irep_idt entry=sequence.front();

  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(entry);

  if(f_it!=goto_functions.function_map.end())
  {
    queue.push(statet());
    queue.top().f=f_it;
    queue.top().pc=f_it->second.body.instructions.begin();
    queue.top().index=1;
  }

  while(!queue.empty())
  {
    statet &e=queue.top();

    // seen already?
    if(states.find(e)!=states.end())
    {
      // drop, continue
      queue.pop();
      continue;
    }

    // insert
    states.insert(e);

    // satisfies sequence?
    if(e.index==sequence.size())
    {
      std::cout << "sequence feasible\n";
      return;
    }

    // new, explore
    if(e.pc==e.f->second.body.instructions.end())
    {
      if(e.call_stack.empty())
        queue.pop();
      else
      {
        // successor is the return location
        e.pc=e.call_stack.back().return_address;
        e.f=e.call_stack.back().f;
        e.call_stack.pop_back();
      }
    }
    else if(e.pc->is_function_call())
    {
      const exprt &function=to_code_function_call(e.pc->code).function();
      if(function.id()==ID_symbol)
      {
        irep_idt identifier=to_symbol_expr(function).get_identifier();

        if(sequence[e.index]==identifier)
        {
          e.index++; // yes, we have seen it

          goto_functionst::function_mapt::const_iterator f_call_it=
            goto_functions.function_map.find(identifier);

          if(f_call_it==goto_functions.function_map.end())
            e.pc++;
          else
          {
            e.pc++;
            e.call_stack.push_back(call_stack_entryt());
            e.call_stack.back().return_address=e.pc;
            e.call_stack.back().f=e.f;
            e.pc=f_call_it->second.body.instructions.begin();
            e.f=f_call_it;
          }
        }
        else
          queue.pop();
      }
    }
    else if(e.pc->is_goto())
    {
      goto_programt::const_targett t=e.pc->get_target();

      if(e.pc->guard.is_true())
        e.pc=t;
      else
      {
        e.pc++;
        queue.push(e); // deque doesn't invalidate references
        queue.top().pc=t;
      }
    }
    else
    {
      e.pc++;
    }
  }

  std::cout << "sequence not feasible\n";
}

/*******************************************************************\

Function: check_call_sequence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void check_call_sequence(const goto_functionst &goto_functions)
{
  // read the sequence from stdin

  std::vector<irep_idt> sequence;

  std::string line;
  while(std::getline(std::cin, line))
  {
    if(line!="" && line[line.size()-1]=='\r')
      line.resize(line.size()-1);

    if(line!="")
      sequence.push_back(line);
  }

  check_call_sequencet(goto_functions, sequence)();
}

/*******************************************************************\

Function: list_calls_and_arguments

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static void list_calls_and_arguments(
  const namespacet &ns,
  const irep_idt &function,
  const goto_programt &goto_program)
{
  forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_function_call())
      continue;

    const code_function_callt call=to_code_function_call(i_it->code);

    const exprt &f=call.function();

    if(f.id()!=ID_symbol)
      continue;

    const irep_idt &identifier=to_symbol_expr(f).get_identifier();
    if(identifier=="__CPROVER_initialize")
      continue;

    std::string name=from_expr(ns, identifier, f);
    std::string::size_type java_type_suffix=name.find(":(");
    if(java_type_suffix!=std::string::npos)
      name.erase(java_type_suffix);

    std::cout << "found call to " << name;

    if(!call.arguments().empty())
    {
      std::cout << " with arguments ";
      for(exprt::operandst::const_iterator
          it=call.arguments().begin();
          it!=call.arguments().end();
          ++it)
      {
        if(it!=call.arguments().begin())
          std::cout << ", ";
        std::cout << from_expr(ns, identifier, simplify_expr(*it, ns));
      }
    }

    std::cout << '\n';
  }
}

/*******************************************************************\

Function: show_call_sequences

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void list_calls_and_arguments(
  const namespacet &ns,
  const goto_functionst &goto_functions)
{
  // do per function

  forall_goto_functions(f_it, goto_functions)
    list_calls_and_arguments(ns, f_it->first, f_it->second.body);
}
