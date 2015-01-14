/*******************************************************************\

Module: Symbolic Execution

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <cassert>

#include <util/std_expr.h>
#include <util/rename.h>
#include <util/symbol_table.h>
#include <util/replace_symbol.h>
#include <util/string2int.h>

#include "goto_symex.h"

/*******************************************************************\

Function: goto_symext::new_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::new_name(symbolt &symbol)
{
  get_new_name(symbol, ns);
  new_symbol_table.add(symbol);
}

/*******************************************************************\

Function: goto_symext::claim

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::claim(
  const exprt &claim_expr,
  const std::string &msg,
  statet &state)
{
  total_claims++;

  exprt expr=claim_expr;

  // we are willing to re-write some quantified expressions
  rewrite_quantifiers(expr, state);

  // now rename, enables propagation    
  state.rename(expr, ns);
  
  // now try simplifier on it
  do_simplify(expr);

  if(expr.is_true()) return;
  
  state.guard.guard_expr(expr);
  
  remaining_claims++;
  target.assertion(state.guard.as_expr(), expr, msg, state.source);
}

/*******************************************************************\

Function: goto_symext::symex_assume

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::symex_assume(statet &state, const exprt &cond)
{
  exprt simplified_cond=cond;

  do_simplify(simplified_cond);

  if(simplified_cond.is_true()) return;

  // not clear why different treatment for threads vs. no threads
  // is essential
  if(state.threads.size()==1)
  {
    exprt tmp=simplified_cond;
    state.guard.guard_expr(tmp);
    target.assumption(state.guard.as_expr(), tmp, state.source);
  }
  else
    state.guard.add(simplified_cond);

  if(state.atomic_section_id!=0 &&
     state.guard.is_false())
    symex_atomic_end(state);
}

/*******************************************************************\

Function: goto_symext::rewrite_quantifiers

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void goto_symext::rewrite_quantifiers(exprt &expr, statet &state)
{
  if(expr.id()==ID_forall)
  {
    // forall X. P -> P
    // we keep the quantified variable unique by means of L2 renaming
    assert(expr.operands().size()==2);
    assert(expr.op0().id()==ID_symbol);
    irep_idt identifier=to_symbol_expr(expr.op0()).get_identifier();
    state.level2.increase_counter(state.level1(identifier));
    exprt tmp=expr.op1();
    expr.swap(tmp);
  }
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose: symex from given state

\*******************************************************************/

void goto_symext::operator()(
  statet &state,
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  assert(!goto_program.instructions.empty());

  state.source=symex_targett::sourcet(goto_program);
  assert(!state.threads.empty());
  assert(!state.call_stack().empty());
  state.top().end_of_function=--goto_program.instructions.end();
  state.top().calling_location.pc=state.top().end_of_function;
  state.symex_target=&target;
  
  assert(state.top().end_of_function->is_end_function());

  const std::string cex_file=options.get_option("verify-cex");
  if(!cex_file.empty())
  {
    unsigned entry_node=0;
    if(read_graphml(cex_file, cex_graph, entry_node))
      throw "Failed to parse counterexample graph "+cex_file;

    state.cex_graph_nodes.insert(entry_node);

    forall_goto_functions(f_it, goto_functions)
    {
      if(!f_it->second.body_available) continue;

      unsigned lb=0;
      forall_goto_program_instructions(i_it, f_it->second.body)
      {
        irep_idt line_no=i_it->source_location.get_line();
        if(line_no.empty()) continue;

        unsigned cur=safe_string2unsigned(id2string(line_no));

        if(lb==0 || lb>cur) lb=cur>5 ? cur-5 : cur;

        goto_programt::const_targett next=i_it;
        ++next;
        unsigned ub=cur;
        if(next!=f_it->second.body.instructions.end() &&
           !next->source_location.get_line().empty())
        {
          irep_idt next_line_no=next->source_location.get_line();
          ub=safe_string2unsigned(id2string(next_line_no));
          --ub;
          if(ub<cur) ub=cur;
        }

        token_map[i_it->location_number]=std::make_pair(lb, ub);

        lb=cur+1;
      }
    }
  }

  while(!state.call_stack().empty())
  {
    symex_step(goto_functions, state);
    
    // is there another thread to execute?
    if(state.call_stack().empty() &&
       state.source.thread_nr+1<state.threads.size())
    {
      unsigned t=state.source.thread_nr+1;
      //std::cout << "********* Now executing thread " << t << std::endl;
      state.switch_to_thread(t);
    }
  }
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose: symex starting from given program

\*******************************************************************/

void goto_symext::operator()(
  const goto_functionst &goto_functions,
  const goto_programt &goto_program)
{
  statet state;
  operator() (state, goto_functions, goto_program);
}

/*******************************************************************\

Function: goto_symext::operator()

  Inputs:

 Outputs:

 Purpose: symex from entry point

\*******************************************************************/

void goto_symext::operator()(const goto_functionst &goto_functions)
{
  goto_functionst::function_mapt::const_iterator it=
    goto_functions.function_map.find(ID_main);

  if(it==goto_functions.function_map.end())
    throw "main symbol not found; please set an entry point";

  const goto_programt &body=it->second.body;

  operator()(goto_functions, body);
}

/*******************************************************************\

Function: goto_symext::symex_step

  Inputs:

 Outputs:

 Purpose: do just one step

\*******************************************************************/

void goto_symext::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  #if 0
  std::cout << "\ninstruction type is " << state.source.pc->type << std::endl;
  std::cout << "Location: " << state.source.pc->location << std::endl;
  std::cout << "Guard: " << from_expr(ns, "", state.guard.as_expr()) << std::endl;
  std::cout << "Code: " << from_expr(ns, "", state.source.pc->code) << std::endl;
  #endif

  assert(!state.threads.empty());
  assert(!state.call_stack().empty());

  const goto_programt::instructiont &instruction=*state.source.pc;

  merge_gotos(state);

  // depth exceeded?
  {
    unsigned max_depth=options.get_unsigned_int_option("depth");
    if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
    state.depth++;
  }

  if(cex_graph.size()!=0 &&
     !state.guard.is_false())
  {
    // simulate epsilon transitions
    std::list<unsigned> worklist;
    for(std::set<unsigned>::const_iterator
        it=state.cex_graph_nodes.begin();
        it!=state.cex_graph_nodes.end();
        ++it)
      worklist.push_back(*it);

    while(!worklist.empty())
    {
      const unsigned n=worklist.back();
      worklist.pop_back();

      const graphmlt::nodet &node=cex_graph[n];

      for(graphmlt::edgest::const_iterator
          it=node.out.begin();
          it!=node.out.end();
          ++it)
      {
        const xmlt &xml_node=it->second.xml_node;
        bool has_epsilon=true;
        for(xmlt::elementst::const_iterator
            x_it=xml_node.elements.begin();
            has_epsilon && x_it!=xml_node.elements.end();
            ++x_it)
        {
          if(x_it->get_attribute("key")=="tokens")
            has_epsilon=x_it->data.empty();
        }

        if(has_epsilon &&
           state.cex_graph_nodes.insert(it->first).second)
          worklist.push_back(it->first);
      }
    }

    std::map<unsigned, std::pair<unsigned, unsigned> >::const_iterator
      t_m_it=token_map.end();
    if(state.source.pc->source_location.get_file()!="<built-in-additions>")
      t_m_it=token_map.find(state.source.pc->location_number);
#if 0
    if(t_m_it!=token_map.end())
      std::cerr << "Token range: [" << t_m_it->second.first
        << ":" << t_m_it->second.second << "]" << std::endl;
    std::cerr << "# nodes: " << state.cex_graph_nodes.size() << std::endl;
#endif

    std::set<unsigned> before;
    if(t_m_it!=token_map.end()) before.swap(state.cex_graph_nodes);

    // greedily make transitions
    for(std::set<unsigned>::const_iterator
        it=before.begin();
        it!=before.end();
        ++it)
    {
      const graphmlt::nodet &node=cex_graph[*it];
#if 0
      std::cerr << "Testing node " << node.node_name << std::endl;
#endif

      bool taken=false;
      for(graphmlt::edgest::const_iterator
          e_it=node.out.begin();
          e_it!=node.out.end() && !taken;
          ++e_it)
      {
        const xmlt &xml_node=e_it->second.xml_node;
        for(xmlt::elementst::const_iterator
            x_it=xml_node.elements.begin();
            x_it!=xml_node.elements.end();
            ++x_it)
        {
          if(x_it->get_attribute("key")!="tokens") continue;

          std::string data=x_it->data;
          while(!data.empty())
          {
            std::string::size_type c=data.find(',');
            const unsigned t=safe_string2unsigned(data.substr(0, c));

            if(t_m_it->second.first<=t && t<=t_m_it->second.second)
            {
              state.cex_graph_nodes.insert(e_it->first);
              taken=true;
#if 0
              std::cerr << "Transition " << *it << " --> " << e_it->first << std::endl;
              std::cerr << e_it->second.xml_node;
#endif
            }

            if(c==std::string::npos)
              break;

            data.erase(0, c+1);
          }
        }
      }

      if(!taken)
        state.cex_graph_nodes.insert(*it);
    }

    // see whether we have only sink nodes left
    bool all_sinks=!before.empty();
    for(std::set<unsigned>::const_iterator
        it=before.begin();
        it!=before.end() && all_sinks;
        ++it)
    {
      const graphmlt::nodet &node=cex_graph[*it];

      all_sinks=node.is_violation;
    }

    if(all_sinks)
      state.guard.add(false_exprt());
  }

  // actually do instruction
  switch(instruction.type)
  {
  case SKIP:
    // really ignore
    state.source.pc++;
    break;

  case END_FUNCTION:
    // do even if state.guard.is_false() to clear out frame created
    // in symex_start_thread
    symex_end_of_function(state);
    state.source.pc++;
    break;
  
  case LOCATION:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    state.source.pc++;
    break;
  
  case GOTO:
    symex_goto(state);
    break;
    
  case ASSUME:
    if(!state.guard.is_false())
    {
      exprt tmp=instruction.guard;
      clean_expr(tmp, state, false);
      state.rename(tmp, ns);
      symex_assume(state, tmp);
    }

    state.source.pc++;
    break;

  case ASSERT:
    if(!state.guard.is_false())
    {
      std::string msg=id2string(state.source.pc->source_location.get_comment());
      if(msg=="") msg="assertion";
      exprt tmp(instruction.guard);
      clean_expr(tmp, state, false);
      claim(tmp, msg, state);
    }

    state.source.pc++;
    break;
    
  case RETURN:
    if(!state.guard.is_false())
      symex_return(state);

    state.source.pc++;
    break;

  case ASSIGN:
    if(!state.guard.is_false())
    {
      code_assignt deref_code=to_code_assign(instruction.code);

      clean_expr(deref_code.lhs(), state, true);
      clean_expr(deref_code.rhs(), state, false);

      symex_assign(state, deref_code);
    }

    state.source.pc++;
    break;

  case FUNCTION_CALL:
    if(!state.guard.is_false())
    {
      code_function_callt deref_code=
        to_code_function_call(instruction.code);

      if(deref_code.lhs().is_not_nil())
        clean_expr(deref_code.lhs(), state, true);

      clean_expr(deref_code.function(), state, false);

      Forall_expr(it, deref_code.arguments())
        clean_expr(*it, state, false);
    
      symex_function_call(goto_functions, state, deref_code);
    }
    else
      state.source.pc++;
    break;

  case OTHER:
    if(!state.guard.is_false())
      symex_other(goto_functions, state);

    state.source.pc++;
    break;

  case DECL:
    if(!state.guard.is_false())
      symex_decl(state);

    state.source.pc++;
    break;

  case DEAD:
    symex_dead(state);
    state.source.pc++;
    break;

  case START_THREAD:
    symex_start_thread(state);
    state.source.pc++;
    break;
  
  case END_THREAD:
    // behaves like assume(0);
    if(!state.guard.is_false())
      state.guard.add(false_exprt());
    state.source.pc++;
    break;
  
  case ATOMIC_BEGIN:
    symex_atomic_begin(state);
    state.source.pc++;
    break;
    
  case ATOMIC_END:
    symex_atomic_end(state);
    state.source.pc++;
    break;
    
  case CATCH:
    symex_catch(state);
    state.source.pc++;
    break;
  
  case THROW:
    symex_throw(state);
    state.source.pc++;
    break;
    
  case NO_INSTRUCTION_TYPE:
    throw "symex got NO_INSTRUCTION";
  
  default:
    throw "symex got unexpected instruction";
  }
}
