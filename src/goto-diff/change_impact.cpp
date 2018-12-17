/*******************************************************************\

Module: Data and control-dependencies of syntactic diff

Author: Michael Tautschnig

Date: April 2016

\*******************************************************************/

/// \file
/// Data and control-dependencies of syntactic diff

#include "change_impact.h"

#include <iostream>

#include <goto-programs/goto_model.h>

#include <analyses/dependence_graph.h>

#include "unified_diff.h"

#if 0
  struct cfg_nodet
  {
    cfg_nodet():node_required(false)
    {
    }

    bool node_required;
#ifdef DEBUG_FULL_SLICERT
    std::set<unsigned> required_by;
#endif
  };

  typedef cfg_baset<cfg_nodet> cfgt;
  cfgt cfg;

  typedef std::vector<cfgt::entryt> dep_node_to_cfgt;
  typedef std::stack<cfgt::entryt> queuet;

  inline void add_to_queue(
    queuet &queue,
    const cfgt::entryt &entry,
    goto_programt::const_targett reason)
  {
#ifdef DEBUG_FULL_SLICERT
    cfg[entry].required_by.insert(reason->location_number);
#endif
    queue.push(entry);
  }

void full_slicert::operator()(
  goto_functionst &goto_functions,
  const namespacet &ns,
  slicing_criteriont &criterion)
{
  // build the CFG data structure
  cfg(goto_functions);

  // fill queue with according to slicing criterion
  queuet queue;
  // gather all unconditional jumps as they may need to be included
  jumpst jumps;
  // declarations or dead instructions may be necessary as well
  decl_deadt decl_dead;

  for(cfgt::entry_mapt::iterator
      e_it=cfg.entry_map.begin();
      e_it!=cfg.entry_map.end();
      e_it++)
  {
    if(criterion(e_it->first))
      add_to_queue(queue, e_it->second, e_it->first);
    else if(implicit(e_it->first))
      add_to_queue(queue, e_it->second, e_it->first);
    else if((e_it->first->is_goto() && e_it->first->guard.is_true()) ||
            e_it->first->is_throw())
      jumps.push_back(e_it->second);
    else if(e_it->first->is_decl())
    {
      const auto &s=to_code_decl(e_it->first->code).symbol();
      decl_dead[s.get_identifier()].push(e_it->second);
    }
    else if(e_it->first->is_dead())
    {
      const auto &s=to_code_dead(e_it->first->code).symbol();
      decl_dead[s.get_identifier()].push(e_it->second);
    }
  }

  // compute program dependence graph (and post-dominators)
  dependence_grapht dep_graph(ns);
  dep_graph(goto_functions, ns);

  // compute the fixedpoint
  fixedpoint(goto_functions, queue, jumps, decl_dead, dep_graph);

  // now replace those instructions that are not needed
  // by skips

  Forall_goto_functions(f_it, goto_functions)
    if(f_it->second.body_available())
    {
      Forall_goto_program_instructions(i_it, f_it->second.body)
      {
        const cfgt::entryt &e=cfg.entry_map[i_it];
        if(!i_it->is_end_function() && // always retained
           !cfg[e].node_required)
          i_it->make_skip();
#ifdef DEBUG_FULL_SLICERT
        else
        {
          std::string c="ins:"+std::to_string(i_it->location_number);
          c+=" req by:";
          for(std::set<unsigned>::const_iterator
              req_it=cfg[e].required_by.begin();
              req_it!=cfg[e].required_by.end();
              ++req_it)
          {
            if(req_it!=cfg[e].required_by.begin())
              c+=",";
            c+=std::to_string(*req_it);
          }
          i_it->source_location.set_column(c);  // for show-goto-functions
          i_it->source_location.set_comment(c); // for dump-c
        }
#endif
      }
    }

  // remove the skips
  remove_skip(goto_functions);
}


void full_slicert::fixedpoint(
  goto_functionst &goto_functions,
  queuet &queue,
  jumpst &jumps,
  decl_deadt &decl_dead,
  const dependence_grapht &dep_graph)
{
  std::vector<cfgt::entryt> dep_node_to_cfg;
  dep_node_to_cfg.reserve(dep_graph.size());
  for(unsigned i=0; i<dep_graph.size(); ++i)
  {
    cfgt::entry_mapt::const_iterator entry=
      cfg.entry_map.find(dep_graph[i].PC);
    assert(entry!=cfg.entry_map.end());

    dep_node_to_cfg.push_back(entry->second);
  }

  // process queue until empty
  while(!queue.empty())
  {
    while(!queue.empty())
    {
      cfgt::entryt e=queue.top();
      cfgt::nodet &node=cfg[e];
      queue.pop();

      // already done by some earlier iteration?
      if(node.node_required)
        continue;

      // node is required
      node.node_required=true;

      // add data and control dependencies of node
      add_dependencies(node, queue, dep_graph, dep_node_to_cfg);

      // retain all calls of the containing function
      add_function_calls(node, queue, goto_functions);

      // find all the symbols it uses to add declarations
      add_decl_dead(node, queue, decl_dead);
    }

    // add any required jumps
    add_jumps(queue, jumps, dep_graph.cfg_post_dominators());
  }
}


void full_slicert::add_dependencies(
  const cfgt::nodet &node,
  queuet &queue,
  const dependence_grapht &dep_graph,
  const dep_node_to_cfgt &dep_node_to_cfg)
{
  const dependence_grapht::nodet &d_node=
    dep_graph[dep_graph[node.PC].get_node_id()];

  for(dependence_grapht::edgest::const_iterator
      it=d_node.in.begin();
      it!=d_node.in.end();
      ++it)
    add_to_queue(queue, dep_node_to_cfg[it->first], node.PC);
}
#endif

class change_impactt
{
public:
  change_impactt(
    const goto_modelt &model_old,
    const goto_modelt &model_new,
    impact_modet impact_mode,
    bool compact_output);

  void operator()();

protected:
  impact_modet impact_mode;
  bool compact_output;

  const goto_functionst &old_goto_functions;
  const namespacet ns_old;
  const goto_functionst &new_goto_functions;
  const namespacet ns_new;

  unified_difft unified_diff;

  dependence_grapht old_dep_graph;
  dependence_grapht new_dep_graph;

  enum mod_flagt
  {
    SAME=0,
    NEW=1<<0,
    DELETED=1<<1,
    NEW_DATA_DEP=1<<2,
    DEL_DATA_DEP=1<<3,
    NEW_CTRL_DEP=1<<4,
    DEL_CTRL_DEP=1<<5
  };

  typedef std::map<goto_programt::const_targett, unsigned>
    goto_program_change_impactt;
  typedef std::map<irep_idt, goto_program_change_impactt>
    goto_functions_change_impactt;

  goto_functions_change_impactt old_change_impact, new_change_impact;

  void change_impact(const irep_idt &function);

  void change_impact(
    const goto_programt &old_goto_program,
    const goto_programt &new_goto_program,
    const unified_difft::goto_program_difft &diff,
    goto_program_change_impactt &old_impact,
    goto_program_change_impactt &new_impact);

  void propogate_dep_back(
    const dependence_grapht::nodet &d_node,
    const dependence_grapht &dep_graph,
    goto_functions_change_impactt &change_impact,
    bool del);
  void propogate_dep_forward(
    const dependence_grapht::nodet &d_node,
    const dependence_grapht &dep_graph,
    goto_functions_change_impactt &change_impact,
    bool del);

  void output_change_impact(
    const irep_idt &function,
    const goto_program_change_impactt &c_i,
    const goto_functionst &goto_functions,
    const namespacet &ns) const;
  void output_change_impact(
    const irep_idt &function,
    const goto_program_change_impactt &o_c_i,
    const goto_functionst &o_goto_functions,
    const namespacet &o_ns,
    const goto_program_change_impactt &n_c_i,
    const goto_functionst &n_goto_functions,
    const namespacet &n_ns) const;

  void output_instruction(char prefix,
      const goto_programt &goto_program,
      const namespacet &ns,
      const irep_idt &function,
      goto_programt::const_targett &target) const;
};

change_impactt::change_impactt(
    const goto_modelt &model_old,
    const goto_modelt &model_new,
    impact_modet _impact_mode,
    bool _compact_output):
  impact_mode(_impact_mode),
  compact_output(_compact_output),
  old_goto_functions(model_old.goto_functions),
  ns_old(model_old.symbol_table),
  new_goto_functions(model_new.goto_functions),
  ns_new(model_new.symbol_table),
  unified_diff(model_old, model_new),
  old_dep_graph(ns_old),
  new_dep_graph(ns_new)
{
  // syntactic difference?
  if(!unified_diff())
    return;

  // compute program dependence graph of old code
  old_dep_graph(old_goto_functions, ns_old);

  // compute program dependence graph of new code
  new_dep_graph(new_goto_functions, ns_new);
}

void change_impactt::change_impact(const irep_idt &function)
{
  unified_difft::goto_program_difft diff = unified_diff.get_diff(function);

  if(diff.empty())
    return;

  goto_functionst::function_mapt::const_iterator old_fit=
    old_goto_functions.function_map.find(function);
  goto_functionst::function_mapt::const_iterator new_fit=
    new_goto_functions.function_map.find(function);

  goto_programt empty;

  const goto_programt &old_goto_program=
    old_fit==old_goto_functions.function_map.end() ?
    empty :
    old_fit->second.body;
  const goto_programt &new_goto_program=
    new_fit==new_goto_functions.function_map.end() ?
    empty :
    new_fit->second.body;

  change_impact(
    old_goto_program,
    new_goto_program,
    diff,
    old_change_impact[function],
    new_change_impact[function]);
}

void change_impactt::change_impact(
  const goto_programt &old_goto_program,
  const goto_programt &new_goto_program,
  const unified_difft::goto_program_difft &diff,
  goto_program_change_impactt &old_impact,
  goto_program_change_impactt &new_impact)
{
  goto_programt::const_targett o_it=
    old_goto_program.instructions.begin();
  goto_programt::const_targett n_it=
    new_goto_program.instructions.begin();

  for(const auto &d : diff)
  {
    switch(d.second)
    {
      case unified_difft::differencet::SAME:
        assert(o_it!=old_goto_program.instructions.end());
        assert(n_it!=new_goto_program.instructions.end());
        old_impact[o_it]|=SAME;
        ++o_it;
        assert(n_it==d.first);
        new_impact[n_it]|=SAME;
        ++n_it;
        break;
      case unified_difft::differencet::DELETED:
        assert(o_it!=old_goto_program.instructions.end());
        assert(o_it==d.first);
        {
          const dependence_grapht::nodet &d_node=
            old_dep_graph[old_dep_graph[o_it].get_node_id()];

          if(impact_mode==impact_modet::BACKWARD ||
             impact_mode==impact_modet::BOTH)
            propogate_dep_back(
              d_node,
              old_dep_graph,
              old_change_impact,
              true);
          if(impact_mode==impact_modet::FORWARD ||
             impact_mode==impact_modet::BOTH)
            propogate_dep_forward(
              d_node,
              old_dep_graph,
              old_change_impact,
              true);
        }
        old_impact[o_it]|=DELETED;
        ++o_it;
        break;
      case unified_difft::differencet::NEW:
        assert(n_it!=new_goto_program.instructions.end());
        assert(n_it==d.first);
        {
          const dependence_grapht::nodet &d_node=
            new_dep_graph[new_dep_graph[n_it].get_node_id()];

          if(impact_mode==impact_modet::BACKWARD ||
             impact_mode==impact_modet::BOTH)
            propogate_dep_back(
              d_node,
              new_dep_graph,
              new_change_impact,
              false);
          if(impact_mode==impact_modet::FORWARD ||
             impact_mode==impact_modet::BOTH)
            propogate_dep_forward(
              d_node,
              new_dep_graph,
              new_change_impact,
              false);
        }
        new_impact[n_it]|=NEW;
        ++n_it;
        break;
    }
  }
}


void change_impactt::propogate_dep_forward(
  const dependence_grapht::nodet &d_node,
  const dependence_grapht &dep_graph,
  goto_functions_change_impactt &change_impact,
  bool del)
{
  for(dependence_grapht::edgest::const_iterator it = d_node.out.begin();
      it != d_node.out.end(); ++it)
  {
    goto_programt::const_targett src = dep_graph[it->first].PC;

    mod_flagt data_flag = del ? DEL_DATA_DEP : NEW_DATA_DEP;
    mod_flagt ctrl_flag = del ? DEL_CTRL_DEP : NEW_CTRL_DEP;

    if((change_impact[src->function][src] &data_flag)
        || (change_impact[src->function][src] &ctrl_flag))
      continue;
    if(it->second.get() == dep_edget::kindt::DATA
        || it->second.get() == dep_edget::kindt::BOTH)
      change_impact[src->function][src] |= data_flag;
    else
      change_impact[src->function][src] |= ctrl_flag;
    propogate_dep_forward(dep_graph[dep_graph[src].get_node_id()], dep_graph,
        change_impact, del);
  }
}

void change_impactt::propogate_dep_back(
  const dependence_grapht::nodet &d_node,
  const dependence_grapht &dep_graph,
  goto_functions_change_impactt &change_impact,
  bool del)
{
  for(dependence_grapht::edgest::const_iterator it = d_node.in.begin();
      it != d_node.in.end(); ++it)
  {
    goto_programt::const_targett src = dep_graph[it->first].PC;

    mod_flagt data_flag = del ? DEL_DATA_DEP : NEW_DATA_DEP;
    mod_flagt ctrl_flag = del ? DEL_CTRL_DEP : NEW_CTRL_DEP;

    if((change_impact[src->function][src] &data_flag)
        || (change_impact[src->function][src] &ctrl_flag))
    {
      continue;
    }
    if(it->second.get() == dep_edget::kindt::DATA
        || it->second.get() == dep_edget::kindt::BOTH)
      change_impact[src->function][src] |= data_flag;
    else
      change_impact[src->function][src] |= ctrl_flag;

    propogate_dep_back(dep_graph[dep_graph[src].get_node_id()], dep_graph,
        change_impact, del);
  }
}

void change_impactt::operator()()
{
  // sorted iteration over intersection(old functions, new functions)
  typedef std::map<irep_idt,
                   goto_functionst::function_mapt::const_iterator>
                     function_mapt;

  function_mapt old_funcs, new_funcs;

  forall_goto_functions(it, old_goto_functions)
    old_funcs.insert(std::make_pair(it->first, it));
  forall_goto_functions(it, new_goto_functions)
    new_funcs.insert(std::make_pair(it->first, it));

  function_mapt::const_iterator ito=old_funcs.begin();
  for(function_mapt::const_iterator itn=new_funcs.begin();
      itn!=new_funcs.end();
      ++itn)
  {
    while(ito!=old_funcs.end() && ito->first<itn->first)
      ++ito;

    if(ito!=old_funcs.end() && itn->first==ito->first)
    {
      change_impact(itn->first);

      ++ito;
    }
  }

  goto_functions_change_impactt::const_iterator oc_it=
    old_change_impact.begin();
  for(goto_functions_change_impactt::const_iterator
      nc_it=new_change_impact.begin();
      nc_it!=new_change_impact.end();
      ++nc_it)
  {
    for( ;
        oc_it!=old_change_impact.end() && oc_it->first<nc_it->first;
        ++oc_it)
      output_change_impact(
        oc_it->first,
        oc_it->second,
        old_goto_functions,
        ns_old);

    if(oc_it==old_change_impact.end() || nc_it->first<oc_it->first)
      output_change_impact(
        nc_it->first,
        nc_it->second,
        new_goto_functions,
        ns_new);
    else
    {
      assert(oc_it->first==nc_it->first);

      output_change_impact(
        nc_it->first,
        oc_it->second,
        old_goto_functions,
        ns_old,
        nc_it->second,
        new_goto_functions,
        ns_new);

      ++oc_it;
    }
  }
}

void change_impactt::output_change_impact(
  const irep_idt &function,
  const goto_program_change_impactt &c_i,
  const goto_functionst &goto_functions,
  const namespacet &ns) const
{
  goto_functionst::function_mapt::const_iterator f_it=
    goto_functions.function_map.find(function);
  assert(f_it!=goto_functions.function_map.end());
  const goto_programt &goto_program=f_it->second.body;

  if(!compact_output)
    std::cout << "/** " << function << " **/\n";

  forall_goto_program_instructions(target, goto_program)
  {
    goto_program_change_impactt::const_iterator c_entry=
      c_i.find(target);
    const unsigned mod_flags =
      c_entry == c_i.end() ? static_cast<unsigned>(SAME) : c_entry->second;

    char prefix = ' ';
    // syntactic changes are preferred over data/control-dependence
    // modifications
    if(mod_flags==SAME)
      prefix=' ';
    else if(mod_flags&DELETED)
      prefix='-';
    else if(mod_flags&NEW)
      prefix='+';
    else if(mod_flags&NEW_DATA_DEP)
      prefix='D';
    else if(mod_flags&NEW_CTRL_DEP)
      prefix='C';
    else if(mod_flags&DEL_DATA_DEP)
      prefix='d';
    else if(mod_flags&DEL_CTRL_DEP)
      prefix='c';
    else
      UNREACHABLE;

    output_instruction(prefix, goto_program, ns, function, target);
  }
}

void change_impactt::output_change_impact(
  const irep_idt &function,
  const goto_program_change_impactt &o_c_i,
  const goto_functionst &o_goto_functions,
  const namespacet &o_ns,
  const goto_program_change_impactt &n_c_i,
  const goto_functionst &n_goto_functions,
  const namespacet &n_ns) const
{
  goto_functionst::function_mapt::const_iterator o_f_it=
    o_goto_functions.function_map.find(function);
  assert(o_f_it!=o_goto_functions.function_map.end());
  const goto_programt &old_goto_program=o_f_it->second.body;

  goto_functionst::function_mapt::const_iterator f_it=
    n_goto_functions.function_map.find(function);
  assert(f_it!=n_goto_functions.function_map.end());
  const goto_programt &goto_program=f_it->second.body;

  if(!compact_output)
    std::cout << "/** " << function << " **/\n";

  goto_programt::const_targett o_target=
    old_goto_program.instructions.begin();
  forall_goto_program_instructions(target, goto_program)
  {
    goto_program_change_impactt::const_iterator o_c_entry=
      o_c_i.find(o_target);
    const unsigned old_mod_flags = o_c_entry == o_c_i.end()
                                     ? static_cast<unsigned>(SAME)
                                     : o_c_entry->second;

    if(old_mod_flags&DELETED)
    {
      output_instruction('-', goto_program, o_ns, function, o_target);
      ++o_target;
      --target;
      continue;
    }

    goto_program_change_impactt::const_iterator c_entry=
      n_c_i.find(target);
    const unsigned mod_flags =
      c_entry == n_c_i.end() ? static_cast<unsigned>(SAME) : c_entry->second;

    char prefix = ' ';
    // syntactic changes are preferred over data/control-dependence
    // modifications
    if(mod_flags==SAME)
    {
      if(old_mod_flags==SAME)
        prefix=' ';
      else if(old_mod_flags&DEL_DATA_DEP)
        prefix='d';
      else if(old_mod_flags&DEL_CTRL_DEP)
        prefix='c';
      else
        UNREACHABLE;

      ++o_target;
    }
    else if(mod_flags&DELETED)
      UNREACHABLE;
    else if(mod_flags&NEW)
      prefix='+';
    else if(mod_flags&NEW_DATA_DEP)
    {
      prefix='D';

      assert(old_mod_flags==SAME ||
             old_mod_flags&DEL_DATA_DEP ||
             old_mod_flags&DEL_CTRL_DEP);
      ++o_target;
    }
    else if(mod_flags&NEW_CTRL_DEP)
    {
      prefix='C';

      assert(old_mod_flags==SAME ||
             old_mod_flags&DEL_DATA_DEP ||
             old_mod_flags&DEL_CTRL_DEP);
      ++o_target;
    }
    else
      UNREACHABLE;

    output_instruction(prefix, goto_program, n_ns, function, target);
  }
  for( ;
      o_target!=old_goto_program.instructions.end();
      ++o_target)
  {
    goto_program_change_impactt::const_iterator o_c_entry=
      o_c_i.find(o_target);
    const unsigned old_mod_flags = o_c_entry == o_c_i.end()
                                     ? static_cast<unsigned>(SAME)
                                     : o_c_entry->second;

    char prefix = ' ';
    // syntactic changes are preferred over data/control-dependence
    // modifications
    if(old_mod_flags==SAME)
      UNREACHABLE;
    else if(old_mod_flags&DELETED)
      prefix='-';
    else if(old_mod_flags&NEW)
      UNREACHABLE;
    else if(old_mod_flags&DEL_DATA_DEP)
      prefix='d';
    else if(old_mod_flags&DEL_CTRL_DEP)
      prefix='c';
    else
      UNREACHABLE;

    output_instruction(prefix, goto_program, o_ns, function, o_target);
  }
}

void change_impactt::output_instruction(char prefix,
    const goto_programt &goto_program,
    const namespacet &ns,
    const irep_idt &function,
    goto_programt::const_targett &target) const
{
  if(compact_output)
  {
    if(prefix == ' ')
      return;
    const irep_idt &file=target->source_location.get_file();
    const irep_idt &line=target->source_location.get_line();
    if(!file.empty() && !line.empty())
      std::cout << prefix << " " << id2string(file)
                << " " << id2string(line) << '\n';
  }
  else
  {
    std::cout << prefix;
    goto_program.output_instruction(ns, function, std::cout, *target);
  }
}

void change_impact(
  const goto_modelt &model_old,
  const goto_modelt &model_new,
  impact_modet impact_mode,
  bool compact_output)
{
  change_impactt c(model_old, model_new, impact_mode, compact_output);
  c();
}
