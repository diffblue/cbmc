//
// Created by Yakir Vizel on 5/1/24.
//

#include "cutpoint_graph.h"
#include "language_util.h"

#include <iostream>
#include <fstream>

cutpoint_grapht::~cutpoint_grapht() {
  m_edges.clear();
  m_cps.clear();
  m_insts.clear();
}

void cutpoint_grapht::run(const goto_functiont & goto_function)
{
  compute_cutpoints(goto_function);
  compute_fwd_reach(goto_function);
  compute_bwd_reach(goto_function);
  compute_edges(goto_function);

  to_dot(goto_function, "cp.dot");
}

void cutpoint_grapht::to_dot(const goto_functiont & f, std::string filename)
{
  std::ofstream out;
  out.open(filename);
  out << "digraph G {\n";
  out << "color=black\nfontsize=20" << '\n';

  const namespacet ns(m_goto_model.symbol_table);

  for (auto cp : m_cps)
  {
    cp->to_dot(out, ns);
  }

  for (auto edge : m_edges)
  {
    out << "Node_" << edge->source().id();
    out << " -> ";
    out << "Node_" << edge->target().id();
    std::string label;
    for (auto inst : *edge)
    {
      std::string code;
      if (inst->is_assign())
      {
        code = from_expr(ns, goto_functionst::entry_point(), inst->code());
      }
      label += inst->to_string() +": " + code + "\n";
    }
    out << "[fontsize=22,label=\"" << label << "\"];\n";
  }


  out << "}\n";

  out.close();
}

cutpoint_edge_ptr cutpoint_grapht::get_edge(const cutpointt &s, const cutpointt &d)
{
  for (auto it = s.succ_begin (), end = s.succ_end (); it != end; ++it)
  {
    cutpoint_edge_ptr edg = *it;
    if (&(edg->target ()) == &d) return edg;
  }

  return nullptr;
}

const cutpoint_edge_ptr
cutpoint_grapht::getEdge(const cutpointt &s, const cutpointt &d) const
{
  for (auto it = s.succ_begin (), end = s.succ_end (); it != end; ++it)
  {
    cutpoint_edge_ptr edg = *it;
    if (&(edg->target ()) == &d) return edg;
  }

  return nullptr;
}

void cutpoint_grapht::compute_edges(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    if (is_cutpoint(*it))
    {
      std::vector<bool> & reach = m_fwd[&(*it)];
      cutpointt & cp = get_cutpoint(*it);

      for (std::size_t r = 0; r < reach.size(); r++)
      {
        if (reach[r] == true)
        {
          cutpoint_edge_ptr edg = create_edge(cp, *m_cps[r]);
          edg->push_back(&(*it));
        }
      }
    }
    else
    {
      std::vector<bool> & breach = m_bwd[&(*it)];
      std::vector<bool> & freach = m_fwd[&(*it)];

      for (int i = 0; i < breach.size(); i++)
      {
        if (breach[i] == false) continue;
        for (int j = 0; j < freach.size(); j++) {
          if (freach[j] == false) continue;
          cutpoint_edge_ptr edge = get_edge(*m_cps[i], *m_cps[j]);
          edge->push_back(&(*it));
        }
      }
    }
  }
}

void cutpoint_grapht::compute_cutpoints(const goto_functiont &goto_function)
{
  m_cps.clear();

  std::map<const goto_programt::instructiont*, std::size_t> cp_map;

  forall_goto_program_instructions(it, goto_function.body)
  {
    if (cp_map.find(&*it) != cp_map.end()) continue;

    // entry
    if (it->incoming_edges.empty())
    {
      auto i = cp_map.find(&*it);
      if (i == cp_map.end())
        cp_map.insert(std::make_pair(&*it, cp_map.size()));
    }

    // exit
    if (it->is_end_function())
    {
      auto i = cp_map.find(&*it);
      if (i == cp_map.end())
        cp_map.insert(std::make_pair(&*it, cp_map.size()));
    }

    for (auto in : it->incoming_edges)
    {
      auto & inst = *in;
      if (inst.is_backwards_goto())
      {
        auto i = cp_map.find(&*it);
        if (i == cp_map.end())
          cp_map.insert(std::make_pair(&*it, cp_map.size()));
      }
    }
  }

  forall_goto_program_instructions(it, goto_function.body)
  {
    auto i = cp_map.find(&*it);
    if (i == cp_map.end()) continue;
    auto inst = i->first;
    if (is_cutpoint(*inst)) continue;

    m_cps.push_back(std::make_shared<cutpointt>(*this, m_cps.size(), *inst));
    m_insts.insert(std::make_pair(inst, m_cps.back()));
  }
}

void cutpoint_grapht::compute_fwd_reach(const goto_functiont &goto_function)
{

  for (auto it = goto_function.body.instructions.rbegin(); it != goto_function.body.instructions.rend();)
  {
    auto itf = (++it).base();
    auto succs = goto_function.body.get_successors(itf);
    //if (succs.empty()) continue;
    auto inst = &*itf;
    m_fwd.insert(std::make_pair(inst, reachabilityt()));
    reachabilityt &r = m_fwd [inst];
    for (auto succ : succs)
    {
      if (is_cutpoint(*succ))
        r.set(get_cutpoint(*succ).id());
      else
        r |= m_fwd[&*succ];

    }
  }
}

void cutpoint_grapht::compute_bwd_reach(const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    auto inst = &*it;
    m_bwd.insert(std::make_pair(inst, reachabilityt()));
    reachabilityt &r = m_bwd[inst];
    for(auto pred : it->incoming_edges)
    {
      if(pred->is_backwards_goto())
        continue;
      if(is_cutpoint(*pred))
        r.set(get_cutpoint(*pred).id());
      else
        r |= m_bwd[&*pred];

    }
  }

  for (auto & cp : m_cps)
  {
    auto & inst = cp->inst();
    reachabilityt &r = m_bwd [&inst];

    for (auto pred : inst.incoming_edges)
    {
      if (! pred->is_backwards_goto()) continue;
      if (is_cutpoint(*pred))
        r.set(get_cutpoint(*pred).id());
      else
        r |= m_bwd[&*pred];
    }
  }
}

