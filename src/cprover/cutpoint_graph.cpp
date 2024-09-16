//
// Created by Yakir Vizel on 5/1/24.
//

#include "cutpoint_graph.h"
#include "language_util.h"

#include <iostream>
#include <fstream>

cutpoint_graph::~cutpoint_graph() {
  m_edges.clear();
  m_cps.clear();
  m_insts.clear();
}

void cutpoint_graph::run(const goto_functiont & goto_function)
{
  computeCutpoints (goto_function);
  computeFwdReach (goto_function);
  computeBwdReach (goto_function);
  computeEdges (goto_function);

  toDot(goto_function, "cp.dot");
}

void cutpoint_graph::toDot(const goto_functiont & f, std::string filename)
{
  std::ofstream out;
  out.open(filename);
  out << "digraph G {\n";
  out << "color=black\nfontsize=20" << '\n';

  const namespacet ns(m_goto_model.symbol_table);

  for (auto cp : m_cps)
  {
    cp->toDot(out, ns);
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

cutpoint_edge_ptr cutpoint_graph::getEdge(const cutpoint &s, const cutpoint &d)
{
  for (auto it = s.succ_begin (), end = s.succ_end (); it != end; ++it)
  {
    cutpoint_edge_ptr edg = *it;
    if (&(edg->target ()) == &d) return edg;
  }

  return nullptr;
}

const cutpoint_edge_ptr cutpoint_graph::getEdge(const cutpoint &s, const cutpoint &d) const
{
  for (auto it = s.succ_begin (), end = s.succ_end (); it != end; ++it)
  {
    cutpoint_edge_ptr edg = *it;
    if (&(edg->target ()) == &d) return edg;
  }

  return nullptr;
}

void cutpoint_graph::computeEdges (const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    if (isCutpoint(*it))
    {
      std::vector<bool> & reach = m_fwd[&(*it)];
      cutpoint & cp = getCutpoint(*it);

      for (unsigned r = 0; r < reach.size(); r++)
      {
        if (reach[r] == true)
        {
          cutpoint_edge_ptr edg = newEdge(cp, *m_cps[r]);
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
          cutpoint_edge_ptr edge = getEdge(*m_cps[i], *m_cps[j]);
          edge->push_back(&(*it));
        }
      }
    }
  }
}

void cutpoint_graph::computeCutpoints(const goto_functiont &goto_function)
{
  m_cps.clear();

  std::map<const goto_programt::instructiont*, unsigned> cp_map;

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
    if (isCutpoint(*inst)) continue;

    m_cps.push_back(std::make_shared<cutpoint>(*this, m_cps.size(), *inst));
    m_insts.insert(std::make_pair(inst, m_cps.back()));
  }
}

void cutpoint_graph::computeFwdReach (const goto_functiont &goto_function)
{

  for (auto it = goto_function.body.instructions.rbegin(); it != goto_function.body.instructions.rend();)
  {
    auto itf = (++it).base();
    auto succs = goto_function.body.get_successors(itf);
    //if (succs.empty()) continue;
    auto inst = &*itf;
    m_fwd.insert(std::make_pair(inst, reachability()));
    reachability &r = m_fwd [inst];
    std::cout << inst->to_string() << "\n";
    if (succs.size() > 1) std::cout << "YAY\n";
    for (auto succ : succs)
    {
      if (isCutpoint(*succ))
        r.set(getCutpoint(*succ).id());
      else
        r |= m_fwd[&*succ];

    }
  }
}

void cutpoint_graph::computeBwdReach (const goto_functiont &goto_function)
{
  forall_goto_program_instructions(it, goto_function.body)
  {
    auto inst = &*it;
    m_bwd.insert(std::make_pair(inst, reachability()));
    reachability &r = m_bwd[inst];
    for(auto pred : it->incoming_edges)
    {
      if(pred->is_backwards_goto())
        continue;
      if(isCutpoint(*pred))
        r.set(getCutpoint(*pred).id());
      else
        r |= m_bwd[&*pred];

    }
  }

  for (auto & cp : m_cps)
  {
    auto & inst = cp->inst();
    reachability &r = m_bwd [&inst];

    for (auto pred : inst.incoming_edges)
    {
      if (! pred->is_backwards_goto()) continue;
      if (isCutpoint(*pred))
        r.set(getCutpoint(*pred).id());
      else
        r |= m_bwd[&*pred];
    }
  }
}

bool cutpoint_graph::isFwdReach(const cutpoint &cp, const goto_programt::instructiont &inst) const
{
  if (&(cp.inst ()) == &inst) return true;

  // The instruction is already a cut-point, but not the one testes.
  // It is impossible to reach another cut-point without getting to it
  if (isCutpoint(inst)) return false;

  // In case the instruction is not a cut-point, retrieve the backward
  // reachability info (cut-point backward reachability) and check if the
  // cut-point is backward reachable. If it is, then the instruction
  // is forward reachable from the given cp.
  auto it = m_bwd.find (&inst);
  INVARIANT(it != m_bwd.end (), "No back-reachability information");

  unsigned sz = it->second.size ();
  unsigned id = cp.id ();
  if (sz == 0 || id >= sz) return false;
  return (it->second)[id];
}
