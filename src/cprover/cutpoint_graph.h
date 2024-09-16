//
// Created by Yakir Vizel on 5/1/24.
//

#ifndef CBMC_CUTPOINT_GRAPH_H
#define CBMC_CUTPOINT_GRAPH_H

#include "goto_model.h"
#include <vector>

/**
 * A cut-point graph over goto programs.
 * The cut-points are:
 * 1. Entry node
 * 2. Exit node
 * 3. Every node that has a back-edge - namely, a loop head.
 */

class cutpoint_graph;
class cutpoint;

class cutpoint_edge
{
  friend class cutpoint_graph;

  cutpoint & m_src;
  cutpoint & m_dst;

  typedef std::vector<const goto_programt::instructiont *> InstVec;
  InstVec m_insts;

  cutpoint &source() { return m_src; }
  cutpoint &target() { return m_dst; }
public:
  cutpoint_edge(cutpoint & s, cutpoint & d) : m_src(s), m_dst(d) {}

  const cutpoint_graph& graph() const;

  const cutpoint &source() const { return m_src; }
  const cutpoint &target() const { return m_dst; }

  void push_back(const goto_programt::instructiont * inst)
  {
    m_insts.push_back(inst);
  }

  typedef InstVec::iterator iterator;
  typedef InstVec::const_iterator const_iterator;

  iterator begin() { return m_insts.begin(); }
  iterator end() { return m_insts.end(); }
  const_iterator begin() const { return m_insts.begin(); }
  const_iterator end() const { return m_insts.end(); }
};

typedef std::shared_ptr<cutpoint_edge> cutpoint_edge_ptr;

class cutpoint
{
  friend class cutpoint_graph;

  const cutpoint_graph &m_graph;
  unsigned m_id;
  const goto_programt::instructiont & m_inst;

  typedef std::vector<cutpoint_edge_ptr> EdgeVec;
  EdgeVec m_succ;

public:
  cutpoint(const cutpoint_graph &p, unsigned id, const goto_programt::instructiont &inst)
    : m_graph(p), m_id(id), m_inst(inst) {}

  const cutpoint_graph &graph() const { return m_graph; }
  unsigned id() const { return m_id; }
  const goto_programt::instructiont &inst() const { return m_inst; }

  void addSucc(cutpoint_edge_ptr & edg) { m_succ.push_back(edg); }

  typedef EdgeVec::const_iterator const_iterator;
  typedef EdgeVec::const_reverse_iterator const_reverse_iterator;

  const_iterator succ_begin() const { return m_succ.begin(); }
  const_iterator succ_end() const { return m_succ.end(); }

  void toDot(std::ostream & out, const namespacet & ns)
  {
    out << "Node_" << m_id << " [shape=Mrecord,fontsize=22,label=\"";
    out << m_inst.to_string() << "\"];\n";
  }
};

class cutpoint_graph
{
  const goto_modelt & m_goto_model;

  typedef std::shared_ptr<cutpoint> cutpoint_ptr;
  typedef std::vector<cutpoint_ptr> CutpointVec;

  typedef std::vector<cutpoint_edge_ptr> EdgeVec;

  CutpointVec m_cps;
  EdgeVec m_edges;

  class reachability : public std::vector<bool> {
  public:
    void set(unsigned index) {
      if (index >= size()) resize(index+1, false);
      (*this)[index] = true;
    }

    reachability& operator|=(const reachability & other) {
      if (this->size() < other.size())
        this->resize(other.size(), false);
      for (unsigned i = 0; i < other.size(); i++)
        (*this)[i] = (*this)[i] || other[i];
      return *this;
    }
  };

  typedef std::map<const goto_programt::instructiont*, reachability> InstBoolMap;

  InstBoolMap m_fwd;
  InstBoolMap m_bwd;

  std::map<const goto_programt::instructiont*, std::shared_ptr<cutpoint>> m_insts;

  cutpoint_edge_ptr newEdge(cutpoint &s, cutpoint &d) {
    m_edges.push_back(std::make_shared<cutpoint_edge>(s, d));

    cutpoint_edge_ptr edg = m_edges.back();

    s.addSucc(edg);
    return edg;
  }

  void computeCutpoints(const goto_functiont & goto_function);
  void computeFwdReach(const goto_functiont & goto_function);
  void computeBwdReach(const goto_functiont & goto_function);
  void computeEdges(const goto_functiont & goto_function);

  void toDot(const goto_functiont & f, std::string filename);

public:
  cutpoint_graph(const goto_modelt & goto_model) : m_goto_model(goto_model) {}
  ~cutpoint_graph();

  void run(const goto_functiont & goto_function);

  bool isCutpoint(const goto_programt::instructiont & inst) const
  {
    return m_insts.count(&inst) > 0;
  }

  cutpoint &getCutpoint(const goto_programt::instructiont & inst) const {
    INVARIANT(isCutpoint(inst), "Function should be called with a cutpoint");
    return *(m_insts.find(&inst)->second);
  }

  cutpoint_edge_ptr getEdge(const cutpoint &s, const cutpoint &d);
  const cutpoint_edge_ptr getEdge(const cutpoint &s, const cutpoint &d) const;

  bool isFwdReach(const cutpoint & cp, const goto_programt::instructiont &inst) const;
};

inline const cutpoint_graph & cutpoint_edge::graph() const { return m_src.graph(); }



#endif //CBMC_CUTPOINT_GRAPH_H
