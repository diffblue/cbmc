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

class cutpoint_grapht;
class cutpointt;

class cutpoint_edget
{
  friend class cutpoint_grapht;

  cutpointt & m_src;
  cutpointt & m_dst;

  typedef std::vector<const goto_programt::instructiont *> inst_vect;
  inst_vect m_insts;

  cutpointt &source() { return m_src; }
  cutpointt &target() { return m_dst; }
public:
  cutpoint_edget(cutpointt & s, cutpointt & d) : m_src(s), m_dst(d) {}

  const cutpoint_grapht & graph() const;

  const cutpointt &source() const { return m_src; }
  const cutpointt &target() const { return m_dst; }

  void push_back(const goto_programt::instructiont * inst)
  {
    m_insts.push_back(inst);
  }

  typedef inst_vect::iterator iterator;
  typedef inst_vect::const_iterator const_iterator;

  iterator begin() { return m_insts.begin(); }
  iterator end() { return m_insts.end(); }
  const_iterator begin() const { return m_insts.begin(); }
  const_iterator end() const { return m_insts.end(); }
};

typedef std::shared_ptr<cutpoint_edget> cutpoint_edge_ptr;

class cutpointt
{
  const cutpoint_grapht &m_graph;
  std::size_t m_id;
  const goto_programt::instructiont & m_inst;

  typedef std::vector<cutpoint_edge_ptr> edge_vect;
  edge_vect m_succ;

public:
  cutpointt(const cutpoint_grapht &p, std::size_t id, const goto_programt::instructiont &inst)
    : m_graph(p), m_id(id), m_inst(inst) {}

  const cutpoint_grapht &graph() const { return m_graph; }
  std::size_t id() const { return m_id; }
  const goto_programt::instructiont &inst() const { return m_inst; }

  void add_succ(cutpoint_edge_ptr & edg) { m_succ.push_back(edg); }

  typedef edge_vect::const_iterator const_iterator;
  typedef edge_vect::const_reverse_iterator const_reverse_iterator;

  const_iterator succ_begin() const { return m_succ.begin(); }
  const_iterator succ_end() const { return m_succ.end(); }

  void to_dot(std::ostream & out, const namespacet & ns)
  {
    out << "Node_" << m_id << " [shape=Mrecord,fontsize=22,label=\"";
    out << m_inst.to_string() << "\"];\n";
  }
};

class cutpoint_grapht
{
  const goto_modelt & m_goto_model;

  typedef std::shared_ptr<cutpointt> cutpoint_ptr;
  typedef std::vector<cutpoint_ptr> cutpoint_vect;

  typedef std::vector<cutpoint_edge_ptr> edge_vect;

  cutpoint_vect m_cps;
  edge_vect m_edges;

  class reachabilityt : public std::vector<bool> {
  public:
    void set(std::size_t index) {
      if (index >= size()) resize(index+1, false);
      (*this)[index] = true;
    }

    reachabilityt & operator|=(const reachabilityt & other) {
      if (this->size() < other.size())
        this->resize(other.size(), false);
      for (std::size_t i = 0; i < other.size(); i++)
        (*this)[i] = (*this)[i] || other[i];
      return *this;
    }
  };

  typedef std::map<const goto_programt::instructiont*, reachabilityt>
    inst_bool_mapt;

  inst_bool_mapt m_fwd;
  inst_bool_mapt m_bwd;

  std::map<const goto_programt::instructiont*, std::shared_ptr<cutpointt>> m_insts;

  cutpoint_edge_ptr create_edge(cutpointt &s, cutpointt &d) {
    m_edges.push_back(std::make_shared<cutpoint_edget>(s, d));

    cutpoint_edge_ptr edg = m_edges.back();

    s.add_succ(edg);
    return edg;
  }

  void compute_cutpoints(const goto_functiont & goto_function);
  void compute_fwd_reach(const goto_functiont & goto_function);
  void compute_bwd_reach(const goto_functiont & goto_function);
  void compute_edges(const goto_functiont & goto_function);

  void to_dot(const goto_functiont & f, std::string filename);

public:
  cutpoint_grapht(const goto_modelt & goto_model) : m_goto_model(goto_model) {}
  ~cutpoint_grapht();

  void run(const goto_functiont & goto_function);

  bool is_cutpoint(const goto_programt::instructiont & inst) const
  {
    return m_insts.count(&inst) > 0;
  }

  cutpointt &get_cutpoint(const goto_programt::instructiont & inst) const {
    INVARIANT(is_cutpoint(inst), "Function should be called with a cutpoint");
    return *(m_insts.find(&inst)->second);
  }

  cutpoint_edge_ptr get_edge(const cutpointt &s, const cutpointt &d);
  const cutpoint_edge_ptr getEdge(const cutpointt &s, const cutpointt &d) const;
};

inline const cutpoint_grapht &cutpoint_edget::graph() const { return m_src.graph(); }



#endif //CBMC_CUTPOINT_GRAPH_H
