//
// Created by Yakir Vizel on 5/28/24.
//

#ifndef CBMC_CHC_WTO_H
#define CBMC_CHC_WTO_H

#include "chc_db.h"
#include <invariant.h>

#include <optional>
#include <unordered_map>
#include <vector>
#include <deque>
#include <iostream>

class wto_singletont;
class wto_componentt;

class wto_element_visitort
{
public:

  virtual void visit(const wto_singletont &) = 0;
  virtual void visit(const wto_componentt &) = 0;

  virtual ~wto_element_visitort() {}
};

class wto_elementt
{
public:
  virtual void accept(wto_element_visitort *) = 0;

  virtual ~wto_elementt() {}
};

class wto_singletont : public wto_elementt
{
private:
  const symbol_exprt* m_singleton;

public:
  wto_singletont(const symbol_exprt *e) : m_singleton(e) {}

  const symbol_exprt* get() const { return m_singleton; }

  void accept(wto_element_visitort *v) override { v->visit(*this); }
};

class wto_componentt : public wto_elementt
{

public:
  typedef std::shared_ptr<wto_elementt> wto_element_ptr;
  typedef std::deque<wto_element_ptr> wto_components_t;

private:
  const symbol_exprt *m_head;
  wto_components_t m_components;

public:
  wto_componentt(const symbol_exprt *head, wto_components_t components)
    : m_head(head), m_components(components) {}

  typename wto_components_t::iterator begin() {
    return m_components.begin();
  }

  typename wto_components_t::iterator end() { return m_components.end(); }

  typename wto_components_t::const_iterator begin() const {
    return m_components.begin();
  }

  typename wto_components_t::const_iterator end() const {
    return m_components.end();
  }

  const symbol_exprt* head() const { return m_head; }

  void accept(wto_element_visitort *v) override { v->visit(*this); }
};

class chc_wtot
{
private:
  // A helper class to extend an unsigned number with +oo;
  class inf_numt
  {
    std::optional<unsigned> m_n;

  public:
    // +oo
    inf_numt() : m_n(std::nullopt) { }
    inf_numt(unsigned n) : m_n(n) { }
    inf_numt(const inf_numt &o) : m_n(o.m_n) { }

    inf_numt &operator=(inf_numt o)
    {
      m_n = o.m_n;
      return *this;
    }

    bool is_plus_infinite() const { return m_n == std::nullopt; }
    bool is_finite() const { return !is_plus_infinite(); }

    unsigned number() const
    {
      INVARIANT(is_finite(), "Cannot call number() on infinite");
      return *m_n;
    }

    bool operator==(inf_numt o) const
    {
      if(is_plus_infinite() && o.is_plus_infinite())
        return true;

      if(is_plus_infinite() || o.is_plus_infinite())
        return false;

      return (number() == o.number());
    }

    bool operator<=(inf_numt o) const
    {
      if(is_plus_infinite() && o.is_plus_infinite())
        return true;

      if(is_plus_infinite())
        return false;

      if(o.is_plus_infinite())
        return true;

      return (number() <= o.number());
    }
  };

  typedef std::shared_ptr<wto_elementt> wto_element_ptr;
  typedef std::deque<wto_element_ptr> partition_t;
  typedef std::unordered_map<std::size_t , std::vector<wto_componentt>>
    nested_components_t;

  chc_graph & m_g;

  std::unordered_map<std::size_t, inf_numt> m_dfn;
  std::vector<const symbol_exprt*> m_stack;
  unsigned m_cur_dfn_num;

  std::deque<wto_element_ptr> m_partition;
  nested_components_t m_nested_comp;

private:
  // helper to avoid initializing all vertices to zero
  inf_numt get_dfn(const symbol_exprt* v) const {
    auto it = m_dfn.find(v->hash());
    if (it != m_dfn.end())
      return it->second;
    return 0;
  }

  std::deque<wto_element_ptr> component(const symbol_exprt* v) {
    std::deque<wto_element_ptr> partition;
    for (auto & target : m_g.outgoing(*v)) {
      const symbol_exprt* t = (&to_symbol_expr(target));
      if (get_dfn(t) == 0)
        visit(t, partition);
    }
    return partition;
  }

  inf_numt visit(const symbol_exprt* v, std::deque<wto_element_ptr> &partition) {
    std::string name = as_string(v->get_identifier());
    m_stack.push_back(v);
    m_dfn[v->hash()] = m_cur_dfn_num++;
    auto head = get_dfn(v);
    bool loop = false;
    for (auto & target : m_g.outgoing(*v)) {
      const symbol_exprt* t = (&to_symbol_expr(target));
      auto min = get_dfn(t);
      if (min == 0)
        min = visit(t, partition);
      if (min <= head) {
        head = min;
        loop = true;
      }
    }

    if (head == get_dfn(v)) { // v is the head of a component
      m_dfn[v->hash()] = inf_numt();
      auto element = m_stack.back();
      m_stack.pop_back();
      if (loop) {
        while (!(element == v)) {
          m_dfn[element->hash()] = 0; // reset
          element = m_stack.back();
          m_stack.pop_back();
        }
        partition.push_front(std::static_pointer_cast<wto_elementt>(
          std::make_shared<wto_componentt>(v, component(v))));
      } else {
        partition.push_front(std::static_pointer_cast<wto_elementt>(
          std::make_shared<wto_singletont>(v)));
      }
    }
    return head;
  }

  class nested_components_visitor : public wto_element_visitort
  {
    std::vector<wto_componentt> m_nested_components;
    nested_components_t &m_nested_components_table;

  public:
    nested_components_visitor(nested_components_t &t)
      : wto_element_visitort(), m_nested_components_table(t) {}

    virtual void visit(const wto_singletont &s) override {
      m_nested_components_table[s.get()->hash()] = m_nested_components;
    }

    virtual void visit(const wto_componentt &c) override {
      m_nested_components.push_back(c);
      m_nested_components_table[c.head()->hash()] = m_nested_components;
      for (auto &e : c) {
        e->accept(this);
      }
      m_nested_components.pop_back();
    }
  };

  // build a map from graph vertex to nested components in the wto
  void build_nested_components() {
    nested_components_visitor vis(m_nested_comp);
    for (auto c : m_partition) {
      c->accept(&vis);
    }
  }

public:
  chc_wtot(chc_graph & g) : m_g(g), m_cur_dfn_num(0) {}

  void build_wto() {
    if (!m_g.has_entry())
    {
      throw incorrect_goto_program_exceptiont("No entry point to CHC");
    }
    visit(m_g.entry(), m_partition);
    build_nested_components();
    // cleanup
    m_stack.clear();
    m_dfn.clear();
  }

  partition_t::iterator begin() { return m_partition.begin(); }
  partition_t::iterator end() { return m_partition.end(); }
  partition_t::const_iterator begin() const { return m_partition.begin(); }
  partition_t::const_iterator end() const { return m_partition.end(); }

  std::vector<wto_componentt>::iterator nested_comp_begin(symbol_exprt* p) {
    return m_nested_comp[p->hash()].begin();
  }
  std::vector<wto_componentt>::iterator nested_comp_end(symbol_exprt* p) {
    return m_nested_comp[p->hash()].end();
  }
  std::vector<wto_componentt>::const_iterator nested_comp_begin(symbol_exprt* p) const {
    auto it = m_nested_comp.find(p->hash());
    INVARIANT(it != m_nested_comp.end(), "No nested component");
    return it->second.begin();
  }
  std::vector<wto_componentt>::const_iterator nested_comp_end(symbol_exprt* p) const {
    auto it = m_nested_comp.find(p->hash());
    INVARIANT(it != m_nested_comp.end(), "No nested component");
    return it->second.end();
  }
};

class SimpleVisitor : public wto_element_visitort
{
  virtual void visit(const wto_singletont & s)
  {
    const symbol_exprt* symb = s.get();
    std::string str = as_string(symb->get_identifier());
    std::cout  << str << " ";
  }

  virtual void visit(const wto_componentt & comp)
  {
    const symbol_exprt* head = comp.head();
    std::string str = head->get_identifier().c_str();
    std::cout << "(" << str << " ";
    for (auto it = comp.begin(); it != comp.end(); it++)
    {
      it->get()->accept(this);
    }
    std::cout << ")" << " ";
  }
};

#endif //CBMC_CHC_WTO_H
