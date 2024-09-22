//
// Created by Yakir Vizel on 5/27/24.
//

#ifndef CBMC_CHC_DB_H
#define CBMC_CHC_DB_H

#include <util/mathematical_expr.h>
#include <util/std_expr.h>
#include <util/find_symbols.h>
#include <language_util.h>

#include <vector>
#include <map>
#include <set>
#include <functional>

class chc_db;
class horn_clause
{
  forall_exprt m_chc;

public:
  horn_clause(forall_exprt f) : m_chc(f) {}

  horn_clause(std::vector<symbol_exprt> & vars, exprt clause) : m_chc(vars, clause) {

  }

  const forall_exprt & get_chc() const
  {
    return m_chc;
  }

  const exprt* body() const {
    if (can_cast_expr<implies_exprt>(m_chc.where()))
    {
      return &to_implies_expr(m_chc.where()).op0();
    }
    return &m_chc.where();
  }

  const exprt* head() const {
    if (can_cast_expr<implies_exprt>(m_chc.where()))
    {
      return &to_implies_expr(m_chc.where()).op1();
    }
    return nullptr;
  }

  bool is_fact() const {
    auto b = body();
    bool not_fact = false;
    b->visit_pre(
      [&not_fact](const exprt &expr)  {
        if(can_cast_expr<function_application_exprt>(expr))
        {
          not_fact = true;
        }
      });
    return !not_fact;
  }

  bool is_query() const {
    if (can_cast_expr<implies_exprt>(m_chc.where()))
    {
      auto h = head();
      bool res = true;
      h->visit_pre(
        [&res](const exprt &expr) {
          if(can_cast_expr<function_application_exprt>(expr))
            res = false;
      });
      return res;
    }
    return false;
  }

  bool operator==(const horn_clause &other) const
  {
    return m_chc == other.m_chc;
  }

  bool operator!=(const horn_clause &other) const
  {
    return !(*this==other);
  }

  bool operator<(const horn_clause &other) const
  {
    return m_chc < other.m_chc;
  }

  template <typename OutputIterator>
  void used_relations(chc_db &db, OutputIterator out) const;
  template <typename OutputIterator>
  void used_func_app(chc_db &db, OutputIterator out) const;
};

/*
 * A database of CHCs.
 * Uninterpreted relations need to be registered.
 */
class chc_db
{
  friend class horn_clause;
public:
  struct is_state_pred : public std::__unary_function<exprt, bool> {
    const chc_db &m_db;
    is_state_pred(const chc_db &db) : m_db(db) {}

    bool operator()(symbol_exprt state) { return m_db.has_state_pred(state); }
  };

private:
  using chcst = std::vector<horn_clause>;
  chcst m_clauses;

  std::set<symbol_exprt> m_state_preds;

  typedef std::set<const horn_clause *> chc_sett;
  typedef std::map<exprt, std::set<const horn_clause *>> chc_indext;
  chc_indext m_body_idx;
  chc_indext m_head_idx;

  // representing the empty set
  static chc_sett m_empty_set;

public:
  chc_db() {}

  void add_state_pred(const symbol_exprt & state) { m_state_preds.insert(state); }
  const std::set<symbol_exprt> &get_state_preds() { return m_state_preds; }
  bool has_state_pred(const symbol_exprt & state) const { return m_state_preds.count(state) > 0; }

  void build_indices();
  void reset_indices();

  const std::set<const horn_clause *> & use(const exprt & state) const {
    auto it = m_body_idx.find(state);
    if (it == m_body_idx.end())
      return m_empty_set;
    return it->second;
  }

  const std::set<const horn_clause *> & def(const exprt & state) const {
    auto it = m_head_idx.find(state);
    if (it == m_head_idx.end())
      return m_empty_set;
    return it->second;
  }

  void add_clause(const forall_exprt & f)
  {
    if (f.is_true())
      return;
    for (auto & c : m_clauses) {
      if (c.get_chc()==f) return;
    }
    m_clauses.push_back(horn_clause(f));
    reset_indices();
  }

  chcst::iterator begin() { return m_clauses.begin(); }
  chcst::iterator end() { return m_clauses.end(); }
  chcst::const_iterator begin() const { return m_clauses.begin(); }
  chcst::const_iterator end() const { return m_clauses.end(); }
};

template <typename OutputIterator>
void horn_clause::used_relations(chc_db &db, OutputIterator out) const
{
  const exprt *body = this->body();
  if (body == nullptr) return;
  std::set<symbol_exprt> symbols = find_symbols(*body);

  chc_db::is_state_pred filter(db);
  for (auto & symb : symbols) {
    if (filter(symb)) {
      *out = symb;
    }
  }
}

template <typename OutputIterator>
void horn_clause::used_func_app(chc_db &db, OutputIterator out) const
{
  const exprt *body = this->body();
  if (body == nullptr) return;

  std::set<function_application_exprt> funcs;
  body->visit_pre([&funcs](const exprt &expr) {
                     if (can_cast_expr<function_application_exprt>(expr))
                     {
                       const function_application_exprt & f = to_function_application_expr(expr);
                       funcs.insert(f);
                     }
                   });

  chc_db::is_state_pred filter(db);
  for (auto & f : funcs) {
    if (filter(to_symbol_expr(f.function()))) {
      *out = f;
    }
  }
}

/*
 * The CHC dependency graph.
 * Uninterpreted relations are vertices, dependency is based on clauses:
 * relations in the body have an edge to the relation in the head.
 */
class chc_graph
{
  chc_db & m_db;
  typedef std::map<exprt, std::set<exprt>> grapht;
  grapht m_incoming;
  grapht m_outgoing;
  const symbol_exprt *m_entry;

  // representing the empty set
  static std::set<exprt> m_expr_empty_set;

public:
  chc_graph(chc_db & db) : m_db(db), m_entry(nullptr) {}

  void build_graph();

  bool has_entry() const { return m_entry != nullptr; }
  const symbol_exprt *entry() const {
    INVARIANT(has_entry(), "Entry must exist.");
    return m_entry; }

  const std::set<exprt> &outgoing(const symbol_exprt &state) const {
    auto it = m_outgoing.find(state);
    if (it == m_outgoing.end())
      return m_expr_empty_set;
    return it->second;
  }

  const std::set<exprt> &incoming(const symbol_exprt &state) const {
    auto it = m_incoming.find(state);
    if (it == m_incoming.end())
      return m_expr_empty_set;
    return it->second;
  }
};

#endif //CBMC_CHC_DB_H
