//
// Created by Yakir Vizel on 5/27/24.
//

#include "chc_db.h"

#include <iostream>

chc_db::chc_sett chc_db::m_empty_set;
std::set<exprt> chc_graph::m_expr_empty_set;

void chc_db::reset_indices()
{
  m_body_idx.clear();
  m_head_idx.clear();
}

void chc_db::build_indices()
{
  reset_indices();

  for (auto &r: m_clauses) {
    if (!can_cast_expr<function_application_exprt>(*r.head()))
    {
      continue;
    }
    exprt func = to_function_application_expr(*r.head()).function();
    m_head_idx[func].insert(&r);

    std::vector<symbol_exprt> use;
    r.used_relations(*this,std::back_inserter(use));
    for (auto & symb : use)
    {
      m_body_idx[symb].insert(&r);
    }
  }
}

void chc_graph::build_graph()
{
  m_db.build_indices();

  for (auto & sp : m_db.get_state_preds())
  {
    std::set<exprt> outgoing;
    const std::set<horn_clause *> &uses = m_db.use(sp);
    for (const horn_clause *r : uses) {
      const exprt * head = r->head();
      if (can_cast_expr<function_application_exprt>(*head))
      {
        outgoing.insert(to_function_application_expr(*head).function());
      }
    }
    m_outgoing.insert(std::make_pair(sp, outgoing));

    std::set<exprt> incoming;
    const std::set<horn_clause *> &defs = m_db.def(sp);
    chc_db::is_state_pred isStatePred(m_db);
    for (const horn_clause *r : defs) {
      std::set<symbol_exprt> symbols = find_symbols(*r->body());
      for (auto & s : symbols)
        if (isStatePred(s))
          incoming.insert(s);
    }
    m_incoming.insert(std::make_pair(sp, incoming));
  }

  for (auto & sp : m_db.get_state_preds()) {
    std::string name = as_string(sp.get_identifier());

    if (name.find("SInitial") != std::string::npos && incoming(sp).size() == 0) {
      m_entry = &sp;
      break;
    }
  }
}
