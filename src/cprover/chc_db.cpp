//
// Created by Yakir Vizel on 5/27/24.
//

#include "chc_db.h"

#include <iostream>

chc_dbt::chc_sett chc_dbt::m_empty_set;
std::unordered_set<exprt, irep_hash> chc_grapht::m_expr_empty_set;

void chc_dbt::reset_indices()
{
  m_body_idx.clear();
  m_head_idx.clear();
}

void chc_dbt::build_indices()
{
  reset_indices();

  for (std::size_t i = 0; i < m_clauses.size(); i++)
  {
    auto & r = m_clauses[i];
    if (!can_cast_expr<function_application_exprt>(*r.head()))
    {
      continue;
    }
    exprt func = to_function_application_expr(*r.head()).function();
    m_head_idx[func].insert(i);

    std::vector<symbol_exprt> use;
    r.used_relations(*this,std::back_inserter(use));
    for (auto & symb : use)
    {
      m_body_idx[symb].insert(i);
    }
  }
}

void chc_grapht::build_graph()
{
  m_db.build_indices();

  for (auto & sp : m_db.get_state_preds())
  {
    std::unordered_set<exprt, irep_hash> outgoing;
    const chc_dbt::chc_sett &uses = m_db.use(sp);
    for (auto idx: uses) {
      const horn_clauset & r = m_db.get_clause(idx);
      const exprt * head = r.head();
      if (can_cast_expr<function_application_exprt>(*head))
      {
        outgoing.insert(to_function_application_expr(*head).function());
      }
    }
    m_outgoing.insert(std::make_pair(sp, outgoing));

    std::unordered_set<exprt, irep_hash> incoming;
    const chc_dbt::chc_sett &defs = m_db.def(sp);
    chc_dbt::is_state_pred isStatePred(m_db);
    for (auto idx : defs) {
      const horn_clauset & r = m_db.get_clause(idx);
      std::set<symbol_exprt> symbols = find_symbols(*r.body());
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
