//
// Created by Yakir Vizel on 7/23/24.
//

#ifndef CBMC_CHC_LARGE_STEP_H
#define CBMC_CHC_LARGE_STEP_H

#include "chc_wto.h"
#include <util/substitute_symbols.h>
#include <util/format_expr.h>

/*
 * Traverses the clauses in order and resolving all predicates (symbols)
 * that are not a head (e.g. a head of a loop).
 * This is similar to variable elimination in SAT.
 */
class resolution_visitort : public wto_element_visitort
{
private:
  chc_dbt & m_db;
  chc_dbt m_new_db;
  std::unordered_map<std::size_t, std::vector<horn_clauset>> m_def;
  std::unordered_set<std::size_t> m_heads;
  bool m_verbose;

public:
  resolution_visitort(chc_dbt & db) : m_db(db), m_verbose(false) {}

  chc_dbt &giveme_new_db() { return m_new_db; }

  virtual void visit(const wto_singletont & s)
  {
    const symbol_exprt* symb = s.get();
    eliminate(symb);
  }

  virtual void visit(const wto_componentt & comp)
  {
    const symbol_exprt* head = comp.head();
    m_heads.insert(head->hash());
    std::string str = head->get_identifier().c_str();
    std::cout << "Head: " << str << "\n";
    for (auto it = comp.begin(); it != comp.end(); it++)
    {
      it->get()->accept(this);
    }
    eliminate(head);
  }

  void populate_new_db()
  {
    std::vector<symbol_exprt> rels;
    for (auto &clause : m_db)
    {
      if(clause.is_query())
      {
        clause.used_relations(m_db, std::back_inserter(rels));
      }
    }

    std::set<std::size_t > preds_hash(m_heads.begin(), m_heads.end());
    for (auto p : rels) {
      preds_hash.insert(p.hash());
    }

    for (auto it : preds_hash)
    {
      auto c = m_def.find(it);
      INVARIANT(c != m_def.end(), "No clauses");
      for (auto clause : c->second)
        m_new_db.add_clause(clause.get_chc());
    }

    for (auto &clause : m_db)
    {
      if(clause.is_query())
      {
        m_new_db.add_clause(clause.get_chc());
      }
    }
  }

private:
  void eliminate(const symbol_exprt *symb)
  {
    for (auto idx : m_db.def(*symb))
    {
      auto & clause = m_db.get_clause(idx);
      std::vector<symbol_exprt> use;

      clause.used_relations(m_db,std::back_inserter(use));
      if (use.size() > 1) {
        throw incorrect_goto_program_exceptiont("Non-linear CHCs not supported yet");
      }

      if (clause.is_fact())
      {
        m_heads.insert(symb->hash());
        std::vector<horn_clauset> def_chcs;
        def_chcs.push_back(clause.get_chc());
        m_def.insert(std::make_pair(symb->hash(), def_chcs));
      }

      for (auto & p : use)
      {
        auto it = m_def.find(p.hash());
        std::vector<horn_clauset> def_chcs;
        if (it == m_def.end() || m_heads.find(p.hash()) != m_heads.end())
        {
          def_chcs.push_back(clause);
        }
        else
        {
          for (auto cls_it = it->second.begin(); cls_it != it->second.end(); cls_it++)
          {
            forall_exprt resolvent = resolve_clauses((*cls_it), clause);
            if (m_verbose)
              std::cout << "Result:\n" << format(resolvent) << "\n";
            def_chcs.push_back(resolvent);
          }
        }
        auto def_it = m_def.find(symb->hash());
        if (def_it == m_def.end())
          m_def.insert(std::make_pair(symb->hash(), def_chcs));
        else
        {
          auto & vec = def_it->second;
          vec.insert(vec.end(), def_chcs.begin(), def_chcs.end());
        }
      }
    }
  }

  forall_exprt resolve_clauses(const horn_clauset & c1, const horn_clauset & c2)
  {
    const exprt &body1 = *c1.body();
    const exprt &head1 = *c1.head();
    const exprt &body2 = *c2.body();
    const exprt &head2 = *c2.head();

    std::vector<function_application_exprt> use2;
    c2.used_func_app(m_db,std::back_inserter(use2));

    INVARIANT(use2.size() == 1, "Only handling linear case");
    if (use2.size() != 1)
      throw analysis_exceptiont("Resolution not possible");

    function_application_exprt & body2_pred = use2[0];

    const function_application_exprt *head1_pred = nullptr;
    if (can_cast_expr<function_application_exprt>(*c1.head()))
    {
      head1_pred = &to_function_application_expr(head1);
    }
    if (head1_pred == nullptr)
      throw analysis_exceptiont("Resolution not possible");

    if (m_verbose)
      std::cout << "Resolving: \n" << format(c1.get_chc()) << "\nAnd: \n"
                << format(c2.get_chc()) << "\n";

    std::set<symbol_exprt> all_vars(c1.get_chc().variables().begin(), c1.get_chc().variables().end());
    all_vars.insert(c2.get_chc().variables().begin(), c2.get_chc().variables().end());

    const function_application_exprt *body1_pred = nullptr;
    exprt::operandst body_ops;
    if (body1.id() == ID_and)
    {
      body1_pred = &to_function_application_expr(to_and_expr(body1).op0());
      body_ops.push_back(to_and_expr(body1).op1());
    }
    else
    {
      body1_pred = &to_function_application_expr(body1);
    }
    exprt transformed_body = (can_cast_expr<and_exprt>(body2)) ? to_and_expr(body2).op1() : true_exprt();
    exprt transformed_head = head2;

    INVARIANT(head1_pred->arguments().size() == 1, "Only one argument to predicate is assumes");
    const exprt &head_arg = head1_pred->arguments().at(0);
    const symbol_exprt & body_arg = to_symbol_expr(body2_pred.arguments().at(0));

    if ((head_arg.id() != ID_symbol) ||
       (to_symbol_expr(head_arg).get_identifier() != body_arg.get_identifier()))
    {
      std::map<irep_idt, exprt> subs;
      subs.insert(std::make_pair(body_arg.get_identifier(), head_arg));

      if(!transformed_body.is_true())
      {
        std::optional<exprt> s = substitute_symbols(subs, transformed_body);
        if(s.has_value())
          transformed_body = std::move(s.value());
      }

      std::optional<exprt> s = substitute_symbols(subs, transformed_head);
      if (s.has_value())
      {
        transformed_head = std::move(s.value());
      }
    }

    body_ops.push_back(transformed_body);
   transformed_body = and_exprt(*body1_pred, std::move(and_exprt(body_ops)));

    forall_exprt f(std::vector<symbol_exprt>(all_vars.begin(), all_vars.end()),
                   implies_exprt(std::move(transformed_body), std::move(transformed_head)));
    return f;
  }
};

#endif //CBMC_CHC_LARGE_STEP_H
