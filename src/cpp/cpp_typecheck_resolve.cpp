/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck_resolve.h"

#include <deque>

#ifdef DEBUG
#  include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/simplify_expr.h>
#include <util/std_code.h>
#include <util/symbol_table_base.h>

extern exprt try_evaluate_constexpr(
  const exprt &expr,
  const symbol_table_baset &symbol_table,
  const namespacet &ns);
#include <util/std_expr.h>
#include <util/string_constant.h>

#include <ansi-c/anonymous_member.h>
#include <ansi-c/merged_type.h>

#include "cpp_convert_type.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_parameter.h"
#include "cpp_template_qualifiers.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"

#include <algorithm>
#include <set>
#include <string>

/// \return true if any template parameter of \p template_type is a
///   variadic pack (an ellipsis parameter, [temp.variadic]).
static bool has_variadic_template_parameter(const template_typet &template_type)
{
  for(const auto &p : template_type.template_parameters())
    if(p.get_bool(ID_ellipsis))
      return true;
  return false;
}

static typet full_function_parameter_type(const exprt &param);

cpp_typecheck_resolvet::cpp_typecheck_resolvet(cpp_typecheckt &_cpp_typecheck)
  : cpp_typecheck(_cpp_typecheck),
    original_scope(nullptr) // set in resolve_scope()
{
}

void cpp_typecheck_resolvet::convert_identifiers(
  const cpp_scopest::id_sett &id_set,
  const cpp_typecheck_fargst &fargs,
  resolve_identifierst &identifiers)
{
  for(const auto &id_ptr : id_set)
  {
    const cpp_idt &identifier = *id_ptr;
    exprt e = convert_identifier(identifier, fargs);

    if(e.is_not_nil())
    {
      CHECK_RETURN(e.id() != ID_type || e.type().is_not_nil());

      identifiers.push_back(e);
    }
  }
}

void cpp_typecheck_resolvet::apply_template_args(
  resolve_identifierst &identifiers,
  const cpp_template_args_non_tct &template_args,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    exprt e = old_id;

    // [temp.arg]/2 + [temp.deduct]/8: applying the explicit template
    // arguments to a candidate may find a kind mismatch -- a non-type
    // argument supplied for a type parameter when an unrelated overload is
    // matched (resolving the by-index `std::get<0>(tuple<...>)` also
    // considers the by-type `std::get<T>(pair<...>)`, whose first parameter
    // `T` is a type, so the literal `0` is "expected type, but got
    // expression").  Such a failure removes only that candidate from the
    // overload set; it must not abort resolution of the remaining (viable)
    // candidates.  Mark the matching context so the mismatch is a silent
    // `template_arg_kind_mismatch_exceptiont`, catch it, and skip the
    // candidate.  Other failures propagate unchanged.
    try
    {
      cpp_typecheckt::template_arg_candidate_matchingt matching_guard{
        cpp_typecheck};
      apply_template_args(e, template_args, fargs);
    }
    catch(const template_arg_kind_mismatch_exceptiont &)
    {
      continue;
    }

    if(e.is_not_nil())
    {
      CHECK_RETURN(e.id() != ID_type || e.type().is_not_nil());

      identifiers.push_back(e);
    }
  }
}

namespace
{
// Save/restore for cpp_typecheck_resolvet::current_deduction_parameters
// across nested deductions.
struct deduction_parameters_guardt
{
  std::set<irep_idt> &target;
  std::set<irep_idt> saved;
  explicit deduction_parameters_guardt(std::set<irep_idt> &t)
    : target(t), saved(t)
  {
  }
  ~deduction_parameters_guardt()
  {
    target.swap(saved);
  }
};

// The identifiers of a template declaration's parameters, as registered in
// the template map by build_unassigned.
std::set<irep_idt> template_parameter_ids(const template_typet &template_type)
{
  std::set<irep_idt> ids;
  for(const auto &p : template_type.template_parameters())
  {
    if(p.id() == ID_type)
      ids.insert(p.type().get(ID_identifier));
    else
      ids.insert(p.get(ID_identifier));
  }
  return ids;
}

// C++20 concept subsumption ([temp.constr.order]).  These helpers implement the
// partial order on constraints that selects the more-constrained overload.
//
// N5008 [temp.constr.order]/1: a constraint P subsumes a constraint Q iff, for
// every disjunctive clause Pi in the disjunctive normal form of P, Pi subsumes
// every conjunctive clause Qj in the conjunctive normal form of Q; Pi subsumes
// Qj iff they share an identical atomic constraint ([temp.constr.atomic]).
// Example from the standard: A && B subsumes A; A subsumes A || B.
//
// A constraint is given as a concept name; its normal form is computed by
// expanding the concept's constraint-expression, recursing through nested
// concept references and the && / || (ID_and / ID_or) structure.  A concept
// whose body is not itself a logical combination is one atomic constraint,
// keyed by the concept name (so the same concept reached from two places is the
// same atomic, per [temp.constr.atomic]); a raw non-concept atomic expression
// is keyed by a canonical serialization (so it only matches the same text).
using constraint_clauset = std::set<std::string>;
using constraint_normalt = std::set<constraint_clauset>;

std::string concept_atom_key(const irept &e)
{
  std::string s = id2string(e.id());
  const irep_idt id = e.get(ID_identifier);
  if(!id.empty())
    s += "#" + id2string(id);
  for(const auto &sub : e.get_sub())
    s += "(" + concept_atom_key(sub) + ")";
  return s;
}

// If e is a reference to a named concept (cpp_name with template-args), return
// the concept name; otherwise the empty id.
irep_idt concept_reference_name(const exprt &e)
{
  if(e.id() != ID_cpp_name)
    return irep_idt();
  bool has_template_args = false;
  irep_idt name;
  for(const auto &sub : e.get_sub())
  {
    if(sub.id() == ID_template_args)
      has_template_args = true;
    else if(sub.id() == ID_name)
      name = sub.get(ID_identifier);
  }
  return has_template_args ? name : irep_idt();
}

// Look up a concept's constraint-expression body by its base name.
exprt concept_constraint_body(
  const symbol_table_baset &symbol_table,
  const irep_idt &name)
{
  for(const auto &entry : symbol_table.symbols)
  {
    if(
      id2string(entry.second.base_name) == id2string(name) &&
      entry.second.type.get_bool(ID_is_template) &&
      entry.second.type.id() == ID_cpp_declaration)
    {
      const cpp_declarationt &decl = to_cpp_declaration(entry.second.type);
      if(
        !decl.declarators().empty() &&
        decl.declarators().front().value().is_not_nil())
        return decl.declarators().front().value();
    }
  }
  return nil_exprt();
}

// Combine two normal forms by pairwise clause union (cross product): used for
// AND in DNF and for OR in CNF.
constraint_normalt
cross_product_union(const constraint_normalt &a, const constraint_normalt &b)
{
  constraint_normalt result;
  for(const auto &ca : a)
    for(const auto &cb : b)
    {
      constraint_clauset c = ca;
      c.insert(cb.begin(), cb.end());
      result.insert(c);
    }
  return result;
}

constraint_normalt set_union(constraint_normalt a, const constraint_normalt &b)
{
  a.insert(b.begin(), b.end());
  return a;
}

constraint_normalt
concept_normal(const symbol_table_baset &, const irep_idt &, bool dnf, int);

// Normal form of a constraint expression.  dnf selects disjunctive (true) vs
// conjunctive (false) normal form.
constraint_normalt concept_normal_expr(
  const symbol_table_baset &symbol_table,
  const exprt &e,
  bool dnf,
  int depth)
{
  if(depth > 32)
    return {{concept_atom_key(e)}};
  if((e.id() == ID_and || e.id() == ID_or) && e.operands().size() >= 2)
  {
    constraint_normalt acc =
      concept_normal_expr(symbol_table, e.operands().front(), dnf, depth + 1);
    for(std::size_t i = 1; i < e.operands().size(); ++i)
    {
      const constraint_normalt rhs =
        concept_normal_expr(symbol_table, e.operands()[i], dnf, depth + 1);
      // In DNF, AND distributes (cross product) and OR unions; in CNF the
      // roles swap.
      const bool cross = dnf ? (e.id() == ID_and) : (e.id() == ID_or);
      acc = cross ? cross_product_union(acc, rhs) : set_union(acc, rhs);
    }
    return acc;
  }
  const irep_idt cref = concept_reference_name(e);
  if(!cref.empty())
    return concept_normal(symbol_table, cref, dnf, depth + 1);
  return {{concept_atom_key(e)}};
}

constraint_normalt concept_normal(
  const symbol_table_baset &symbol_table,
  const irep_idt &name,
  bool dnf,
  int depth)
{
  if(depth > 32)
    return {{id2string(name)}};
  const exprt body = concept_constraint_body(symbol_table, name);
  // Decompose only when the body is itself a logical combination or a nested
  // concept reference; otherwise the whole concept is one atomic constraint
  // keyed by its name.
  if(
    body.is_not_nil() && (body.id() == ID_and || body.id() == ID_or ||
                          !concept_reference_name(body).empty()))
    return concept_normal_expr(symbol_table, body, dnf, depth + 1);
  return {{id2string(name)}};
}

// N5008 [temp.constr.order]/1: does the constraint named p_name subsume the
// constraint named q_name?
bool constraint_subsumes(
  const symbol_table_baset &symbol_table,
  const irep_idt &p_name,
  const irep_idt &q_name)
{
  if(p_name == q_name)
    return true; // every constraint subsumes itself
  const constraint_normalt dnf_p =
    concept_normal(symbol_table, p_name, /*dnf=*/true, 0);
  const constraint_normalt cnf_q =
    concept_normal(symbol_table, q_name, /*dnf=*/false, 0);
  for(const auto &pi : dnf_p)
    for(const auto &qj : cnf_q)
    {
      bool shares_atomic = false;
      for(const auto &atom : pi)
        if(qj.count(atom) != 0)
        {
          shares_atomic = true;
          break;
        }
      if(!shares_atomic)
        return false;
    }
  return true;
}

// True iff p_name is STRICTLY more constrained than q_name: p subsumes q but
// not vice versa.  Used to drop the less-constrained overload.
bool constraint_strictly_subsumes(
  const symbol_table_baset &symbol_table,
  const irep_idt &p_name,
  const irep_idt &q_name)
{
  if(p_name.empty() || q_name.empty() || p_name == q_name)
    return false;
  return constraint_subsumes(symbol_table, p_name, q_name) &&
         !constraint_subsumes(symbol_table, q_name, p_name);
}

// Associated-constraint normal form of a (function) template declaration: the
// conjunction of its per-parameter concept constraints (abbreviated
// `template <Concept T>`) and its requires-clause.  An empty result denotes an
// unconstrained declaration (the "true" constraint).
constraint_normalt template_constraint_normal(
  const symbol_table_baset &symbol_table,
  const cpp_declarationt &decl,
  bool dnf)
{
  std::vector<constraint_normalt> parts;
  for(const auto &p : decl.template_type().template_parameters())
  {
    const irep_idt &cc = p.get("#C_concept_constraint");
    if(!cc.empty())
      parts.push_back(concept_normal(symbol_table, cc, dnf, 0));
  }
  const irept &req = decl.template_type().find(ID_C_requires_clause);
  if(req.is_not_nil() && req.id() != ID_nil)
    parts.push_back(concept_normal_expr(
      symbol_table, static_cast<const exprt &>(req), dnf, 0));
  if(parts.empty())
    return {};
  // A declaration's associated constraints are the conjunction of its
  // constituents ([temp.constr.decl]).
  constraint_normalt acc = parts.front();
  for(std::size_t i = 1; i < parts.size(); ++i)
    acc = dnf ? cross_product_union(acc, parts[i]) : set_union(acc, parts[i]);
  return acc;
}

// normal_subsumes(DNF(P), CNF(Q)) per [temp.constr.order]/1, with the empty
// normal form treated as the "true" constraint (subsumed by anything; subsumes
// only "true").
bool normal_subsumes(
  const constraint_normalt &dnf_p,
  const constraint_normalt &cnf_q)
{
  if(cnf_q.empty())
    return true;
  if(dnf_p.empty())
    return false;
  for(const auto &pi : dnf_p)
    for(const auto &qj : cnf_q)
    {
      bool shares_atomic = false;
      for(const auto &atom : pi)
        if(qj.count(atom) != 0)
        {
          shares_atomic = true;
          break;
        }
      if(!shares_atomic)
        return false;
    }
  return true;
}

} // namespace

// True iff declaration p is STRICTLY more constrained than q ([temp.func.order]
// + [temp.constr.order]): p's associated constraints subsume q's but not the
// other way round.  External linkage: also used by the class-template
// partial-specialization search in cpp_instantiate_template.cpp
// ([temp.class.spec.match]/2 with [temp.constr.order]).
bool template_constraint_strictly_subsumes(
  const symbol_table_baset &symbol_table,
  const cpp_declarationt &p,
  const cpp_declarationt &q)
{
  const bool p_subsumes_q = normal_subsumes(
    template_constraint_normal(symbol_table, p, /*dnf=*/true),
    template_constraint_normal(symbol_table, q, /*dnf=*/false));
  const bool q_subsumes_p = normal_subsumes(
    template_constraint_normal(symbol_table, q, /*dnf=*/true),
    template_constraint_normal(symbol_table, p, /*dnf=*/false));
  return p_subsumes_q && !q_subsumes_p;
}

namespace
{

// Does this (function) template declaration carry any associated constraint?
bool template_is_constrained(const cpp_declarationt &decl)
{
  for(const auto &p : decl.template_type().template_parameters())
    if(!p.get("#C_concept_constraint").empty())
      return true;
  const irept &req = decl.template_type().find(ID_C_requires_clause);
  return req.is_not_nil() && req.id() != ID_nil;
}

// Historical constraint-name spelling of a template declaration, used only for
// the substring fallback when normal-form subsumption is inconclusive.  Mirrors
// the previous get_tmpl_concepts extraction.
std::string constraint_name_string(const cpp_declarationt &decl)
{
  for(const auto &p : decl.template_type().template_parameters())
  {
    const irep_idt &cc = p.get("#C_concept_constraint");
    if(!cc.empty())
      return id2string(cc);
  }
  const irept &req = decl.template_type().find(ID_C_requires_clause);
  if(req.is_not_nil() && req.id() != ID_nil)
  {
    std::string concepts;
    std::function<void(const irept &)> visit = [&](const irept &node)
    {
      if(node.id() == ID_name)
      {
        const irep_idt &nm = node.get(ID_identifier);
        if(!nm.empty())
        {
          if(!concepts.empty())
            concepts += "&&";
          concepts += id2string(nm);
        }
      }
      for(const auto &sub : node.get_sub())
        visit(sub);
    };
    visit(req);
    return concepts;
  }
  return {};
}
} // namespace

/// guess arguments of function templates
void cpp_typecheck_resolvet::guess_function_template_args(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  resolve_identifierst non_templates;

  // C++20 concept subsumption: when multiple templates with concept
  // constraints match, prefer the more constrained one. Filter before
  // instantiation so only the best candidate is instantiated.
  if(old_identifiers.size() > 1)
  {
    // Extract concept constraint from template parameters
    auto get_constraint = [&](const exprt &id) -> irep_idt
    {
      const typet &t =
        id.type().id() == ID_struct_tag
          ? static_cast<const typet &>(
              cpp_typecheck.follow_tag(to_struct_tag_type(id.type())))
        : id.type().id() == ID_union_tag
          ? static_cast<const typet &>(
              cpp_typecheck.follow_tag(to_union_tag_type(id.type())))
          : id.type();
      if(!t.get_bool(ID_is_template))
        return irep_idt();
      const cpp_declarationt &decl = to_cpp_declaration(t);
      for(const auto &p : decl.template_type().template_parameters())
      {
        const irep_idt &c = p.get("#C_concept_constraint");
        if(!c.empty())
          return c;
      }
      return irep_idt();
    };

    std::vector<bool> subsumed(old_identifiers.size(), false);
    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      irep_idt ci = get_constraint(old_identifiers[i]);
      if(ci.empty())
        continue;
      for(std::size_t j = 0; j < old_identifiers.size(); ++j)
      {
        if(i == j)
          continue;
        irep_idt cj = get_constraint(old_identifiers[j]);
        if(cj.empty())
          continue;
        // N5008 [temp.constr.order]/1: candidate i is the less-constrained one
        // (and is removed) when some other candidate j is strictly more
        // constrained.  Subsumption is computed on the normal forms of the
        // constraints (constraint_subsumes).  When the normal-form comparison
        // is inconclusive (e.g. a constraint we cannot fully decompose, such as
        // some library ranges concepts), fall back to the historical
        // name-substring heuristic -- but only when the correct comparison has
        // NOT shown i to be the strictly more-constrained one, so we never drop
        // the better candidate (the bug this fixes).
        if(constraint_strictly_subsumes(cpp_typecheck.symbol_table, cj, ci))
        {
          subsumed[i] = true;
        }
        else if(
          !constraint_strictly_subsumes(cpp_typecheck.symbol_table, ci, cj) &&
          ci != cj && id2string(cj).find(id2string(ci)) != std::string::npos)
        {
          subsumed[i] = true;
        }
      }
    }

    bool any_subsumed = false;
    for(bool s : subsumed)
      if(s)
        any_subsumed = true;

    if(any_subsumed)
    {
      resolve_identifierst filtered;
      for(std::size_t i = 0; i < old_identifiers.size(); ++i)
        if(!subsumed[i])
          filtered.push_back(old_identifiers[i]);
      old_identifiers.swap(filtered);
    }
  }

  // Index-based: a requires-clause rejection of a primary overload may
  // APPEND its #sfinae_alt twin for consideration (same-signature
  // overloads differing only in constraints share one symbol).
  for(std::size_t old_idx = 0; old_idx < old_identifiers.size(); ++old_idx)
  {
    const exprt old_id = old_identifiers[old_idx];
    // N5008 [temp.deduct.guide]/1: deduction guides are not found by name
    // lookup and are not functions; they are used only when forming the set of
    // implied class-template-argument-deduction candidates
    // ([over.match.class.deduct]), never in ordinary overload resolution.  A
    // guide parses like a constructor of the class-template name, so a guide
    // such as `tuple(U...) -> tuple<>` shares the name `tuple` and would
    // otherwise be picked up here and (mis-)instantiated as a regular function
    // template.  Class template argument deduction has its own, separate guide
    // handling (deduce_class_template_arguments), so skip guides here.
    {
      const irep_idt cand_id = old_id.id() == ID_symbol
                                 ? to_symbol_expr(old_id).get_identifier()
                                 : old_id.get(ID_identifier);
      if(!cand_id.empty())
      {
        const symbolt *cand_sym = cpp_typecheck.symbol_table.lookup(cand_id);
        if(cand_sym != nullptr && cand_sym->type.id() == ID_cpp_declaration)
        {
          const cpp_declarationt &cand_decl =
            to_cpp_declaration(cand_sym->type);
          if(
            !cand_decl.declarators().empty() &&
            cand_decl.declarators().front().get_bool("#is_deduction_guide"))
          {
            continue;
          }
        }
      }
    }

    // [temp.deduct]/3 and [temp.deduct]/8: a substitution failure
    // while deducing this candidate is a SFINAE failure — discard
    // the candidate and continue with the next one.  The
    // `sfinae_contextt` guard suppresses diagnostics for the
    // duration of the substitution and rolls the error count back
    // on exit, including when leaving via `throw 0`.
    exprt e;
    {
      sfinae_contextt sfinae_guard{cpp_typecheck};
      // [temp.deduct]/8: substitution/conversion failures while deducing
      // THIS candidate's template arguments remove the candidate; the
      // matching guard routes them into silent kind-mismatch throws.
      cpp_typecheckt::template_arg_candidate_matchingt matching_guard{
        cpp_typecheck};
      try
      {
        e = guess_function_template_args(old_id, fargs);
      }
      catch(...)
      {
        continue;
      }
    }

    if(e.is_not_nil())
    {
      CHECK_RETURN(e.id() != ID_type);

      // C++20: check concept constraint satisfaction
      bool concept_ok = true;
      {
        irep_idt tmpl_id = old_id.get(ID_identifier);
        if(tmpl_id.empty() && old_id.id() == ID_symbol)
          tmpl_id = to_symbol_expr(old_id).get_identifier();
        const auto *tmpl_sym = cpp_typecheck.symbol_table.lookup(tmpl_id);
        if(tmpl_sym && tmpl_sym->type.get_bool(ID_is_template))
        {
          const cpp_declarationt &tdecl = to_cpp_declaration(tmpl_sym->type);
          for(const auto &p : tdecl.template_type().template_parameters())
          {
            const irep_idt &cc = p.get("#C_concept_constraint");
            if(cc.empty())
              continue;
            // Get the deduced type from fargs
            typet actual_type;
            if(!fargs.operands.empty())
              actual_type = fargs.operands[0].type();
            if(actual_type.is_nil())
              break;
            // Look up concept definition
            for(const auto &entry : cpp_typecheck.symbol_table)
            {
              if(
                id2string(entry.second.base_name) != id2string(cc) ||
                !entry.second.type.get_bool(ID_is_template))
                continue;
              const cpp_declarationt &concept_decl =
                to_cpp_declaration(entry.second.type);
              if(concept_decl.declarators().empty())
                break;
              const exprt &cval = concept_decl.declarators()[0].value();
              if(cval.is_nil())
                break;
              // Get concept parameter name
              irep_idt cparam;
              for(const auto &cp :
                  concept_decl.template_type().template_parameters())
              {
                if(cp.id() == ID_type)
                {
                  const std::string cid =
                    id2string(cp.type().get(ID_identifier));
                  auto pos = cid.rfind("::");
                  cparam = pos != std::string::npos
                             ? irep_idt{cid.substr(pos + 2)}
                             : irep_idt{cid};
                  break;
                }
              }
              if(cparam.empty())
                break;
              // Evaluate the concept definition with the actual type.
              // Resolve a type from a cpp_name node.
              auto resolve_type = [&](const irept &node) -> typet
              {
                if(node.id() == ID_cpp_name)
                {
                  for(const auto &s : node.get_sub())
                    if(s.id() == ID_name && s.get(ID_identifier) == cparam)
                      return actual_type;
                }
                return typet{};
              };

              // Evaluate an expression tree directly.
              std::function<int(const irept &)> eval =
                [&](const irept &node) -> int
              {
                // -1 = unknown, 0 = false, 1 = true
                if(node.id() == ID_and)
                {
                  for(const auto &sub : node.get_sub())
                  {
                    int v = eval(sub);
                    if(v == 0)
                      return 0;
                    if(v == -1)
                      return -1;
                  }
                  return 1;
                }
                if(node.id() == ID_or)
                {
                  bool any_unknown = false;
                  for(const auto &sub : node.get_sub())
                  {
                    int v = eval(sub);
                    if(v == 1)
                      return 1;
                    if(v == -1)
                      any_unknown = true;
                  }
                  return any_unknown ? -1 : 0;
                }
                if(node.id() == ID_not)
                {
                  if(node.get_sub().empty())
                    return -1;
                  int v = eval(node.get_sub()[0]);
                  return v == -1 ? -1 : (v ? 0 : 1);
                }
                // sizeof(T) <= N
                if(
                  node.id() == ID_le || node.id() == ID_lt ||
                  node.id() == ID_ge || node.id() == ID_gt)
                {
                  // Try to evaluate via typecheck+simplify
                  exprt cmp = static_cast<const exprt &>(node);
                  std::function<void(irept &)> subst_types = [&](irept &n)
                  {
                    if(n.id() == ID_cpp_name)
                    {
                      for(const auto &s : n.get_sub())
                        if(s.id() == ID_name && s.get(ID_identifier) == cparam)
                        {
                          n = actual_type;
                          return;
                        }
                    }
                    for(auto &sub : n.get_sub())
                      subst_types(sub);
                    for(auto &named : n.get_named_sub())
                      subst_types(named.second);
                  };
                  subst_types(cmp);
                  try
                  {
                    cpp_typecheck.typecheck_expr(cmp);
                    simplify(cmp, cpp_typecheck);
                    if(cmp.is_true())
                      return 1;
                    if(cmp.is_false())
                      return 0;
                  }
                  catch(...)
                  {
                  }
                  return -1;
                }
                // Type trait: side_effect(function_call)
                if(node.id() == ID_side_effect)
                {
                  const auto &subs = node.get_sub();
                  if(subs.size() >= 2 && subs[0].id() == ID_cpp_name)
                  {
                    irep_idt fname;
                    for(const auto &s : subs[0].get_sub())
                      if(s.id() == ID_name)
                        fname = s.get(ID_identifier);
                    const auto &args = subs[1].get_sub();
                    if(args.empty())
                      return -1;
                    typet arg_type = resolve_type(args[0]);
                    if(arg_type.is_nil())
                      return -1;
                    if(fname == "__is_integral")
                      return (arg_type.id() == ID_signedbv ||
                              arg_type.id() == ID_unsignedbv ||
                              arg_type.id() == ID_bool ||
                              arg_type.id() == ID_c_bool)
                               ? 1
                               : 0;
                    if(fname == "__is_floating_point")
                      return (arg_type.id() == ID_floatbv ||
                              arg_type.id() == ID_fixedbv)
                               ? 1
                               : 0;
                    if(fname == "__is_pointer")
                      return arg_type.id() == ID_pointer ? 1 : 0;
                    if(fname == "__is_signed")
                      return arg_type.id() == ID_signedbv ? 1 : 0;
                    if(fname == "__is_same")
                    {
                      if(args.size() >= 2)
                      {
                        typet t2 = resolve_type(args[1]);
                        if(!t2.is_nil())
                          return arg_type == t2 ? 1 : 0;
                      }
                      return -1;
                    }
                  }
                }
                // compound requirement: check method return type
                if(node.id() == irep_idt{"compound_requirement"})
                {
                  const irep_idt &method =
                    static_cast<const exprt &>(node).get("#method");
                  const auto &constraint = node.find("#constraint");
                  if(method.empty() || constraint.is_nil())
                    return -1;
                  if(actual_type.id() != ID_struct_tag)
                    return -1;
                  const auto &struct_type = to_struct_type(
                    cpp_typecheck.follow_tag(to_struct_tag_type(actual_type)));
                  typet return_type;
                  for(const auto &comp : struct_type.components())
                  {
                    if(
                      comp.get_base_name() == method &&
                      comp.type().id() == ID_code)
                    {
                      return_type = to_code_type(comp.type()).return_type();
                      break;
                    }
                  }
                  if(return_type.is_nil())
                    return -1;
                  // Extract expected type from constraint template args.
                  // Structure: cpp_name(name, template_args(arguments=(...)))
                  // The arguments named sub contains nodes with type subs.
                  typet expected_type;
                  for(const auto &sub : constraint.get_sub())
                  {
                    if(sub.id() == ID_template_args)
                    {
                      const auto &args = sub.find(ID_arguments);
                      if(!args.is_nil())
                      {
                        for(const auto &arg : args.get_sub())
                        {
                          const auto &t = arg.find(ID_type);
                          if(!t.is_nil())
                          {
                            expected_type = static_cast<const typet &>(t);
                            break;
                          }
                        }
                      }
                      break;
                    }
                  }
                  if(expected_type.is_nil())
                    return -1;
                  try
                  {
                    cpp_typecheck.typecheck_type(expected_type);
                  }
                  catch(...)
                  {
                    return -1;
                  }
                  return return_type == expected_type ? 1 : 0;
                }
                // typecast(true) — from requires-expression fallback
                if(node.id() == ID_typecast)
                {
                  const auto &subs = node.get_sub();
                  if(!subs.empty())
                    return eval(subs[0]);
                }
                if(node.id() == ID_constant)
                {
                  const auto &val = static_cast<const exprt &>(node);
                  if(val.is_true())
                    return 1;
                  if(val.is_false())
                    return 0;
                }
                return -1;
              };

              int result = eval(cval);
              if(result == 0)
                concept_ok = false;
              break;
            }
            break;
          }
        }
      }

      // [temp.deduct]/5 with [temp.constr.decl]/1: after deducing this
      // function-template specialization, its associated constraints (the
      // requires-clause) must be satisfied by the deduced arguments;
      // otherwise the candidate is removed.  The concept_ok check above
      // only handles a concept written on a template *parameter*
      // (#C_concept_constraint, e.g. template<integral T>); it does not
      // cover a requires-clause (template<typename T> requires C<T>), which
      // is stored on the template_type.  Without this, e.g. a constrained
      // templated constructor `C(T) requires integral<T>` would wrongly be
      // viable with T deduced as a class type, yielding a bogus by-value
      // `C(C)` whose argument materialisation re-invokes the same
      // construction without bound (cf. libstdc++ __max_size_type /
      // __max_diff_type).
      bool requires_ok = true;
      if(
        concept_ok && e.id() == ID_template_function_instance &&
        e.type().find(ID_C_template_arguments).is_not_nil())
      {
        const symbolt *tsym =
          cpp_typecheck.symbol_table.lookup(e.type().get(ID_C_template));
        if(tsym != nullptr && tsym->type.id() == ID_cpp_declaration)
        {
          const cpp_declarationt &tdecl = to_cpp_declaration(tsym->type);
          // N5008 [temp.constr.decl]/3: the associated constraints are
          // the conjunction of the template-head requires-clause and
          // the declarator's TRAILING requires-clause
          // ([dcl.decl.general]/4).
          exprt req_clause = static_cast<const exprt &>(
            tdecl.template_type().find(ID_C_requires_clause));
          if(!tdecl.declarators().empty())
          {
            const exprt &trailing = static_cast<const exprt &>(
              tdecl.declarators().front().find(ID_C_requires_clause));
            if(trailing.is_not_nil() && trailing.id() != ID_nil)
            {
              if(req_clause.is_nil() || req_clause.id() == ID_nil)
                req_clause = trailing;
              else
              {
                exprt conj(ID_and);
                conj.add_to_operands(std::move(req_clause));
                conj.add_to_operands(exprt(trailing));
                req_clause = std::move(conj);
              }
            }
          }
          if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
          {
            // Evaluate the substituted constraint inside a SFINAE context
            // ([temp.constr.atomic]/3): a failed/unsatisfied constraint is a
            // soft failure, so any diagnostics emitted while typechecking it
            // are suppressed and the error count is reset on exit.
            sfinae_contextt sfinae_guard{cpp_typecheck};
            try
            {
              // Map each (type) template parameter's short name to the
              // deduced type.  The requires-clause is a raw parsed
              // expression that still refers to the parameters by
              // cpp_name (e.g. "T"); template_map.apply only rewrites
              // typed parameter symbols, so substitute by name here.
              const auto &params = tdecl.template_type().template_parameters();
              const cpp_template_args_tct &targs =
                to_cpp_template_args_tc(e.type().find(ID_C_template_arguments));
              const auto &targ_v = targs.arguments();
              std::map<irep_idt, typet> name_to_type;
              for(std::size_t pi = 0; pi < params.size() && pi < targ_v.size();
                  ++pi)
              {
                if(params[pi].id() != ID_type)
                  continue;
                const std::string pid =
                  id2string(params[pi].type().get(ID_identifier));
                const auto pos = pid.rfind("::");
                const irep_idt sname =
                  pos != std::string::npos ? pid.substr(pos + 2) : pid;
                if(targ_v[pi].id() == ID_type)
                  name_to_type[sname] = targ_v[pi].type();
              }
              // N5008 [temp.constr.decl]/3: the associated constraints of
              // a constrained member of a class template are formed from
              // BOTH the member's and the enclosing class template's
              // parameters; after the class is instantiated, atoms may
              // still name the CLASS's parameters (libstdc++ C++20
              // pair<T1,T2>'s converting constructor requires
              // _S_constructible<...>() over T1/T2).  Map those names to
              // the class instance's arguments as well (the instance
              // symbol records them in ID_C_template /
              // ID_C_template_arguments).
              {
                const irep_idt &member_id = e.type().get(ID_C_template);
                const std::string member_str = id2string(member_id);
                // enclosing class identifier: strip the final `::member`
                // component (angle-aware) and insert the `tag-` marker
                std::size_t depth = 0, final_sep = std::string::npos;
                for(std::size_t ci = 0; ci + 1 < member_str.size(); ++ci)
                {
                  if(member_str[ci] == '<')
                    ++depth;
                  else if(member_str[ci] == '>' && depth > 0)
                    --depth;
                  else if(
                    depth == 0 && member_str[ci] == ':' &&
                    member_str[ci + 1] == ':')
                    final_sep = ci;
                }
                if(final_sep != std::string::npos)
                {
                  std::string cls = member_str.substr(0, final_sep);
                  std::size_t lt2 = cls.find('<');
                  std::size_t se2 =
                    lt2 == std::string::npos ? std::string::npos : lt2;
                  std::size_t sep2 = cls.rfind("::", se2);
                  cls.insert(sep2 == std::string::npos ? 0 : sep2 + 2, "tag-");
                  const symbolt *class_sym =
                    cpp_typecheck.symbol_table.lookup(cls);
                  if(
                    class_sym != nullptr &&
                    class_sym->type.find(ID_C_template).is_not_nil() &&
                    class_sym->type.find(ID_C_template_arguments).is_not_nil())
                  {
                    const template_typet &class_tmpl =
                      static_cast<const template_typet &>(
                        class_sym->type.find(ID_C_template));
                    const cpp_template_args_tct &class_targs =
                      to_cpp_template_args_tc(
                        class_sym->type.find(ID_C_template_arguments));
                    const auto &cparams = class_tmpl.template_parameters();
                    const auto &cargs = class_targs.arguments();
                    for(std::size_t pi = 0;
                        pi < cparams.size() && pi < cargs.size();
                        ++pi)
                    {
                      if(cparams[pi].id() != ID_type)
                        continue;
                      const std::string pid =
                        id2string(cparams[pi].type().get(ID_identifier));
                      const auto cpos = pid.rfind("::");
                      const irep_idt sname =
                        cpos != std::string::npos ? pid.substr(cpos + 2) : pid;
                      // member parameters shadow class parameters
                      // ([temp.local]); do not overwrite
                      if(
                        cargs[pi].id() == ID_type &&
                        name_to_type.find(sname) == name_to_type.end())
                      {
                        name_to_type[sname] = cargs[pi].type();
                      }
                    }
                  }
                }
              }
              exprt req_copy = req_clause;
              std::function<void(irept &)> subst = [&](irept &n)
              {
                if(n.id() == ID_cpp_name)
                {
                  irep_idt only_name;
                  bool single = true;
                  for(const auto &s : n.get_sub())
                  {
                    if(s.id() == ID_name)
                    {
                      if(!only_name.empty())
                        single = false;
                      only_name = s.get(ID_identifier);
                    }
                    else
                      single = false;
                  }
                  if(single)
                  {
                    auto it = name_to_type.find(only_name);
                    if(it != name_to_type.end())
                    {
                      n = it->second;
                      return;
                    }
                  }
                }
                for(auto &sub : n.get_sub())
                  subst(sub);
                for(auto &named : n.get_named_sub())
                  subst(named.second);
              };
              subst(req_copy);
              // [expr.prim.req.general]/2: bind the requirement-parameters of
              // any requires-expression in the clause as local symbols, so
              // their uses (e.g. `a` in `requires(T a){ a + a; }`) resolve
              // while the constraint is checked.  A named concept binds these
              // during its own instantiation; a requires-expression used
              // DIRECTLY as a function template's requires-clause reaches here
              // without that binding, so `a + a` would otherwise fail to
              // resolve and the (satisfied) constraint be wrongly rejected.
              // Scope-restored by req_save_scope below.
              cpp_save_scopet req_save_scope(cpp_typecheck.cpp_scopes);
              std::function<void(const irept &)> bind_req_params =
                [&](const irept &node)
              {
                const irept &rp = node.find("#requires_params");
                for(const auto &param : rp.get_sub())
                {
                  const irep_idt pname = param.get(ID_name);
                  if(pname.empty())
                    continue;
                  typet ptype = static_cast<const typet &>(param.find(ID_type));
                  try
                  {
                    cpp_typecheck.typecheck_type(ptype);
                  }
                  catch(...)
                  {
                  }
                  const irep_idt id = "requires_param::" + id2string(pname);
                  if(!cpp_typecheck.symbol_table.has_symbol(id))
                  {
                    symbolt psym{id, ptype, ID_cpp};
                    psym.base_name = pname;
                    psym.is_lvalue = true;
                    cpp_typecheck.symbol_table.add(psym);
                  }
                  else
                    cpp_typecheck.symbol_table.get_writeable_ref(id).type =
                      ptype;
                  cpp_idt &sc =
                    cpp_typecheck.cpp_scopes.current_scope().insert(pname);
                  sc.identifier = id;
                  sc.id_class = cpp_idt::id_classt::SYMBOL;
                }
                for(const auto &s : node.get_sub())
                  bind_req_params(s);
                for(const auto &ns : node.get_named_sub())
                  bind_req_params(ns.second);
              };
              bind_req_params(req_copy);
              // Keep a substituted-but-untypechecked copy: if the
              // whole-clause type-check throws, the tri-state evaluator
              // below can still decide the clause per atom (its call-atom
              // path prepares deferred callee bodies and type-checks in
              // the candidate's class scope).  N5008
              // [temp.constr.atomic]/3 makes a genuine substitution
              // failure "not satisfied"; without this retry a throw kept
              // the candidate alive -- libstdc++ pair's converting
              // constructor with a literal 0 argument threw on first
              // evaluation exactly this way and beat the viable const-ref
              // constructor, corrupting every _M_get_insert_*_pos result
              // in std::map.  A throw the evaluator cannot decide keeps
              // the candidate (previous behaviour) since wholesale
              // rejection broke valid concept-using code.
              const exprt req_substituted = req_copy;
              bool whole_clause_typecheck_failed = false;
              try
              {
                cpp_typecheck.typecheck_expr(req_copy);
                // Constant-fold the substituted constraint so atomic
                // constraints written with type traits (e.g.
                // `!is_convertible_v<U, size_type>`) collapse to a boolean
                // constant.  typecheck_expr resolves the trait's `::value` to
                // a comparison such as notequal(1, 0) but does not fold it;
                // without this the tri-state eval below sees an opaque
                // comparison, returns "unknown", and wrongly keeps a candidate
                // whose requires-clause is actually unsatisfied (e.g. the
                // libstdc++ span(_It, _End) iterator-sentinel constructor stays
                // viable for span(ptr, count), is selected, and its `__last -
                // __first` body is ill-formed).
                simplify(req_copy, cpp_typecheck);
              }
              catch(...)
              {
                req_copy = req_substituted;
                whole_clause_typecheck_failed = true;
              }
              // [temp.constr.op]: tri-state evaluation of the constraint's
              // boolean structure (1 satisfied, 0 unsatisfied, -1 unknown).
              // typecheck_expr folds atomic constraints to constants but
              // leaves the &&/|| structure, so a single is_false() check
              // misses e.g. or(false, false).  Reject only on a definite
              // 'unsatisfied'; keep the candidate when unknown.
              const bool clause_mentions_concepts =
                id2string(e.type().get(ID_C_template)).find("#concept_") !=
                std::string::npos;
              std::function<int(const exprt &)> eval =
                [&](const exprt &x) -> int
              {
                if(x.is_true())
                  return 1;
                if(x.is_false())
                  return 0;
                // N5008 [temp.constr.atomic]/1: the atom is contextually
                // converted to bool.  A folded trait member such as
                // bool_constant<...>::value is a constant of type c_bool
                // (or another integral type), which is_true/is_false do
                // not recognize -- previously this made a definitively
                // FALSE clause "unknown", keeping an unsatisfiable
                // overload (libstdc++ pair's converting constructor with
                // a literal 0 argument) that then beat the viable one.
                // Trust such constants only when the candidate's
                // constraints mention no concept-ids: concept evaluation
                // still error-recovers into bogus zero constants under
                // the SFINAE guard (the std::span constructors), so a
                // concept-tainted 0 must stay "unknown".
                if(
                  !clause_mentions_concepts && x.is_constant() &&
                  (x.type().id() == ID_c_bool || x.type().id() == ID_signedbv ||
                   x.type().id() == ID_unsignedbv))
                {
                  return to_constant_expr(x).is_zero() ? 0 : 1;
                }
                if(x.id() == ID_and)
                {
                  int r = 1;
                  for(const auto &o : x.operands())
                  {
                    const int v = eval(o);
                    if(v == 0)
                      return 0;
                    if(v == -1)
                      r = -1;
                  }
                  return r;
                }
                if(x.id() == ID_or)
                {
                  int r = 0;
                  for(const auto &o : x.operands())
                  {
                    const int v = eval(o);
                    if(v == 1)
                      return 1;
                    if(v == -1)
                      r = -1;
                  }
                  return r;
                }
                if(x.id() == ID_not && x.operands().size() == 1)
                {
                  const int v = eval(to_not_expr(x).op());
                  return v == -1 ? -1 : (v == 0 ? 1 : 0);
                }
                if(x.id() == ID_typecast && x.operands().size() == 1)
                  return eval(to_typecast_expr(x).op());
                if(x.id() == ID_symbol)
                {
                  const symbolt *s = cpp_typecheck.symbol_table.lookup(
                    to_symbol_expr(x).get_identifier());
                  if(
                    s != nullptr && s->is_macro && s->value.is_not_nil() &&
                    s->value.id() != ID_symbol)
                    return eval(s->value);
                }
                // [temp.constr.atomic]: an atomic constraint is a
                // constant expression; a clause like libstdc++ C++20
                // pair's `requires (_S_constructible<_U1, _U2>())` calls
                // a consteval static member.  The structural cases above
                // cannot fold a CALL, so type-check and constant-fold the
                // substituted atom in the candidate's class scope inside
                // a SFINAE context.  Failures (or a non-constant result)
                // stay "unknown" and keep the candidate ([temp.constr.
                // atomic]/3 makes unsatisfaction soft here anyway).
                // After a whole-clause type-check failure the clause is
                // the raw substituted parse tree; only CALL atoms are
                // safe to fold there (a bare cpp_name may be a
                // concept-id, whose error recovery yields a bogus
                // constant -- the std::span constructors' clauses).
                if(
                  x.id() == ID_side_effect || x.id() == ID_function_call ||
                  x.id() == ID_cpp_name ||
                  (!whole_clause_typecheck_failed &&
                   (x.id() == ID_equal || x.id() == ID_notequal)))
                {
                  try
                  {
                    sfinae_contextt atom_sfinae{cpp_typecheck};
                    cpp_save_scopet atom_scope{cpp_typecheck.cpp_scopes};
                    const std::string ctor_id =
                      id2string(e.type().get(ID_C_template));
                    // enclosing class of the member template: strip the
                    // final `::member` component (angle-aware) and insert
                    // the `tag-` marker
                    std::size_t depth = 0, final_sep = std::string::npos;
                    for(std::size_t ci = 0; ci + 1 < ctor_id.size(); ++ci)
                    {
                      if(ctor_id[ci] == '<')
                        ++depth;
                      else if(ctor_id[ci] == '>' && depth > 0)
                        --depth;
                      else if(
                        depth == 0 && ctor_id[ci] == ':' &&
                        ctor_id[ci + 1] == ':')
                        final_sep = ci;
                    }
                    if(final_sep != std::string::npos)
                    {
                      std::string cls = ctor_id.substr(0, final_sep);
                      std::size_t lt2 = cls.find('<');
                      std::size_t se2 =
                        lt2 == std::string::npos ? std::string::npos : lt2;
                      std::size_t sep2 = cls.rfind("::", se2);
                      cls.insert(
                        sep2 == std::string::npos ? 0 : sep2 + 2, "tag-");
                      auto sc_it = cpp_typecheck.cpp_scopes.id_map.find(cls);
                      if(sc_it != cpp_typecheck.cpp_scopes.id_map.end())
                        cpp_typecheck.cpp_scopes.go_to(
                          static_cast<cpp_scopet &>(*sc_it->second));
                    }
                    exprt atom = x;
                    // [temp.constr.atomic]/1 + [expr.const]: an atomic
                    // constraint's expression is manifestly constant-
                    // evaluated; type-check it in a constant-expression
                    // context so the constexpr call evaluator folds a
                    // call atom (e.g. pair's _S_constructible<...>()).
                    //
                    // Only TRUST the folded value when the type-check
                    // produced no (recovered) diagnostics: an atom over
                    // constructs CBMC cannot model (e.g. a concept-id
                    // like std::contiguous_iterator in std::span's
                    // constructors) may error-recover into a bogus
                    // constant, wrongly removing a viable candidate.
                    // Errors here are soft ([temp.constr.atomic]/3
                    // SFINAE), but the RESULT is then "unknown".
                    const std::size_t atom_errors_before =
                      cpp_typecheck.get_message_handler().get_message_count(
                        messaget::M_ERROR);
                    {
                      cpp_typecheckt::constant_expression_contextt
                        constant_guard{cpp_typecheck};
                      cpp_typecheck.typecheck_expr(atom);
                    }
                    const bool atom_clean =
                      cpp_typecheck.get_message_handler().get_message_count(
                        messaget::M_ERROR) == atom_errors_before;
                    simplify(atom, cpp_typecheck);
                    if(atom_clean)
                    {
                      if(atom.is_true())
                        return 1;
                      if(atom.is_false())
                        return 0;
                      // a folded call returns `bool` spelled as c_bool
                      // ([basic.fundamental]); its constant value is a
                      // bit pattern, which is_true/is_false do not
                      // recognize
                      if(atom.is_constant() && atom.type().id() == ID_c_bool)
                        return to_constant_expr(atom).is_zero() ? 0 : 1;
                    }
                  }
                  catch(...)
                  {
                    // N5008 [temp.constr.atomic]/3: if substitution of
                    // the mapped arguments into the atomic constraint
                    // fails, the constraint is NOT satisfied.  A THROW
                    // from type-checking the substituted concept-id
                    // atom is exactly that substitution failure (e.g.
                    // common_reference_with<T,U> whose
                    // common_reference_t<T,U> names no ::type) -- the
                    // constrained overload must lose, not win by
                    // "unknown".  CBMC-side modelling gaps instead
                    // error-recover (diagnostics + continue), which the
                    // atom_clean gate above already maps to "unknown",
                    // so genuine gaps still keep the candidate.
                    if(x.id() == ID_cpp_name)
                      return 0;
                  }
                }
                return -1; // unknown -- conservatively keep the candidate
              };
              if(eval(req_copy) == 0)
                requires_ok = false;
            }
            catch(...)
            {
            }
          }
        }
      }

      if(concept_ok && requires_ok)
      {
        identifiers.push_back(e);
      }
      else if(!requires_ok)
      {
        // N5008 [over.match.viable]/3 + [temp.constr.decl]: an overload
        // whose associated constraints are not satisfied is removed --
        // but a SAME-SIGNATURE twin differing only in constraints
        // shares this symbol as its #sfinae_alt; give it its own turn
        // ([over.match.funcs]: each declared overload participates).
        const irep_idt tmpl_name = e.type().get(ID_C_template);
        auto alt_it2 = cpp_typecheck.sfinae_alternatives.find(tmpl_name);
        if(alt_it2 != cpp_typecheck.sfinae_alternatives.end())
        {
          const irep_idt alt_name = id2string(tmpl_name) + "#sfinae_alt";
          if(!cpp_typecheck.symbol_table.has_symbol(alt_name))
            cpp_typecheck.symbol_table.insert(alt_it2->second);
          exprt alt_id{ID_symbol};
          alt_id.type() = alt_it2->second.type;
          alt_id.set(ID_identifier, alt_name);
          old_identifiers.push_back(alt_id);
        }
      }
    }
    else if(old_id.id() == ID_symbol)
    {
      const irep_idt &sym_name = to_symbol_expr(old_id).get_identifier();
      auto alt_it = cpp_typecheck.sfinae_alternatives.find(sym_name);
      if(alt_it != cpp_typecheck.sfinae_alternatives.end())
      {
        // Primary overload failed SFINAE — try the alternative.
        const irep_idt &alt_name = id2string(sym_name) + "#sfinae_alt";
        if(!cpp_typecheck.symbol_table.has_symbol(alt_name))
          cpp_typecheck.symbol_table.insert(alt_it->second);
        exprt alt_id = old_id;
        alt_id.type() = alt_it->second.type;
        to_symbol_expr(alt_id).set_identifier(alt_name);
        // [temp.deduct]/8: deduction failures for the ALTERNATIVE are
        // SFINAE failures too -- discard, exactly like the primary
        // candidate loop above (the hard error otherwise escapes the
        // whole resolution, e.g. std::stoll("literal") guessing the
        // WIDE overload's alternative).
        exprt alt_e;
        {
          sfinae_contextt sfinae_guard{cpp_typecheck};
          cpp_typecheckt::template_arg_candidate_matchingt matching_guard{
            cpp_typecheck};
          try
          {
            alt_e = guess_function_template_args(alt_id, fargs);
          }
          catch(...)
          {
            alt_e.make_nil();
          }
        }
        if(alt_e.is_not_nil())
        {
          CHECK_RETURN(alt_e.id() != ID_type);
          identifiers.push_back(alt_e);
        }
      }
      else if(!old_id.type().get_bool(ID_is_template))
      {
        non_templates.push_back(old_id);
      }
    }
    else if(!old_id.type().get_bool(ID_is_template))
    {
      // N5008 [over.match.funcs] + [over.match.best]/2.4: a non-template
      // candidate must participate in overload resolution alongside
      // function-template specializations.  An implicitly-declared
      // copy/move assignment operator (and similar non-static members) is
      // represented here as a member expression rather than a symbol, so the
      // `ID_symbol` branch above would silently drop it -- leaving only a
      // converting `operator=` template and wrongly selecting it for a
      // same-type assignment `x = y`.  Collect such non-template candidates
      // too so they are disambiguated against the template specializations.
      non_templates.push_back(old_id);
    }
  }

  // Only include non-template identifiers when there are also template
  // function instances — they need to participate in disambiguation.
  // When there are no template instances, leave identifiers empty so
  // the caller falls back to the non-template resolution path.
  if(!identifiers.empty())
  {
    for(auto &nt : non_templates)
      identifiers.push_back(std::move(nt));
  }

  disambiguate_functions(identifiers, fargs);

  // there should only be one left, or we have failed to disambiguate
  if(identifiers.size() == 1)
  {
    exprt e = *identifiers.begin();

    // If a non-template identifier won disambiguation, keep it as-is.
    if(e.id() != ID_template_function_instance)
      return;

    // instantiate that one
    CHECK_RETURN(e.id() == ID_template_function_instance);

    const symbolt &template_symbol =
      cpp_typecheck.lookup(e.type().get(ID_C_template));

    const cpp_template_args_tct &template_args =
      to_cpp_template_args_tc(e.type().find(ID_C_template_arguments));

    // Let's build the instance.

    // For template constructors in instantiated template classes,
    // pre-populate the template map with the class template arguments.
    cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);
    const irep_idt &inst_class_tag = e.type().get(ID_C_class);
    if(!inst_class_tag.empty())
    {
      const symbolt *class_sym =
        cpp_typecheck.symbol_table.lookup(inst_class_tag);
      // Primary-template instances only: for a PARTIAL SPECIALIZATION
      // instance, ID_C_template holds the specialization's own
      // parameter list while ID_C_template_arguments holds the
      // PRIMARY template's argument list ([temp.spec.partial]) --
      // pairing them positionally binds garbage (e.g. _Types :=
      // tuple<int> instead of {int} for
      // tuple_element<__i, tuple<_Types...>>).
      if(
        class_sym != nullptr &&
        class_sym->type.find(ID_C_template).is_not_nil() &&
        class_sym->type.find(ID_C_template_arguments).is_not_nil() &&
        class_sym->type.get(ID_specialization_of).empty())
      {
        cpp_typecheck.template_map.build(
          static_cast<const template_typet &>(
            class_sym->type.find(ID_C_template)),
          static_cast<const cpp_template_args_tct &>(
            class_sym->type.find(ID_C_template_arguments)));
      }
    }

    // N5008 [temp.variadic]/5,8: replay the deduction-time pack bindings
    // recorded on the pseudo-instance (multi-pack member templates, e.g.
    // std::pair's piecewise constructor and its delegation target with
    // non-type index packs).  The template map active during deduction has
    // been unwound by now; without this the instantiation below rebuilds
    // the packs from the flat argument list, which cannot encode the split
    // between the packs (template_mapt::build then keeps whatever pack
    // state is current -- see its n_packs > 1 branch).
    {
      const irept &packs = e.type().find("#deduced_packs");
      for(const auto &entry : packs.get_sub())
      {
        const irep_idt pid = entry.get(ID_identifier);
        if(entry.id() == ID_expression)
        {
          // non-type pack: element VALUES
          std::vector<exprt> vals;
          for(const auto &v : entry.get_sub())
            vals.push_back(static_cast<const exprt &>(v));
          cpp_typecheck.template_map.pack_size_map[pid] = vals.size();
          if(!vals.empty())
          {
            cpp_typecheck.template_map.pack_expr_map[pid] = vals;
            cpp_typecheck.template_map.expr_map[pid] = vals.front();
          }
          continue;
        }
        std::vector<typet> elems;
        for(const auto &t : entry.get_sub())
          elems.push_back(static_cast<const typet &>(t));
        cpp_typecheck.template_map.pack_size_map[pid] = elems.size();
        cpp_typecheck.template_map.pack_args_map[pid] = elems;
        if(!elems.empty())
          cpp_typecheck.template_map.type_map[pid] = elems.front();
      }
    }

    const symbolt &new_symbol = cpp_typecheck.instantiate_template(
      source_location, template_symbol, template_args, template_args);

    identifiers.clear();
    // The instantiated function may have function pointer parameters
    // with spurious ellipsis from variadic template pack expansion.
    // Check and fix the type before returning.
    typet inst_type = new_symbol.type;
    if(inst_type.id() == ID_code)
    {
      bool has_variadic_pack = false;
      const cpp_declarationt &tmpl_decl =
        to_cpp_declaration(template_symbol.type);
      for(const auto &p : tmpl_decl.template_type().template_parameters())
      {
        if(p.get_bool(ID_ellipsis))
        {
          has_variadic_pack = true;
          break;
        }
      }

      if(has_variadic_pack)
      {
        for(auto &param : to_code_type(inst_type).parameters())
        {
          if(param.type().id() == ID_pointer)
          {
            typet &base = to_pointer_type(param.type()).base_type();
            if(base.id() == ID_code)
            {
              code_typet &ct = to_code_type(base);
              if(ct.has_ellipsis())
                ct.remove_ellipsis();
            }
          }
        }

        // Expand pack parameter: the instantiated function has a single
        // parameter for the pack, but it should have N copies where N
        // is the pack size (extra template args beyond non-pack params).
        const auto &tmpl_params =
          tmpl_decl.template_type().template_parameters();
        std::size_t non_pack_count = 0;
        for(const auto &tp : tmpl_params)
        {
          if(!tp.get_bool(ID_ellipsis))
            ++non_pack_count;
        }
        std::size_t pack_size =
          template_args.arguments().size() > non_pack_count
            ? template_args.arguments().size() - non_pack_count
            : 0;

        // N5008 [temp.variadic]/4-5: with MORE THAN ONE template parameter
        // pack (e.g. `template<unsigned long... Uf, class... Up>
        // impl(indices<Uf...>, Up...)`), the flat argument count minus the
        // non-pack parameters lumps ALL packs together, overestimating the
        // FUNCTION parameter pack's arity (it corresponds to one specific
        // template pack).  The deduction-time bindings replayed above
        // (#deduced_packs) record each pack's own arity by full identifier;
        // subtract the leading packs' arities so `pack_size` is the arity
        // of the LAST pack (the one a trailing function parameter pack
        // expands, as in the libc++/libstdc++ shapes).  If a leading
        // pack's arity is unrecorded, leave the expansion alone
        // (conservative: instantiate_template has already expanded
        // correctly-shaped instances).
        {
          std::vector<irep_idt> pack_ids;
          for(const auto &tp : tmpl_params)
          {
            if(!tp.get_bool(ID_ellipsis))
              continue;
            pack_ids.push_back(
              tp.id() == ID_type ? tp.type().get(ID_identifier)
                                 : tp.get(ID_identifier));
          }
          if(pack_ids.size() > 1)
          {
            bool all_known = true;
            std::size_t leading_arity = 0;
            for(std::size_t k = 0; k + 1 < pack_ids.size(); ++k)
            {
              const irep_idt &pid = pack_ids[k];
              auto ta = cpp_typecheck.template_map.pack_args_map.find(pid);
              auto te = cpp_typecheck.template_map.pack_expr_map.find(pid);
              auto ts = cpp_typecheck.template_map.pack_size_map.find(pid);
              if(ta != cpp_typecheck.template_map.pack_args_map.end())
                leading_arity += ta->second.size();
              else if(te != cpp_typecheck.template_map.pack_expr_map.end())
                leading_arity += te->second.size();
              else if(ts != cpp_typecheck.template_map.pack_size_map.end())
                leading_arity += ts->second;
              else
                all_known = false;
            }
            if(all_known && pack_size >= leading_arity)
              pack_size -= leading_arity;
            else if(!all_known)
              pack_size = 0; // unknown split: do not expand
          }
        }

        // N5008 [temp.variadic]/4-5: only a genuine *function parameter pack*
        // -- a function parameter declared with a top-level `...`, e.g.
        // `_U... args` -- expands into N function parameters.  A parameter
        // whose type merely *contains* the pack nested inside a template-
        // argument expansion (e.g. `Base<0, _U...>`, deduced via the
        // derived-to-base rule [temp.deduct.call]/4.3) is a *single*
        // parameter whose type-internal pack instantiate_template already
        // expanded inside the template-argument list (to `Base<0, int, int>`);
        // duplicating it here would create a spurious extra parameter and
        // leave the instantiated function with an unbindable call.  Detect a
        // genuine function parameter pack by the top-level ellipsis on the
        // declarator/type only -- mirroring the empty-pack guard in
        // cpp_instantiate_template.cpp.
        bool has_function_param_pack = false;
        // N5008 [temp.variadic]/4: a *function* parameter pack expands to one
        // function parameter per deduced element; the positioning of that
        // expansion is determined by the FUNCTION parameter list, not the
        // template parameter list.  `non_pack_count` above counts non-pack
        // TEMPLATE parameters (used only to size the pack), which can exceed
        // the number of non-pack function parameters when a template parameter
        // is not a function parameter -- e.g. an explicit leading return-type
        // parameter `R` in `template<class R, class F, class... A> R f(F, A&&...)`
        // called as `f<int>(...)`.  Using the template count to position the
        // expansion then inserts one parameter too many.  Count the non-pack
        // function parameters (and the pack's position among them) directly.
        std::size_t func_non_pack_count = 0;
        std::size_t func_params_before_pack = 0;
        if(!tmpl_decl.declarators().empty())
        {
          const irept &fparams =
            tmpl_decl.declarators().front().type().find(ID_parameters);
          for(const auto &p : fparams.get_sub())
          {
            if(p.id() != ID_cpp_declaration)
              continue;
            bool this_is_pack = false;
            for(const auto &d : p.get_sub())
              if(
                d.id() == ID_cpp_declarator &&
                (d.find(ID_type).get_bool(ID_ellipsis) ||
                 d.get_bool(ID_ellipsis)))
                this_is_pack = true;
            if(this_is_pack)
              has_function_param_pack = true;
            else
            {
              ++func_non_pack_count;
              if(!has_function_param_pack)
                ++func_params_before_pack;
            }
          }
        }

        if(pack_size > 1 && has_function_param_pack)
        {
          auto &params = to_code_type(inst_type).parameters();
          // Find the function parameter pack and duplicate it to match the
          // pack size.  The pack sits after the non-pack function parameters
          // that precede it (and after 'this' for member functions).
          std::size_t param_offset = 0;
          if(!params.empty() && params.front().get_this())
            param_offset = 1;

          // Only expand if the parameter count doesn't already match
          // (instantiate_template may have already expanded the pack).
          std::size_t expected_params =
            func_non_pack_count + pack_size + param_offset;
          if(
            params.size() < expected_params &&
            func_params_before_pack + param_offset < params.size())
          {
            std::size_t pack_idx = func_params_before_pack + param_offset;
            code_typet::parametert pack_param = params[pack_idx];
            for(std::size_t i = 1; i < pack_size; ++i)
              params.insert(params.begin() + pack_idx + i, pack_param);

            // N5008 [temp.deduct.call]/1-4 + [temp.variadic]/4: the deduced
            // elements of a function parameter pack may have DIFFERENT types
            // (e.g. a forwarding-reference pack `A&&...` called with
            // heterogeneous lvalue arguments `call_on(i, d)` deduces
            // A = {int&, double&}).  The loop above expanded the pack into
            // `pack_size` copies of the FIRST element's parameter, which is
            // only correct for a homogeneous pack; for a forwarding-reference
            // pack it leaves later arguments unable to bind to the first
            // element's reference type (there is no implicit conversion), so
            // the call is wrongly rejected as "no match".  Assign each expanded
            // parameter the type of its corresponding deduced pack element.
            //
            // Guarded to the parameter patterns that reach this expansion and
            // for which the parameter type equals its deduced template argument
            // -- the identity pattern `A` and the forwarding reference `A&&`
            // (whose `A& &&` collapses to `A&`); for these, template argument
            // `non_pack_count + i` is exactly the i-th parameter's type.  Other
            // patterns (where the parameter merely contains `A`) keep the
            // duplicated form, so this only ever corrects a wrong homogeneous
            // expansion.
            // N5008 [temp.param]/11: the pack's template arguments start at the
            // pack's POSITION in the template parameter list, which is
            // `non_pack_count` only when the pack is the last template
            // parameter.  When further template parameters follow the pack
            // (e.g. `template<class U, class... W, class X = void>`), the pack
            // starts earlier: the leading non-pack parameters before it each
            // consume one argument.  Using `non_pack_count` there would read
            // the trailing parameters' arguments as pack elements (binding
            // e.g. `X`'s `void` into the pack), producing an ill-formed
            // parameter.  Compute the pack's argument start position directly.
            std::size_t pack_targ_start = 0;
            for(const auto &tp : tmpl_params)
            {
              if(tp.get_bool(ID_ellipsis))
                break;
              ++pack_targ_start;
            }
            if(
              pack_targ_start < template_args.arguments().size() &&
              template_args.arguments()[pack_targ_start].id() == ID_type &&
              pack_param.type() ==
                template_args.arguments()[pack_targ_start].type())
            {
              for(std::size_t i = 0; i < pack_size; ++i)
              {
                const std::size_t targ = pack_targ_start + i;
                if(
                  targ < template_args.arguments().size() &&
                  template_args.arguments()[targ].id() == ID_type)
                {
                  params[pack_idx + i].type() =
                    template_args.arguments()[targ].type();
                }
              }
            }
          }
        }
      }
    }

    identifiers.push_back(symbol_exprt(new_symbol.name, inst_type));
  }
}

void cpp_typecheck_resolvet::remove_templates(resolve_identifierst &identifiers)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    const typet &followed =
      old_id.type().id() == ID_struct_tag
        ? static_cast<const typet &>(
            cpp_typecheck.follow_tag(to_struct_tag_type(old_id.type())))
      : old_id.type().id() == ID_union_tag
        ? static_cast<const typet &>(
            cpp_typecheck.follow_tag(to_union_tag_type(old_id.type())))
      : old_id.type().id() == ID_c_enum_tag
        ? static_cast<const typet &>(
            cpp_typecheck.follow_tag(to_c_enum_tag_type(old_id.type())))
        : old_id.type();
    if(!followed.get_bool(ID_is_template))
      identifiers.push_back(old_id);
  }
}

void cpp_typecheck_resolvet::remove_duplicates(
  resolve_identifierst &identifiers)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  std::set<irep_idt> ids;
  std::set<exprt> other;

  for(const auto &old_id : old_identifiers)
  {
    irep_idt id;

    if(old_id.id() == ID_symbol)
      id = to_symbol_expr(old_id).identifier();
    else if(old_id.id() == ID_type && old_id.type().id() == ID_struct_tag)
      id = to_struct_tag_type(old_id.type()).get_identifier();
    else if(old_id.id() == ID_type && old_id.type().id() == ID_union_tag)
      id = to_union_tag_type(old_id.type()).get_identifier();

    if(id.empty())
    {
      if(other.insert(old_id).second)
        identifiers.push_back(old_id);
    }
    else
    {
      if(ids.insert(id).second)
        identifiers.push_back(old_id);
    }
  }
}

exprt cpp_typecheck_resolvet::convert_template_parameter(
  const cpp_idt &identifier)
{
#ifdef DEBUG
  std::cout << "RESOLVE MAP:\n";
  cpp_typecheck.template_map.print(std::cout);
#endif

  // look up the parameter in the template map
  exprt e = cpp_typecheck.template_map.lookup(identifier.identifier);

  // If not found, the parameter may have been registered under a different
  // template scope (e.g., forward declaration vs definition). Try matching
  // by base name.
  //
  // N5008 [temp.deduct]/2: deduction starts from a clean slate -- when the
  // EXACT identifier has an entry in the map (a nil or ID_unassigned
  // placeholder from build_unassigned), this parameter belongs to an
  // ACTIVE deduction context and its unbound state is meaningful.  The
  // by-name fallback must not then capture a same-short-name parameter of
  // an ENCLOSING instantiation: resolving the `_Alloc` of the pattern
  // `hash<vector<bool, _Alloc>>` (stl_bvector.h) through unordered_set's
  // `_Alloc = allocator<K>` instantiated a hybrid vector<bool,
  // allocator<K>> whose transitively cached, half-substituted instances
  // (e.g. a truncated __alloc_traits) later broke vector<K> for the same
  // K.  The fallback stays for identifiers wholly unknown to the map (the
  // forward-declaration-vs-definition scope mismatch it was added for).
  if(
    (e.is_nil() || (e.id() == ID_type && e.type().is_nil())) &&
    cpp_typecheck.template_map.type_map.find(identifier.identifier) ==
      cpp_typecheck.template_map.type_map.end() &&
    cpp_typecheck.template_map.expr_map.find(identifier.identifier) ==
      cpp_typecheck.template_map.expr_map.end())
  {
    const std::string id_str = id2string(identifier.identifier);
    auto pos = id_str.rfind("::");
    if(pos != std::string::npos)
    {
      const std::string base = id_str.substr(pos + 2);
      e = cpp_typecheck.template_map.lookup_by_suffix(
        base, identifier.identifier);
    }
  }

  if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
  {
    // N5008 [temp.variadic]/5,7: the identifier may name a template parameter
    // *pack* that was bound (in template_map.pack_args_map) to two or more
    // elements.  build() deliberately does not record a scalar type_map entry
    // for a multi-element type pack (that would collapse pack expansions and
    // sizeof... -- which are resolved separately via pack_args_map /
    // pack_size_map by template_mapt::apply).  But a *scalar* reference to the
    // pack's pattern (e.g. the parameter type of a function parameter pack
    // `U... args`, resolved before the parameter list is expanded into one
    // parameter per element) still reaches this lookup; for a single-element
    // pack a convenience type_map entry makes it succeed, so for consistency
    // resolve a multi-element pack here to its first element (the pattern's
    // representative type).  The actual per-element expansion of the parameter
    // list happens afterwards in guess_function_template_args.  Without this,
    // instantiating a function parameter pack of two or more (non-class)
    // elements threw, dropping the enclosing function body.
    const auto pa_it =
      cpp_typecheck.template_map.pack_args_map.find(identifier.identifier);
    if(
      pa_it != cpp_typecheck.template_map.pack_args_map.end() &&
      !pa_it->second.empty())
    {
      exprt pack_front{ID_type};
      pack_front.type() = pa_it->second.front();
      pack_front.add_source_location() = source_location;
      return pack_front;
    }
  }

  if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
  {
    // N5008 [temp.variadic]/7 + [temp.arg.explicit]/4: a parameter pack that is
    // empty in this instantiation expands to zero elements.  A scalar reference
    // to such a pack's pattern (e.g. the element type of a constructor
    // parameter pack `_Tail... __tail` whose `_Tail` is empty here) reaches
    // this lookup with pack_size_map == 0 and no pack_args_map entry.  Return
    // the empty_typet zero-length-pack sentinel (recognised downstream) instead
    // of throwing, so the surrounding parameter/argument is dropped rather than
    // aborting the whole specialization.
    const auto ps_it =
      cpp_typecheck.template_map.pack_size_map.find(identifier.identifier);
    if(
      ps_it != cpp_typecheck.template_map.pack_size_map.end() &&
      ps_it->second == 0)
    {
      exprt empty_pack{ID_type};
      empty_pack.type() = empty_typet{};
      empty_pack.add_source_location() = source_location;
      return empty_pack;
    }
    // Don't print an error message — the caller may catch the exception
    // (e.g., during SFINAE or template argument deduction).
    throw 0;
  }

  e.add_source_location() = source_location;

  return e;
}

exprt cpp_typecheck_resolvet::convert_identifier(
  const cpp_idt &identifier,
  const cpp_typecheck_fargst &fargs)
{
  if(identifier.id_class == cpp_scopet::id_classt::TEMPLATE_PARAMETER)
    return convert_template_parameter(identifier);

  exprt e;

  if(
    identifier.is_member && !identifier.is_constructor &&
    !identifier.is_static_member)
  {
    // a regular struct or union member

    const symbolt *compound_ptr =
      cpp_typecheck.symbol_table.lookup(identifier.class_identifier);
    if(!compound_ptr)
    {
      exprt nil;
      nil.make_nil();
      return nil;
    }
    const symbolt &compound_symbol = *compound_ptr;

    CHECK_RETURN(
      compound_symbol.type.id() == ID_struct ||
      compound_symbol.type.id() == ID_union);

    const struct_union_typet &struct_union_type =
      to_struct_union_type(compound_symbol.type);

    const exprt &component =
      struct_union_type.get_component(identifier.identifier);

    const typet &type = component.type();
    DATA_INVARIANT(type.is_not_nil(), "type must not be nil");

    if(identifier.id_class == cpp_scopet::id_classt::TYPEDEF)
    {
      e = type_exprt(type);
    }
    else if(identifier.id_class == cpp_scopet::id_classt::SYMBOL)
    {
      // A non-static, non-type member.
      // There has to be an object.
      e = exprt(ID_member);
      e.set(ID_component_name, identifier.identifier);
      e.add_source_location() = source_location;

      exprt object;
      object.make_nil();

#if 0
      std::cout << "I: " << identifier.class_identifier
                << " "
                << cpp_typecheck.cpp_scopes.current_scope().
                    this_class_identifier << '\n';
#endif

      const exprt &this_expr = original_scope->this_expr;

      if(fargs.has_object)
      {
        // the object is given to us in fargs
        PRECONDITION(!fargs.operands.empty());
        object = fargs.operands.front();
      }
      else if(this_expr.is_not_nil())
      {
        // use this->...
        DATA_INVARIANT(
          this_expr.type().id() == ID_pointer,
          "this argument should be pointer");
        object =
          exprt(ID_dereference, to_pointer_type(this_expr.type()).base_type());
        object.copy_to_operands(this_expr);
        object.type().set(
          ID_C_constant,
          to_pointer_type(this_expr.type())
            .base_type()
            .get_bool(ID_C_constant));
        object.set(ID_C_lvalue, true);
        object.add_source_location() = source_location;
      }

      // check if the member can be applied to the object
      if(
        (object.type().id() != ID_struct_tag &&
         object.type().id() != ID_union_tag) ||
        !has_component_rec(object.type(), identifier.identifier, cpp_typecheck))
      {
        // failed
        object.make_nil();
      }

      if(object.is_not_nil())
      {
        // we got an object
        e.add_to_operands(std::move(object));

        bool old_value = cpp_typecheck.disable_access_control;
        cpp_typecheck.disable_access_control = true;
        cpp_typecheck.typecheck_expr_member(e);
        cpp_typecheck.disable_access_control = old_value;
      }
      else if(
        compound_symbol.type.id() == ID_union &&
        compound_symbol.type.find(ID_C_unnamed_object).is_not_nil())
      {
        // Anonymous union member: access through the unnamed object
        // variable rather than through 'this'.
        const irep_idt &unnamed_obj =
          compound_symbol.type.get(ID_C_unnamed_object);
        const symbolt *anon_sym =
          cpp_typecheck.symbol_table.lookup(unnamed_obj);
        if(anon_sym == nullptr)
        {
          // Try with scope prefix
          for(cpp_scopet *s = &cpp_typecheck.cpp_scopes.current_scope();
              !s->is_root_scope();
              s = &s->get_parent())
          {
            anon_sym = cpp_typecheck.symbol_table.lookup(
              id2string(s->prefix) + id2string(unnamed_obj));
            if(anon_sym != nullptr)
              break;
          }
        }
        if(anon_sym != nullptr)
        {
          exprt anon_obj = anon_sym->symbol_expr();
          anon_obj.set(ID_C_lvalue, true);
          e.add_to_operands(std::move(anon_obj));
          e.type() = type;
          bool old_value = cpp_typecheck.disable_access_control;
          cpp_typecheck.disable_access_control = true;
          cpp_typecheck.typecheck_expr_member(e);
          cpp_typecheck.disable_access_control = old_value;
        }
        else
        {
          e.id(ID_ptrmember);
          tag_typet class_tag_type{ID_union_tag, identifier.class_identifier};
          e.copy_to_operands(exprt("cpp-this", pointer_type(class_tag_type)));
          e.type() = type;
        }
      }
      else
      {
        // this has to be a method or form a pointer-to-member expression
        if(identifier.is_method)
        {
          const symbolt *sym_ptr =
            cpp_typecheck.symbol_table.lookup(identifier.identifier);
          if(!sym_ptr)
          {
            e.make_nil();
          }
          else
          {
            e = cpp_symbol_expr(*sym_ptr);
          }
        }
        else
        {
          e.id(ID_ptrmember);
          tag_typet class_tag_type{
            compound_symbol.type.id() == ID_struct ? ID_struct_tag
                                                   : ID_union_tag,
            identifier.class_identifier};
          e.copy_to_operands(exprt("cpp-this", pointer_type(class_tag_type)));
          e.type() = type;
        }
      }
    }
  }
  else
  {
    const symbolt *sym_ptr =
      cpp_typecheck.symbol_table.lookup(identifier.identifier);
    if(!sym_ptr)
    {
      exprt nil;
      nil.make_nil();
      return nil;
    }
    const symbolt &symbol = *sym_ptr;

    if(symbol.is_type)
    {
      e.make_nil();

      if(symbol.is_macro) // includes typedefs
      {
        // Phase 4 caller for typedef symbols per N5008
        // [temp.inst]/3.1: when the resolver hands a typedef back
        // out, drive on-demand resolution of the typedef's alias
        // type if the producer marked it lazy.  The helper itself
        // guards against re-entry into a class still being
        // typechecked, so calling it unconditionally is safe.
        if(symbol.type.get_bool(ID_C_lazy_member_type))
        {
          symbolt *writeable_sym =
            cpp_typecheck.symbol_table.get_writeable(symbol.name);
          if(writeable_sym != nullptr)
            cpp_typecheck.try_resolve_lazy_typedef_symbol(*writeable_sym);
        }
        e = type_exprt(symbol.type);
        PRECONDITION(symbol.type.is_not_nil());
      }
      else if(symbol.type.id() == ID_c_enum)
      {
        e = type_exprt(c_enum_tag_typet(symbol.name));
      }
      else if(symbol.type.id() == ID_struct)
      {
        e = type_exprt(struct_tag_typet(symbol.name));
      }
      else if(symbol.type.id() == ID_union)
      {
        e = type_exprt(union_tag_typet(symbol.name));
      }
    }
    else if(symbol.is_macro)
    {
      if(symbol.type.id() == ID_code)
      {
        // constexpr function
        e = cpp_symbol_expr(symbol);
      }
      else if(
        symbol.type.id() == ID_struct || symbol.type.id() == ID_struct_tag)
      {
        // constexpr struct variable: keep as symbol so it remains an
        // lvalue for member function calls (this pointer formation)
        e = cpp_symbol_expr(symbol);
      }
      else
      {
        e = symbol.value;
        if(e.is_nil())
          e = cpp_symbol_expr(symbol);
      }
    }
    else
    {
      e = cpp_symbol_expr(symbol);
    }
  }

  e.add_source_location() = source_location;

  return e;
}

void cpp_typecheck_resolvet::filter(
  resolve_identifierst &identifiers,
  const wantt want)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  for(const auto &old_id : old_identifiers)
  {
    bool match = false;

    switch(want)
    {
    case wantt::TYPE:
      match = (old_id.id() == ID_type);
      break;

    case wantt::VAR:
      match = (old_id.id() != ID_type);
      break;

    case wantt::BOTH:
      match = true;
      break;

    default:
      UNREACHABLE;
    }

    if(match)
      identifiers.push_back(old_id);
  }
}

/// N5008 [over.match.funcs]/5, [over.ics.ref]: for a call on a non-const
/// object, a const member function's implicit object parameter binding adds a
/// cv-qualification and ranks worse than a non-const member function's.  For a
/// member function *template* candidate that is still a
/// `template_function_instance` (the `this` parameter, with its const member
/// qualifier, is added only when the template is instantiated), the deduced
/// function type carries no `this` parameter, so `disambiguate_functions`
/// cannot see the const member-qualifier and ranks the const and non-const
/// overloads equally -- letting the const overload be (mis)selected for a
/// non-const object.  Recover the qualifier from the candidate template's
/// declarator (`ID_method_qualifier`) and return the cv penalty that the
/// instantiated overload would have received: 1 for a const member function
/// called on a non-const object, 0 otherwise.
unsigned cpp_typecheck_resolvet::member_template_const_penalty(
  const exprt &cand,
  const cpp_typecheck_fargst &fargs)
{
  if(
    cand.id() != ID_template_function_instance || !fargs.has_object ||
    fargs.operands.empty())
    return 0;
  const irep_idt tmpl = cand.type().get(ID_C_template);
  if(tmpl.empty())
    return 0;
  const symbolt *tsym = cpp_typecheck.symbol_table.lookup(tmpl);
  if(tsym == nullptr || tsym->type.id() != ID_cpp_declaration)
    return 0;
  const cpp_declarationt &decl = to_cpp_declaration(tsym->type);
  if(decl.declarators().empty())
    return 0;
  const typet &mq = static_cast<const typet &>(
    decl.declarators().front().find(ID_method_qualifier));
  const bool member_const = cpp_typecheck.has_const(mq);
  const bool object_const =
    fargs.operands.front().type().get_bool(ID_C_constant);
  return (member_const && !object_const) ? 1 : 0;
}

void cpp_typecheck_resolvet::exact_match_functions(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  if(!fargs.in_use)
    return;

  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  identifiers.clear();

  // put in the ones that match precisely
  for(const auto &old_id : old_identifiers)
  {
    unsigned distance;
    unsigned cv_distance = 0;
    if(disambiguate_functions(old_id, distance, fargs, &cv_distance))
    {
      cv_distance += member_template_const_penalty(old_id, fargs);
      // A reference binding differing from the argument only in top-level
      // cv-qualification is an identity conversion ([over.ics.ref]); its
      // cv tie-breaker ([over.ics.rank]/3.2.6) is reported separately in
      // `cv_distance`.  A precise match still requires it to be zero, so e.g.
      // `f() const` is not a precise match for a non-const object (preserving
      // const/non-const member-function overload selection).
      if(distance + cv_distance <= 0)
        identifiers.push_back(old_id);
    }
  }
}

void cpp_typecheck_resolvet::disambiguate_functions(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  // sort according to distance
  std::multimap<std::size_t, exprt> distance_map;

  for(const auto &old_id : old_identifiers)
  {
    unsigned args_distance;
    unsigned cv_distance = 0;

    if(disambiguate_functions(old_id, args_distance, fargs, &cv_distance))
    {
      cv_distance += member_template_const_penalty(old_id, fargs);
      std::size_t template_distance = 0;

      if(!old_id.type().get(ID_C_template).empty())
        template_distance = old_id.type()
                              .find(ID_C_template_arguments)
                              .find(ID_arguments)
                              .get_sub()
                              .size();

      // [over.match.best]/1 + [over.ics.rank]: ranking is primarily by
      // the quality of the argument implicit-conversion sequences
      // (`args_distance`); preferring a non-template / fewer-template-
      // argument candidate ([over.match.best]/1, last bullet) is only a
      // tie-breaker that applies when the conversion sequences are
      // otherwise indistinguishable.  Order lexicographically with
      // `args_distance` as the high-order key and `template_distance` as
      // the low-order key, so a candidate with a strictly better ICS
      // wins regardless of template-ness.  Without this, a non-template
      // copy constructor `optional(const optional<T>&)` whose argument
      // needs a (second) user-defined conversion `T -> optional<T>`
      // (args_distance 4, template_distance 0) would beat the direct
      // converting constructor `optional(_Up&&)` with `_Up=T` (a perfect
      // match, args_distance 0, but template_distance >= 1) — violating
      // [over.best.ics] (an implicit conversion sequence contains at
      // most one user-defined conversion).
      // `cv_distance` is the lowest-order key: per [over.ics.rank]/3.2.6 the
      // top-level cv-qualification of a *reference* binding is a tie-breaker
      // applied only between reference bindings, ranked below the non-template
      // preference ([over.match.best]/2.4).  Folding it into `args_distance`
      // would let a by-value match by a constructor/operator *template* beat a
      // reference binding by the (non-template) copy/move special member --
      // e.g. selecting `operator=(_Up)` over the copy assignment for `x = y`
      // with `x`, `y` of the same class.
      std::size_t total_distance =
        // NOLINTNEXTLINE(whitespace/operators)
        1000000000ULL * args_distance + 1000 * template_distance + cv_distance;

      distance_map.insert({total_distance, old_id});
    }
  }

  old_identifiers.clear();

  // put in the top ones
  if(!distance_map.empty())
  {
    auto range = distance_map.equal_range(distance_map.begin()->first);
    for(auto it = range.first; it != range.second; ++it)
      old_identifiers.push_back(it->second);
  }

  if(old_identifiers.size() > 1 && fargs.in_use)
  {
    // [temp.deduct.partial]: when comparing two function templates,
    // a forwarding-reference parameter `T&&` is less specialized than
    // a lvalue-reference parameter `T&` when the corresponding
    // argument is an lvalue.  Inspect each candidate's
    // `C_template` field (the recorded original template signature)
    // to detect this rvalue-vs-lvalue-reference asymmetry and
    // dominate the forwarding-ref overload.  Without this, calls
    // such as `as_const(s)` (with `as_const(T&)` AND
    // `as_const(T&&) = delete` overloads — the libstdc++ pattern
    // used to forbid xvalue arguments) report
    //   symbol 'as_const' does not uniquely resolve
    // because both deduce to a `T&` parameter type after
    // reference-collapsing and CBMC's distance-based disambiguation
    // can't tell them apart.
    if(fargs.operands.size() >= 1)
    {
      // Helper to read a template parameter's reference-kind
      // from the recorded `C_template` signature: returns
      // 'L' for lvalue-ref, 'R' for rvalue-ref / forwarding-ref,
      // 'V' for by-value, 'O' for other.
      auto template_param_kind =
        [](const exprt &cand, std::size_t param_idx) -> char
      {
        if(cand.type().id() != ID_code)
          return 'O';
        const irept &tmpl = cand.type().find(ID_C_template);
        if(tmpl.id().empty())
          return 'O';
        // The template signature renders as
        //   template.NAME<...>(parameter(type=KIND(...)))->(RET)
        // where KIND is one of: reference, referencervalue_reference,
        // rvalue_reference, or absent (by-value).
        const std::string s = tmpl.pretty(0, 999);
        std::size_t pos = 0;
        for(std::size_t i = 0; i <= param_idx; ++i)
        {
          pos = s.find("parameter(type=", pos);
          if(pos == std::string::npos)
            return 'O';
          if(i < param_idx)
            pos += 1;
        }
        const std::size_t kind_start =
          pos + std::string("parameter(type=").size();
        const std::string head = s.substr(kind_start, 40);
        // Order matters: "referencervalue_reference" prefix-overlaps
        // with "reference"; check the longer variant first.
        if(head.rfind("referencervalue_reference", 0) == 0)
          return 'R';
        if(head.rfind("rvalue_reference(", 0) == 0)
          return 'R';
        if(head.rfind("reference(", 0) == 0)
          return 'L';
        return 'V';
      };

      // For each pair, check if one's first-param kind dominates the
      // other's per [temp.deduct.partial] when the call argument is
      // an lvalue.
      std::vector<bool> dominated_fwd(old_identifiers.size(), false);
      for(std::size_t i = 0; i < old_identifiers.size(); ++i)
      {
        for(std::size_t j = 0; j < old_identifiers.size(); ++j)
        {
          if(i == j || dominated_fwd[i] || dominated_fwd[j])
            continue;
          if(old_identifiers[i].type().id() != ID_code)
            continue;
          if(old_identifiers[j].type().id() != ID_code)
            continue;
          const code_typet &fi = to_code_type(old_identifiers[i].type());
          const code_typet &fj = to_code_type(old_identifiers[j].type());
          if(fi.parameters().size() != fj.parameters().size())
            continue;
          if(fi.parameters().size() != fargs.operands.size())
            continue;
          // Compare per-parameter kinds.  i is dominated by j if
          // for every parameter, i's kind is "forwarding ref" and
          // j's kind is "lvalue ref" AND the argument is an lvalue
          // — and at least one parameter has this asymmetry.
          bool i_dominated = true;
          bool any_diff = false;
          for(std::size_t p = 0; p < fi.parameters().size(); ++p)
          {
            const char ki = template_param_kind(old_identifiers[i], p);
            const char kj = template_param_kind(old_identifiers[j], p);
            if(ki == kj)
              continue;
            // Argument must be an lvalue for the rvalue-ref vs
            // lvalue-ref partial ordering to apply.
            const bool arg_lvalue = p < fargs.operands.size() &&
                                    fargs.operands[p].get_bool(ID_C_lvalue);
            if(ki == 'R' && kj == 'L' && arg_lvalue)
              any_diff = true;
            else
            {
              i_dominated = false;
              break;
            }
          }
          if(i_dominated && any_diff)
            dominated_fwd[i] = true;
        }
      }
      if(std::count(dominated_fwd.begin(), dominated_fwd.end(), false) >= 1)
      {
        std::vector<exprt> survivors;
        for(std::size_t i = 0; i < old_identifiers.size(); ++i)
          if(!dominated_fwd[i])
            survivors.push_back(old_identifiers[i]);
        if(survivors.size() < old_identifiers.size() && !survivors.empty())
          old_identifiers.swap(survivors);
      }
    }

    // Try to further disambiguate by partial ordering: a candidate is
    // "dominated" if another candidate has at least as specific
    // parameter types (via derived-to-base subtyping) for every
    // parameter and strictly more specific for at least one.
    std::vector<bool> dominated(old_identifiers.size(), false);

    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      if(old_identifiers[i].type().id() != ID_code)
        continue;

      const code_typet &f1 = to_code_type(old_identifiers[i].type());

      for(std::size_t j = 0; j < old_identifiers.size(); ++j)
      {
        if(i == j || dominated[j])
          continue;

        if(old_identifiers[j].type().id() != ID_code)
          continue;

        const code_typet &f2 = to_code_type(old_identifiers[j].type());

        if(f1.parameters().size() != f2.parameters().size())
          continue;

        // Check if f2 is at least as specific as f1 (i.e., f2
        // dominates f1): for each parameter, f2's type must be the
        // same as or a subtype (more derived) of f1's type.
        bool f2_at_least_as_specific = true;
        bool f2_strictly_more_specific = false;

        for(std::size_t p = 0;
            p < f1.parameters().size() && f2_at_least_as_specific;
            ++p)
        {
          typet type1 = f1.parameters()[p].type();
          typet type2 = f2.parameters()[p].type();

          if(type1 == type2)
            continue;

          if(is_reference(type1) != is_reference(type2))
          {
            f2_at_least_as_specific = false;
            continue;
          }

          if(type1.id() == ID_pointer)
            type1 = to_pointer_type(type1).base_type();
          if(type2.id() == ID_pointer)
            type2 = to_pointer_type(type2).base_type();

          if(type1.id() != ID_struct_tag || type2.id() != ID_struct_tag)
          {
            f2_at_least_as_specific = false;
            continue;
          }

          // f2's param type is a subtype (more derived) of f1's
          if(cpp_typecheck.subtype_typecast(
               cpp_typecheck.follow_tag(to_struct_tag_type(type2)),
               cpp_typecheck.follow_tag(to_struct_tag_type(type1))))
          {
            f2_strictly_more_specific = true;
          }
          else
          {
            f2_at_least_as_specific = false;
          }
        }

        if(f2_at_least_as_specific && f2_strictly_more_specific)
          dominated[i] = true;
      }
    }

    // N5008 [temp.func.order] + [temp.deduct.partial]: deduction-based
    // partial ordering between function-template candidates.  The subtyping
    // pass above only orders concrete derived-to-base struct parameters; this
    // orders the template parameter *patterns* themselves -- e.g. f(_Tp*) is
    // more specialised than f(const _Ptr&), which is what disambiguates
    // libstdc++ std::__to_address(_Tp*) from __to_address(const _Ptr&) for a
    // pointer argument (and any equivalent overload pair).  Candidate i is
    // dominated by j when j is at-least-as-specialised as i but not vice
    // versa.
    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      if(dominated[i] || old_identifiers[i].type().id() != ID_code)
        continue;
      const irep_idt ti = old_identifiers[i].type().get(ID_C_template);
      if(ti.empty())
        continue;
      const symbolt *si = cpp_typecheck.symbol_table.lookup(ti);
      if(si == nullptr || si->type.id() != ID_cpp_declaration)
        continue;

      for(std::size_t j = 0; j < old_identifiers.size(); ++j)
      {
        if(i == j || dominated[i] || old_identifiers[j].type().id() != ID_code)
          continue;
        const irep_idt tj = old_identifiers[j].type().get(ID_C_template);
        if(tj.empty() || tj == ti)
          continue;
        const symbolt *sj = cpp_typecheck.symbol_table.lookup(tj);
        if(sj == nullptr || sj->type.id() != ID_cpp_declaration)
          continue;

        const cpp_declarationt &Di = to_cpp_declaration(si->type);
        const cpp_declarationt &Dj = to_cpp_declaration(sj->type);
        const bool j_aas_i =
          cpp_typecheck.function_template_at_least_as_specialised(
            Dj, Di, tj, ti);
        const bool i_aas_j =
          cpp_typecheck.function_template_at_least_as_specialised(
            Di, Dj, ti, tj);
        if(j_aas_i && !i_aas_j)
          dominated[i] = true;
      }
    }

    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      if(!dominated[i])
        identifiers.push_back(old_identifiers[i]);
    }

    // If still ambiguous, prefer candidates with resolved return
    // types over those with unresolved 'auto'.  This handles the
    // case where a more specialized template (e.g., _Ty* _Unfancy)
    // ties with a generic one (auto _Unfancy) after instantiation.
    if(identifiers.size() > 1)
    {
      resolve_identifierst resolved;
      for(const auto &id : identifiers)
      {
        if(id.type().id() != ID_code)
        {
          resolved.push_back(id);
          continue;
        }
        const auto &ret = to_code_type(id.type()).return_type();
        if(ret.id() != ID_auto)
          resolved.push_back(id);
      }
      if(!resolved.empty() && resolved.size() < identifiers.size())
        identifiers = resolved;
    }
  }
  else
  {
    identifiers.swap(old_identifiers);
  }

  remove_duplicates(identifiers);
}

void cpp_typecheck_resolvet::make_constructors(
  resolve_identifierst &identifiers)
{
  resolve_identifierst new_identifiers;

  for(const auto &identifier_orig : identifiers)
  {
    exprt identifier = identifier_orig;
    if(identifier.id() != ID_type)
    {
      // already an expression
      new_identifiers.push_back(identifier);
      continue;
    }

    // A type substituted from the template map may still be in its
    // unconverted parse form (a `frontend_pointer` reference, e.g. the
    // pack element int& behind the functional cast `Args(args)...` in a
    // function-type partial specialization).  The POD/reference
    // classification below and the later argument matching need the
    // converted form ([expr.type.conv] operates on the actual type).
    if(
      identifier.type().id() == ID_frontend_pointer ||
      identifier.type().id() == ID_merged_type)
    {
      try
      {
        cpp_typecheck.typecheck_type(identifier.type());
      }
      catch(...)
      {
        // leave unconverted; downstream matching will reject
      }
    }

    // is it a POD?

    if(cpp_typecheck.cpp_is_pod(identifier.type()))
    {
      // there are two pod constructors:

      // 1. no arguments, default initialization
      {
        const code_typet t1({}, identifier.type());
        exprt pod_constructor1(ID_pod_constructor, t1);
        new_identifiers.push_back(pod_constructor1);
      }

      // 2. one argument, copy/conversion
      {
        const code_typet t2(
          {code_typet::parametert(identifier.type())}, identifier.type());
        exprt pod_constructor2(ID_pod_constructor, t2);
        new_identifiers.push_back(pod_constructor2);
      }

      // enums, in addition, can also be constructed from int
      if(identifier.type().id() == ID_c_enum_tag)
      {
        const code_typet t3(
          {code_typet::parametert(signed_int_type())}, identifier.type());
        exprt pod_constructor3(ID_pod_constructor, t3);
        new_identifiers.push_back(pod_constructor3);
      }
    }
    else if(is_reference(identifier.type()))
    {
      // N5008 [expr.type.conv]/1: a functional cast `T(x)` where T is a
      // REFERENCE type direct-initializes a result of type T from x
      // (equivalent to a cast).  References are not PODs and have no
      // constructors, so without a synthesized single-argument
      // "constructor" the resolution finds no candidate at all -- e.g.
      // libstdc++'s `_M_invoker(_M_functor, _ArgTypes(__args)...)` in
      // std::function::operator() with _ArgTypes = int&.  There is no
      // zero-argument form: a reference must be bound ([dcl.init.ref]).
      const code_typet t(
        {code_typet::parametert(identifier.type())}, identifier.type());
      exprt pod_constructor(ID_pod_constructor, t);
      new_identifiers.push_back(pod_constructor);
    }
    else if(identifier.type().id() == ID_struct_tag)
    {
      const struct_typet &struct_type =
        cpp_typecheck.follow_tag(to_struct_tag_type(identifier.type()));

      // Collect identifiers already present to avoid duplicates
      std::set<irep_idt> existing_ids;
      for(const auto &existing : new_identifiers)
      {
        if(existing.id() == ID_symbol)
          existing_ids.insert(to_symbol_expr(existing).get_identifier());
      }

      // go over components
      for(const auto &component : struct_type.components())
      {
        const typet &type = component.type();

        if(component.get_bool(ID_from_base))
          continue;

        if(
          type.id() == ID_code &&
          to_code_type(type).return_type().id() == ID_constructor)
        {
          if(existing_ids.count(component.get_name()))
            continue;
          const symbolt &symb = cpp_typecheck.lookup(component.get_name());
          exprt e = cpp_symbol_expr(symb);
          e.type() = type;
          new_identifiers.push_back(e);
        }
      }

      // Also look for template constructors in the class scope.
      // Template constructors are not struct components; they are
      // stored as TEMPLATE entries in the class scope.
      const irep_idt &class_name = struct_type.get(ID_name);
      auto scope_it = cpp_typecheck.cpp_scopes.id_map.find(class_name);
      if(scope_it != cpp_typecheck.cpp_scopes.id_map.end())
      {
        cpp_scopet &class_scope = static_cast<cpp_scopet &>(*scope_it->second);
        const irep_idt &ctor_base_name =
          cpp_typecheck.lookup(class_name).base_name;
        cpp_scopet::id_sett tmpl_set = class_scope.lookup(
          ctor_base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);
        for(const auto &id_ptr : tmpl_set)
        {
          // Skip if already present (e.g., from convert_identifiers)
          bool already_present = false;
          for(const auto &existing : new_identifiers)
          {
            if(
              existing.id() == ID_symbol &&
              to_symbol_expr(existing).get_identifier() == id_ptr->identifier)
            {
              already_present = true;
              break;
            }
          }
          if(already_present)
            continue;

          const symbolt &symb = cpp_typecheck.lookup(id_ptr->identifier);
          exprt e = cpp_symbol_expr(symb);
          // Store the class tag so that template argument deduction
          // can pre-populate the template map with class template args.
          e.set(ID_C_class, class_name);
          new_identifiers.push_back(e);
        }
      }
    }
  }

  identifiers.swap(new_identifiers);
}

void cpp_typecheck_resolvet::resolve_argument(
  exprt &argument,
  const cpp_typecheck_fargst &fargs)
{
  if(argument.id() == ID_ambiguous) // could come from a template parameter
  {
    // this must be resolved in the template scope
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    argument = resolve(to_cpp_name(argument.type()), wantt::VAR, fargs, false);
  }
}

exprt cpp_typecheck_resolvet::do_builtin(
  const irep_idt &base_name,
  const cpp_typecheck_fargst &fargs,
  const cpp_template_args_non_tct &template_args)
{
  exprt dest;

  const cpp_template_args_non_tct::argumentst &arguments =
    template_args.arguments();

  if(base_name == ID_unsignedbv || base_name == ID_signedbv)
  {
    if(arguments.size() != 1)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects one template argument, but got "
        << arguments.size() << messaget::eom;
      throw 0;
    }

    exprt argument = arguments.front(); // copy

    if(argument.id() == ID_type)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects one integer template argument, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    resolve_argument(argument, fargs);

    const auto i = numeric_cast<mp_integer>(argument);
    if(!i.has_value())
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << "template argument must be constant" << messaget::eom;
      throw 0;
    }

    if(*i < 1)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << "template argument must be greater than zero" << messaget::eom;
      throw 0;
    }

    dest = type_exprt(typet(base_name));
    dest.type().set(ID_width, integer2string(*i));
  }
  else if(base_name == ID_fixedbv)
  {
    if(arguments.size() != 2)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects two template arguments, but got "
        << arguments.size() << messaget::eom;
      throw 0;
    }

    exprt argument0 = arguments[0];
    resolve_argument(argument0, fargs);
    exprt argument1 = arguments[1];
    resolve_argument(argument1, fargs);

    if(argument0.id() == ID_type)
    {
      cpp_typecheck.error().source_location = argument0.find_source_location();
      cpp_typecheck.error()
        << base_name << " expects two integer template arguments, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    if(argument1.id() == ID_type)
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << base_name << " expects two integer template arguments, "
        << "but got type" << messaget::eom;
      throw 0;
    }

    const auto width = numeric_cast<mp_integer>(argument0);

    if(!width.has_value())
    {
      cpp_typecheck.error().source_location = argument0.find_source_location();
      cpp_typecheck.error()
        << "template argument must be constant" << messaget::eom;
      throw 0;
    }

    const auto integer_bits = numeric_cast<mp_integer>(argument1);

    if(!integer_bits.has_value())
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be constant" << messaget::eom;
      throw 0;
    }

    if(*width < 1)
    {
      cpp_typecheck.error().source_location = argument0.find_source_location();
      cpp_typecheck.error()
        << "template argument must be greater than zero" << messaget::eom;
      throw 0;
    }

    if(*integer_bits < 0)
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be greater or equal zero" << messaget::eom;
      throw 0;
    }

    if(*integer_bits > *width)
    {
      cpp_typecheck.error().source_location = argument1.find_source_location();
      cpp_typecheck.error()
        << "template argument must be smaller or equal width" << messaget::eom;
      throw 0;
    }

    dest = type_exprt(typet(base_name));
    dest.type().set(ID_width, integer2string(*width));
    dest.type().set(ID_integer_bits, integer2string(*integer_bits));
  }
  else if(base_name == ID_integer)
  {
    if(!arguments.empty())
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << base_name << " expects no template arguments" << messaget::eom;
      throw 0;
    }

    dest = type_exprt(typet(base_name));
  }
  else if(base_name.starts_with("constant_infinity"))
  {
    // ok, but type missing
    dest = exprt(ID_infinity, size_type());
  }
  else if(base_name == "dump_scopes")
  {
    dest = exprt(ID_constant, typet(ID_empty));
    cpp_typecheck.warning()
      << "Scopes in location " << source_location << messaget::eom;
    cpp_typecheck.cpp_scopes.get_root_scope().print(cpp_typecheck.warning());
  }
  else if(base_name == "current_scope")
  {
    dest = exprt(ID_constant, typet(ID_empty));
    cpp_typecheck.warning() << "Scope in location " << source_location << ": "
                            << original_scope->prefix << messaget::eom;
  }
  else if(base_name == ID_size_t)
  {
    dest = type_exprt(size_type());
  }
  else if(base_name == ID_ssize_t)
  {
    dest = type_exprt(signed_size_type());
  }
  else
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "unknown built-in identifier: " << base_name
                          << messaget::eom;
    throw 0;
  }

  return dest;
}

/// \par parameters: a cpp_name
/// \return a base_name, and potentially template arguments for the base name;
///   as side-effect, we got to the right scope
cpp_scopet &cpp_typecheck_resolvet::resolve_scope(
  const cpp_namet &cpp_name,
  irep_idt &base_name,
  cpp_template_args_non_tct &template_args)
{
  PRECONDITION(!cpp_name.get_sub().empty());

  original_scope = &cpp_typecheck.cpp_scopes.current_scope();
  source_location = cpp_name.source_location();

  irept::subt::const_iterator pos = cpp_name.get_sub().begin();

  bool recursive = true;

  // check if we need to go to the root scope
  if(pos->id() == "::")
  {
    pos++;
    cpp_typecheck.cpp_scopes.go_to_root_scope();
    recursive = false;
  }

  std::string final_base_name;
  template_args.make_nil();

  while(pos != cpp_name.get_sub().end())
  {
    if(pos->id() == ID_name)
      final_base_name += pos->get_string(ID_identifier);
    else if(pos->id() == ID_decltype)
    {
      exprt expr = static_cast<const exprt &>(pos->find(ID_type_arg));
      if(expr.is_nil())
        expr = static_cast<const exprt &>(pos->find(ID_expr_arg));
      if(expr.is_nil())
        expr = static_cast<const exprt &>(pos->find("expr"));
      if(expr.is_not_nil())
      {
        // Apply template_map to substitute template parameters
        // in the decltype expression (e.g., __test<_Tp>(nullptr))
        cpp_typecheck.template_map.apply(expr);
        cpp_typecheck.typecheck_expr(expr);
        typet t = expr.type();
        // Remove references
        if(
          t.id() == ID_pointer &&
          (t.get_bool(ID_C_reference) || t.get_bool(ID_C_rvalue_reference)))
          t = to_pointer_type(t).base_type();
        if(t.id() == ID_struct_tag)
        {
          cpp_typecheck.elaborate_class_template(t);
          const irep_idt &scope_id = to_struct_tag_type(t).get_identifier();
          cpp_typecheck.cpp_scopes.go_to(
            cpp_typecheck.cpp_scopes.get_scope(scope_id));
        }
        else
        {
          // decltype resolved to a non-class type; cannot scope into it.
          throw 0; // decltype resolved to non-class type
        }
      }
      final_base_name.clear();
    }
    else if(pos->id() == ID_template_args)
      template_args = to_cpp_template_args_non_tc(*pos);
    else if(pos->id() == "::")
    {
      // If final_base_name is empty, the scope was already navigated
      // (e.g., by a decltype handler). Just advance past ::.
      if(final_base_name.empty() && template_args.is_nil())
      {
        ++pos;
        continue;
      }
      if(cpp_typecheck.suppress_elaborate && template_args.is_nil())
      {
        // Fast path: use RECURSIVE lookup but only accept scopes.
        // Skip the expensive filter_for_named_scopes.
        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED);
        bool found = false;
        for(const auto *id_ptr : id_set)
        {
          if(id_ptr->is_scope)
          {
            cpp_typecheck.cpp_scopes.go_to(
              static_cast<cpp_scopet &>(const_cast<cpp_idt &>(*id_ptr)));
            found = true;
            break;
          }
          if(id_ptr->is_typedef())
          {
            // Follow typedef to find the scope
            const auto *sym =
              cpp_typecheck.symbol_table.lookup(id_ptr->identifier);
            if(sym && sym->is_type && sym->type.id() == ID_struct_tag)
            {
              auto it = cpp_typecheck.cpp_scopes.id_map.find(
                to_struct_tag_type(sym->type).get_identifier());
              if(
                it != cpp_typecheck.cpp_scopes.id_map.end() &&
                it->second->is_scope)
              {
                cpp_typecheck.cpp_scopes.go_to(
                  static_cast<cpp_scopet &>(*it->second));
                found = true;
                break;
              }
            }
            // MEMBER typedefs are stored as struct components, not
            // standalone symbols ([class.member.lookup]); follow the
            // parent class's component to the underlying scope exactly
            // as filter_for_named_scopes does on the slow path.
            // Without this, a member alias chain such as libc++
            // __split_buffer's `typedef allocator_traits
            // __alloc_traits; using iterator = __alloc_traits::
            // pointer;` bailed out here, the alias stayed
            // unregistered, and the field declaration `iterator end;`
            // resolved to the namespace-scope std::iterator template
            // instead.
            if(
              sym == nullptr && id_ptr->is_member &&
              config.ansi_c.preprocessor ==
                configt::ansi_ct::preprocessort::CLANG)
            {
              const cpp_idt &parent = id_ptr->get_parent();
              const auto *class_sym =
                cpp_typecheck.symbol_table.lookup(parent.identifier);
              if(class_sym != nullptr && class_sym->type.id() == ID_struct)
              {
                const struct_typet::componentt *chosen = nullptr;
                for(const auto &comp :
                    to_struct_type(class_sym->type).components())
                {
                  if(!(comp.get_base_name() == id_ptr->base_name &&
                       comp.get_bool(ID_is_type)))
                    continue;
                  if(comp.get_name() == id_ptr->identifier)
                  {
                    chosen = &comp;
                    break;
                  }
                  if(
                    chosen == nullptr || (chosen->get_bool(ID_from_base) &&
                                          !comp.get_bool(ID_from_base)))
                  {
                    chosen = &comp;
                  }
                }
                if(chosen != nullptr && chosen->type().id() == ID_struct_tag)
                {
                  auto it = cpp_typecheck.cpp_scopes.id_map.find(
                    to_struct_tag_type(chosen->type()).get_identifier());
                  if(
                    it != cpp_typecheck.cpp_scopes.id_map.end() &&
                    it->second->is_scope)
                  {
                    cpp_typecheck.cpp_scopes.go_to(
                      static_cast<cpp_scopet &>(*it->second));
                    found = true;
                    break;
                  }
                }
              }
            }
          }
        }
        if(found)
        {
          final_base_name.clear();
          ++pos;
          continue;
        }
        // Check if the name is a struct_tag identifier that has a
        // registered scope (e.g., an elaborated template class).
        // The name might be a full identifier (tag-X) or a base name
        // from template_map substitution. Try both.
        {
          auto it = cpp_typecheck.cpp_scopes.id_map.find(final_base_name);
          if(it == cpp_typecheck.cpp_scopes.id_map.end())
          {
            // Try with current scope prefix
            const std::string &scope_id =
              id2string(cpp_typecheck.cpp_scopes.current_scope().identifier);
            if(!scope_id.empty())
              it = cpp_typecheck.cpp_scopes.id_map.find(
                scope_id + "::" + id2string(final_base_name));
          }
          if(it == cpp_typecheck.cpp_scopes.id_map.end())
          {
            // Try as tag identifier
            it = cpp_typecheck.cpp_scopes.id_map.find(
              "tag-" + id2string(final_base_name));
          }
          if(
            it != cpp_typecheck.cpp_scopes.id_map.end() && it->second->is_scope)
          {
            cpp_typecheck.cpp_scopes.go_to(
              static_cast<cpp_scopet &>(*it->second));
            final_base_name.clear();
            ++pos;
            continue;
          }
        }
        // Check template_map for template parameters like _Up::X
        {
          typet mapped{};
          for(const auto &entry : cpp_typecheck.template_map.type_map)
          {
            const std::string &key = id2string(entry.first);
            auto p = key.rfind("::");
            std::string suffix =
              p != std::string::npos ? key.substr(p + 2) : key;
            if(
              suffix == id2string(final_base_name) &&
              entry.second.id() != ID_unassigned && entry.second.id() != ID_nil)
            {
              mapped = entry.second;
              break;
            }
          }
          if(mapped.is_not_nil() && mapped.id() == ID_struct_tag)
          {
            const irep_idt &scope_id =
              to_struct_tag_type(mapped).get_identifier();
            auto it = cpp_typecheck.cpp_scopes.id_map.find(scope_id);
            if(
              it != cpp_typecheck.cpp_scopes.id_map.end() &&
              it->second->is_scope)
            {
              cpp_typecheck.cpp_scopes.go_to(
                static_cast<cpp_scopet &>(*it->second));
              final_base_name.clear();
              ++pos;
              continue;
            }
          }
        }
        // Scope not found with suppress — bail out
        // Try to elaborate template class instances before giving up.
        // The name might be a struct_tag identifier (e.g.,
        // "std::__1::tag-__wrap_iter<ptr_signed_int>") that the scope
        // system doesn't know about. Look it up in the symbol table.
        {
          const auto *sym = cpp_typecheck.symbol_table.lookup(final_base_name);
          if(
            sym && sym->type.get_bool(ID_template_class_instance) &&
            (sym->type.id() == ID_struct || sym->type.id() == ID_union))
          {
            bool old_suppress = cpp_typecheck.suppress_elaborate;
            bool old_force = cpp_typecheck.force_elaborate;
            cpp_typecheck.suppress_elaborate = false;
            cpp_typecheck.force_elaborate = true;
            try
            {
              typet tag_type =
                sym->type.id() == ID_struct
                  ? static_cast<typet>(struct_tag_typet{sym->name})
                  : static_cast<typet>(union_tag_typet{sym->name});
              cpp_typecheck.elaborate_class_template(tag_type);
            }
            catch(...)
            {
            }
            cpp_typecheck.suppress_elaborate = old_suppress;
            cpp_typecheck.force_elaborate = old_force;
            // After elaboration, the scope should be registered
            auto it = cpp_typecheck.cpp_scopes.id_map.find(sym->name);
            if(
              it != cpp_typecheck.cpp_scopes.id_map.end() &&
              it->second->is_scope)
            {
              cpp_typecheck.cpp_scopes.go_to(
                static_cast<cpp_scopet &>(*it->second));
              final_base_name.clear();
              ++pos;
              continue;
            }
          }
        }
        throw 0;
      }

      if(template_args.is_not_nil())
      {
        // Clang's builtin alias template
        // `__make_integer_seq<Tpl, T, N>` names `Tpl<T, 0, ..., N-1>`
        // (the compiler-accelerated backing of [intseq.make]; libc++'s
        // tuple indices are built on it).  It is not an ordinary
        // template, so rewrite the name to the expanded template-id
        // before the scope lookup would fail on it -- the analogue of
        // the GCC `__integer_pack(N)` expansion in
        // typecheck_template_args.
        if(
          final_base_name == "__make_integer_seq" &&
          template_args.arguments().size() == 3)
        {
          const auto &ma = template_args.arguments();
          // The pack template: a (possibly qualified) name.
          const exprt &tpl_arg = ma[0];
          // The element type.
          // The element type arrives as `type` or an `ambiguous` node
          // carrying the type.
          typet elem_type =
            ma[1].id() == ID_type || ma[1].id() == ID_ambiguous
              ? ma[1].type()
              : static_cast<const typet &>(static_cast<const irept &>(ma[1]));
          // The count: a constant expression in this context.
          // The count arrives as a plain expression, or wrapped in a
          // `type`/`ambiguous` node (a dependent name such as `N`
          // parses as ambiguous(cpp_name)).
          exprt count = ma[2];
          if(count.id() == ID_type || count.id() == ID_ambiguous)
            count = static_cast<const exprt &>(
              static_cast<const irept &>(ma[2].type()));
          std::optional<mp_integer> n;
          try
          {
            cpp_typecheck.typecheck_expr(count);
            simplify(count, cpp_typecheck);
            n = numeric_cast<mp_integer>(count);
          }
          catch(...)
          {
            // dependent count: not expandable here
          }
          irep_idt tpl_name;
          // The pack-template argument arrives as `type`,
          // `cpp_name`, or an `ambiguous` node wrapping either.
          const irept *tpl_node = &static_cast<const irept &>(tpl_arg);
          if(tpl_node->id() == ID_ambiguous || tpl_node->id() == ID_type)
          {
            const irept &t = tpl_arg.type();
            if(t.id() == ID_cpp_name)
              tpl_node = &t;
          }
          if(tpl_node->id() == ID_cpp_name)
            tpl_name = to_cpp_name(*tpl_node).get_base_name();
          if(n.has_value() && *n >= 0 && !tpl_name.empty())
          {
            typet elem_tc = elem_type;
            cpp_typecheck.typecheck_type(elem_tc);
            cpp_template_args_non_tct expanded_args;
            auto &eargs = expanded_args.arguments();
            exprt type_arg{ID_type};
            type_arg.type() = elem_type;
            eargs.push_back(static_cast<const exprt &>(type_arg));
            for(mp_integer i = 0; i < *n; ++i)
              eargs.push_back(from_integer(i, elem_tc));
            auto tpl_id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
              tpl_name, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
            if(!tpl_id_set.empty())
            {
              typet instance = disambiguate_template_classes(
                tpl_name, tpl_id_set, expanded_args, false);
              instance.add_source_location() = source_location;
              cpp_typecheck.elaborate_class_template(instance);
              if(instance.id() == ID_struct_tag)
              {
                cpp_typecheck.cpp_scopes.go_to(
                  cpp_typecheck.cpp_scopes.get_scope(
                    to_struct_tag_type(instance).get_identifier()));
                final_base_name.clear();
                template_args.make_nil();
                ++pos;
                continue;
              }
            }
          }
          // Not expandable here: fall through to the ordinary lookup
          // (which will fail with the previous diagnostic).
        }

        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED,
          cpp_idt::id_classt::TEMPLATE);

        // N5008 [basic.lookup.qual] + [temp.names]/3: for
        // `T::template name<args>` the name is looked up in the scope
        // of T.  When T is a class-template instance whose members
        // have not been registered yet (its scope was entered without
        // full elaboration -- e.g. __gnu_cxx::__alloc_traits<A, U>'s
        // member template `rebind` while instantiating _Vector_base),
        // the lookup comes back empty and the recursive fallback would
        // collect every same-name member template in the program
        // ("template scope 'rebind' is ambiguous", with the correct
        // candidate not even in the set).  Elaborate the instance and
        // retry the scope-restricted lookup first.
        if(
          id_set.empty() &&
          !cpp_typecheck.cpp_scopes.current_scope().class_identifier.empty())
        {
          struct_tag_typet instance{
            cpp_typecheck.cpp_scopes.current_scope().class_identifier};
          cpp_typecheck.elaborate_class_template(instance);
          id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
            final_base_name,
            recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED,
            cpp_idt::id_classt::TEMPLATE);
        }

        // If no template was found, check if the name is a template
        // template parameter and resolve it via the template map.
        if(id_set.empty())
        {
          const auto param_set =
            cpp_typecheck.cpp_scopes.current_scope().lookup(
              final_base_name,
              recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED,
              cpp_idt::id_classt::TEMPLATE_PARAMETER);
          if(!param_set.empty())
          {
            const cpp_idt &param_id = **param_set.begin();
            exprt e = cpp_typecheck.template_map.lookup(param_id.identifier);
            if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
            {
              const std::string id_str = id2string(param_id.identifier);
              auto p = id_str.rfind("::");
              if(p != std::string::npos)
                e = cpp_typecheck.template_map.lookup_by_suffix(
                  id_str.substr(p + 2), param_id.identifier);
            }
            if(
              e.id() == ID_type &&
              e.type().id() == ID_template_parameter_symbol_type)
            {
              const irep_idt &tmpl_id =
                to_template_parameter_symbol_type(e.type()).get_identifier();
              if(cpp_typecheck.symbol_table.has_symbol(tmpl_id))
              {
                const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
                auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
                  tmpl_sym.base_name,
                  cpp_scopet::RECURSIVE,
                  cpp_idt::id_classt::TEMPLATE);
                for(const auto &f : found)
                  id_set.insert(f);
              }
            }
          }
        }

#ifdef DEBUG
        std::cout << "S: "
                  << cpp_typecheck.cpp_scopes.current_scope().identifier
                  << '\n';
        cpp_typecheck.cpp_scopes.current_scope().print(std::cout);
        std::cout << "X: " << id_set.size() << '\n';
#endif
        // Check if this is a template alias rather than a class template
        bool is_alias = false;
        for(const auto &id_ptr : id_set)
        {
          const symbolt &s = cpp_typecheck.lookup(id_ptr->identifier);
          if(
            s.type.get_bool(ID_is_template) &&
            to_cpp_declaration(s.type).is_template_alias())
          {
            is_alias = true;
            break;
          }
        }

        if(is_alias)
        {
          typet result =
            resolve_template_alias(final_base_name, id_set, template_args);
          if(result.id() == ID_struct_tag)
          {
            struct_tag_typet instance = to_struct_tag_type(result);
            instance.add_source_location() = source_location;
            cpp_typecheck.elaborate_class_template(instance);
            cpp_typecheck.cpp_scopes.go_to(
              cpp_typecheck.cpp_scopes.get_scope(instance.get_identifier()));
          }
          else
          {
            // Per [temp.deduct]/8: when a template alias resolves to
            // a non-class type during qualified name lookup, treat it
            // as a substitution failure (SFINAE).
            throw 0;
          }
        }
        else
        {
          // The walk through `resolve_scope` only enters this branch
          // for non-final cpp_name components.  When that component
          // is qualified by a leading `::` (recursive=false from
          // here on), pass `qualified=true` so the fallback id_set
          // lookup inside `disambiguate_template_classes` doesn't
          // ascend to the root scope, which would otherwise gather
          // every same-base-name template across the program and
          // produce spurious ambiguity errors during deep stdlib
          // partial-spec evaluation (notably for the
          // `__allocator_traits_base::__rebind` chain that tests
          // `_Tp::template rebind<_Up>::other`).
          //
          // For unqualified-first-component lookups (e.g.
          // `__int_traits<_Tp>::__digits` where `__int_traits` was
          // brought in via a `using` declaration), keep the
          // original recursive-fallback behaviour.
          typet instance = disambiguate_template_classes(
            final_base_name,
            id_set,
            template_args,
            /*qualified=*/!recursive);

          instance.add_source_location() = source_location;

          // the "::" triggers template elaboration.
          // When suppress_elaborate is true (e.g., during class body
          // processing), force elaboration so that scope resolution
          // can access the template class's members.
          cpp_typecheck.elaborate_class_template(instance);

          cpp_typecheck.cpp_scopes.go_to(cpp_typecheck.cpp_scopes.get_scope(
            to_tag_type(instance).get_identifier()));
        }

        template_args.make_nil();
      }
      else
      {
        auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          final_base_name,
          recursive ? cpp_scopet::RECURSIVE : cpp_scopet::QUALIFIED);

        // If the name resolves to a template parameter, substitute it
        // with the actual type from the template map and use that type's
        // scope for the qualified lookup.
        if(!id_set.empty())
        {
          const cpp_idt &first = **id_set.begin();
          if(first.id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
          {
            exprt e = convert_template_parameter(first);
            if(e.id() == ID_type && e.type().id() == ID_struct_tag)
            {
              cpp_typecheck.elaborate_class_template(e.type());
              const irep_idt &scope_id =
                to_struct_tag_type(e.type()).get_identifier();
              cpp_typecheck.cpp_scopes.go_to(
                cpp_typecheck.cpp_scopes.get_scope(scope_id));
              template_args.make_nil();
              final_base_name.clear();
              pos++;
              continue;
            }
          }
        }

        filter_for_named_scopes(id_set);

        // If no named scope found, check for typedefs resolving to a
        // class type (e.g., typedef Base _Mybase; using _Mybase::_Mybase)
        if(id_set.empty())
        {
          auto typedef_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
            final_base_name, cpp_scopet::RECURSIVE);
          for(const auto &id_ptr : typedef_set)
          {
            if(id_ptr->id_class == cpp_idt::id_classt::TYPEDEF)
            {
              const symbolt *sym =
                cpp_typecheck.symbol_table.lookup(id_ptr->identifier);
              if(sym != nullptr && sym->is_type)
              {
                typet t = sym->type;
                if(t.id() == ID_struct_tag)
                {
                  cpp_typecheck.elaborate_class_template(t);
                  const irep_idt &scope_id =
                    to_struct_tag_type(t).get_identifier();
                  cpp_typecheck.cpp_scopes.go_to(
                    cpp_typecheck.cpp_scopes.get_scope(scope_id));
                  final_base_name.clear();
                  ++pos;
                  final_base_name.clear();
                  break;
                }
              }
            }
          }
          if(final_base_name.empty())
            continue; // typedef resolved, continue with next component
        }

        if(id_set.empty())
        {
          // Fallback: search the global id_map for the namespace.
          // This handles cases where the current scope (e.g., a
          // template instantiation scope) doesn't have the target
          // namespace in its parent chain.
          for(auto &entry : cpp_typecheck.cpp_scopes.id_map)
          {
            if(
              entry.second->base_name == final_base_name &&
              entry.second->is_namespace())
            {
              id_set.insert(entry.second);
            }
          }
        }

        if(id_set.empty())
        {
          if(final_base_name.empty())
          {
            ++pos;
            continue;
          }
          // Check id_map for struct_tag identifiers from
          // template_map substitution (e.g., tag-A::value_type).
          auto id_it = cpp_typecheck.cpp_scopes.id_map.find(final_base_name);
          if(
            id_it != cpp_typecheck.cpp_scopes.id_map.end() &&
            id_it->second->is_scope)
          {
            cpp_typecheck.cpp_scopes.go_to(
              static_cast<cpp_scopet &>(*id_it->second));

            // Trigger class elaboration so that base-class members
            // (e.g., inherited typedefs) are available for the
            // subsequent qualified lookup.
            if(!cpp_typecheck.cpp_scopes.current_scope()
                  .class_identifier.empty())
            {
              struct_tag_typet instance{
                cpp_typecheck.cpp_scopes.current_scope().class_identifier};
              cpp_typecheck.elaborate_class_template(instance);
            }

            final_base_name.clear();
            ++pos;
            continue;
          }
          if(cpp_typecheck.suppress_elaborate)
          {
            throw 0;
          }
          // Scope-not-found during qualified name lookup is a
          // potential SFINAE failure.  Throw without error message
          // so that template specialization matching can discard
          // this candidate.  The error is caught by method body
          // processing or template instantiation.
          throw 0;
        }
        else if(id_set.size() >= 2)
        {
          cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
          cpp_typecheck.error().source_location = source_location;
          cpp_typecheck.error() << "scope '" << final_base_name
                                << "' is ambiguous" << messaget::eom;
          throw 0;
        }

        CHECK_RETURN(id_set.size() == 1);

        cpp_typecheck.cpp_scopes.go_to(**id_set.begin());

        // the "::" triggers template elaboration
        if(!cpp_typecheck.cpp_scopes.current_scope().class_identifier.empty())
        {
          struct_tag_typet instance(
            cpp_typecheck.cpp_scopes.current_scope().class_identifier);
          cpp_typecheck.elaborate_class_template(instance);
        }
      }

      // we start from fresh
      final_base_name.clear();
    }
    else if(pos->id() == ID_operator)
    {
      final_base_name += "operator";

      irept::subt::const_iterator next = pos + 1;
      CHECK_RETURN(next != cpp_name.get_sub().end());

      if(
        next->id() == ID_cpp_name || next->id() == ID_pointer ||
        next->id() == ID_frontend_pointer || next->id() == ID_int ||
        next->id() == ID_char || next->id() == ID_c_bool ||
        next->id() == ID_merged_type)
      {
        // it's a cast operator
        irept next_ir = *next;
        typet op_name;
        op_name.swap(next_ir);
        cpp_typecheck.typecheck_type(op_name);
        final_base_name += "(" + cpp_type2name(op_name) + ")";
        pos++;
      }
    }
    else
    {
      final_base_name += pos->id_string();
      // Substitute destructor names: when "~" is followed by a name
      // that's a template parameter, replace it with the actual type.
      if(
        pos->id_string() == "~" && (pos + 1) != cpp_name.get_sub().end() &&
        (pos + 1)->id() == ID_name)
      {
        irep_idt param_name = (pos + 1)->get(ID_identifier);
        // Collect all live struct-typed bindings whose short name matches.
        // The flat template map may hold SEVERAL same-short-name parameters
        // of unrelated templates ([basic.scope.temp]/2 -- e.g. the
        // destructibility probe's `_Tp` = basic_string alongside
        // allocator's and char_traits' `_Tp` during a libstdc++ trait
        // evaluation); picking an arbitrary one spelled the WRONG
        // destructor (`~allocator` looked up in basic_string's scope,
        // failing and dropping the trait's base specifier).  Per
        // [expr.prim.id.dtor]/2 the type designated by ~T must be the
        // object's type, and the destructor name is looked up in that
        // class's scope -- which is the CURRENT scope here.  Prefer the
        // binding that designates the current class scope; otherwise keep
        // the historical first match.
        const typet *chosen = nullptr;
        const irep_idt current_scope_id =
          cpp_typecheck.cpp_scopes.current_scope().identifier;
        for(const auto &entry : cpp_typecheck.template_map.type_map)
        {
          const std::string &key = id2string(entry.first);
          auto p = key.rfind("::");
          std::string suffix = p != std::string::npos ? key.substr(p + 2) : key;
          if(
            suffix != id2string(param_name) ||
            entry.second.id() != ID_struct_tag)
          {
            continue;
          }
          if(
            to_struct_tag_type(entry.second).get_identifier() ==
            current_scope_id)
          {
            chosen = &entry.second;
            break; // exact designation of the object's class
          }
          if(chosen == nullptr)
            chosen = &entry.second;
        }
        if(chosen != nullptr)
        {
          // Skip the name sub-node (it will be replaced)
          ++pos;
          // Use the struct's base name for the destructor.  The final
          // path component must be found ANGLE-AWARE: for a template
          // instance tag like `std::__cxx11::tag-basic_string<char,
          // std::tag-allocator<char>>` a naive rfind("::") lands inside
          // the template ARGUMENTS and produces the wrong destructor
          // name (`~allocator`).
          irep_idt tag = to_struct_tag_type(*chosen).get_identifier();
          std::string tag_str = id2string(tag);
          {
            std::size_t depth = 0;
            std::size_t final_component = 0;
            for(std::size_t i = 0; i + 1 < tag_str.size(); ++i)
            {
              if(tag_str[i] == '<')
                ++depth;
              else if(tag_str[i] == '>' && depth > 0)
                --depth;
              else if(depth == 0 && tag_str[i] == ':' && tag_str[i + 1] == ':')
                final_component = i + 2;
            }
            tag_str = tag_str.substr(final_component);
          }
          if(tag_str.substr(0, 4) == "tag-")
            tag_str = tag_str.substr(4);
          auto angle = tag_str.find('<');
          if(angle != std::string::npos)
            tag_str = tag_str.substr(0, angle);
          final_base_name += tag_str;
        }
        else
        {
          // N5008 [expr.prim.id.dtor]/1: in ~type-name the type-name may
          // be a TYPEDEF-NAME naming the class type (e.g. libstdc++'s
          // `__n->~__node_type()` in _Hashtable_alloc::
          // _M_deallocate_node_ptr, where __node_type is a class-scope
          // alias of _Hash_node<...>).  The class's destructor component
          // is named after the CLASS, so looking up "~__node_type"
          // fails (silently, dropping the member's body during
          // instantiation).  Resolve the typedef in the current scope
          // chain and spell the destructor with the designated class's
          // own name (final path component, angle-aware).
          // Resolve the type-name with a fresh sub-resolver, first in
          // the object's class scope (current), then in the recorded
          // postfix-expression context, which is where e.g. libstdc++'s
          // `__n->~__node_type()` finds the alias.
          typet designated;
          designated.make_nil();
          {
            const cpp_namet type_cpp_name(param_name, source_location);
            for(int attempt = 0; attempt < 2 && designated.is_nil(); ++attempt)
            {
              cpp_save_scopet dtor_td_save_scope(cpp_typecheck.cpp_scopes);
              if(attempt == 1)
              {
                if(cpp_typecheck.access_judgment_scope == nullptr)
                  break;
                cpp_typecheck.cpp_scopes.go_to(
                  *cpp_typecheck.access_judgment_scope);
              }
              cpp_typecheck_resolvet sub_resolver(cpp_typecheck);
              const exprt result = sub_resolver.resolve(
                type_cpp_name,
                wantt::TYPE,
                cpp_typecheck_fargst(),
                false); // fail_with_exception
              if(result.id() == ID_type && result.type().id() == ID_struct_tag)
                designated = result.type();
            }
          }
          if(designated.is_not_nil())
          {
            ++pos; // skip the typedef-name sub-node (it is replaced)
            std::string tag_str =
              id2string(to_struct_tag_type(designated).get_identifier());
            {
              std::size_t depth = 0;
              std::size_t final_component = 0;
              for(std::size_t i = 0; i + 1 < tag_str.size(); ++i)
              {
                if(tag_str[i] == '<')
                  ++depth;
                else if(tag_str[i] == '>' && depth > 0)
                  --depth;
                else if(
                  depth == 0 && tag_str[i] == ':' && tag_str[i + 1] == ':')
                  final_component = i + 2;
              }
              tag_str = tag_str.substr(final_component);
            }
            if(tag_str.substr(0, 4) == "tag-")
              tag_str = tag_str.substr(4);
            auto angle = tag_str.find('<');
            if(angle != std::string::npos)
              tag_str = tag_str.substr(0, angle);
            final_base_name += tag_str;
          }
        }
      }
    }

    pos++;
  }

  base_name = final_base_name;

  return cpp_typecheck.cpp_scopes.current_scope();
}

/// disambiguate partial specialization
typet cpp_typecheck_resolvet::disambiguate_template_classes(
  const irep_idt &base_name,
  const cpp_scopest::id_sett &id_set,
  const cpp_template_args_non_tct &full_template_args,
  bool qualified)
{
  cpp_scopest::id_sett effective_id_set = id_set;

  if(effective_id_set.empty() && !qualified)
  {
    // The template may not be visible in the current scope (e.g.,
    // during template instantiation). Search from the root scope.
    //
    // Skip this fallback when the lookup is qualified (`T::name`).
    // Per [basic.lookup.qual] the search is restricted to T's scope
    // and its base classes; ascending to the root scope here would
    // collect every same-base-name template across the program
    // (e.g. `rebind` from every `allocator<X>` instance), producing
    // a spurious "template scope 'rebind' is ambiguous" error
    // during deep stdlib partial-spec evaluation.
    effective_id_set = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
      base_name, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
  }

  // If still not found, search the symbol table for class templates
  // with the matching base name. This handles cases where the class
  // template was not added to the scope tree (e.g., templates from
  // system headers that were parsed but not fully registered).
  if(effective_id_set.empty() && !qualified)
  {
    for(const auto &sym_pair : cpp_typecheck.symbol_table)
    {
      const symbolt &sym = sym_pair.second;
      if(
        sym.base_name == base_name && sym.type.get_bool(ID_is_template) &&
        to_cpp_declaration(sym.type).is_class_template())
      {
        auto it = cpp_typecheck.cpp_scopes.id_map.find(sym.name);
        if(
          it != cpp_typecheck.cpp_scopes.id_map.end() &&
          (it->second->id_class == cpp_idt::id_classt::TEMPLATE ||
           it->second->is_template_scope()))
        {
          effective_id_set.insert(it->second);
        }
      }
    }
  }

  if(effective_id_set.empty())
  {
    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template scope '" << base_name << "' not found"
                          << messaget::eom;
    throw 0;
  }

  std::set<irep_idt> primary_templates;

  for(const auto &id_ptr : effective_id_set)
  {
    irep_idt id = id_ptr->identifier;
    // For template scopes found via id_map, the identifier might be
    // empty. Look up the id_map key instead.
    if(id.empty() || !cpp_typecheck.symbol_table.has_symbol(id))
    {
      for(const auto &entry : cpp_typecheck.cpp_scopes.id_map)
      {
        if(entry.second == id_ptr)
        {
          id = entry.first;
          break;
        }
      }
    }
    if(!cpp_typecheck.symbol_table.has_symbol(id))
      continue;
    const symbolt &s = cpp_typecheck.lookup(id);
    if(!s.type.get_bool(ID_is_template))
      continue;
    const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);
    if(!cpp_declaration.is_class_template())
      continue;
    irep_idt specialization_of = cpp_declaration.get_specialization_of();
    if(!specialization_of.empty())
      primary_templates.insert(specialization_of);
    else
      primary_templates.insert(id);
  }

  if(primary_templates.empty())
  {
    // The id_set may contain non-class templates (e.g., constructor
    // templates of an instantiated class) that shadow the class
    // template with the same base name. Walk up from each candidate's
    // parent scope to find the actual class template.
    for(const auto &id_ptr : effective_id_set)
    {
      auto it = cpp_typecheck.cpp_scopes.id_map.find(id_ptr->identifier);
      if(it == cpp_typecheck.cpp_scopes.id_map.end())
        continue;
      cpp_scopet &scope_ref = static_cast<cpp_scopet &>(*it->second);
      cpp_scopet *scope = &scope_ref;
      while(!scope->is_root_scope())
      {
        scope = &scope->get_parent();
        auto found = scope->lookup(
          base_name, cpp_scopet::SCOPE_ONLY, cpp_idt::id_classt::TEMPLATE);
        for(const auto &fid : found)
        {
          if(!cpp_typecheck.symbol_table.has_symbol(fid->identifier))
            continue;
          const symbolt &fs = cpp_typecheck.lookup(fid->identifier);
          if(!fs.type.get_bool(ID_is_template))
            continue;
          const cpp_declarationt &fd = to_cpp_declaration(fs.type);
          if(!fd.is_class_template())
            continue;
          irep_idt spec = fd.get_specialization_of();
          primary_templates.insert(spec.empty() ? fid->identifier : spec);
        }
        if(!primary_templates.empty())
          break;
      }
      if(!primary_templates.empty())
        break;
    }
  }

  if(primary_templates.empty())
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template '" << base_name << "' not found"
                          << messaget::eom;
    throw 0;
  }

  if(primary_templates.size() >= 2)
  {
    // Multiple primary templates found.  Per [class.member.lookup]
    // and [temp.names]/3, name lookup for `T::template name<args>`
    // is restricted to the scope of T, and a name declared in a
    // derived class hides a name with the same base_name inherited
    // from any base class.
    //
    // Filter in two passes:
    //
    //   (1) Keep only candidates whose identifier is within the
    //       current scope (either starts with `current::` or is
    //       `current` itself).  This matches the classic "scope of
    //       T" rule.
    //
    //   (2) Among the surviving candidates, drop any candidate whose
    //       declaring class is a base of another candidate's
    //       declaring class (dominance / name hiding by derived
    //       class).  If that also fails to narrow, leave the set
    //       unchanged so the ambiguity error below fires.
    cpp_scopet &current = cpp_typecheck.cpp_scopes.current_scope();
    const std::string prefix = id2string(current.identifier) + "::";
    // A class-instance scope's identifier carries the "tag-" marker on
    // its final class component ("__gnu_cxx::tag-__alloc_traits<...>"),
    // while a member template's identifier is rooted at the class name
    // WITHOUT it ("__gnu_cxx::__alloc_traits<...>::template.rebind<>").
    // Build a tag-stripped variant of the prefix so the scope-of-T
    // filter recognizes the class's own member templates; the "tag-"
    // token sits after the last "::" preceding the template-argument
    // list (arguments may contain "::" themselves).
    std::string untagged_prefix = prefix;
    {
      std::size_t lt_pos = untagged_prefix.find('<');
      std::size_t search_end =
        lt_pos == std::string::npos ? std::string::npos : lt_pos;
      std::size_t sep = untagged_prefix.rfind("::", search_end);
      std::size_t tag_pos = sep != std::string::npos ? sep + 2 : 0;
      if(untagged_prefix.compare(tag_pos, 4, "tag-") == 0)
        untagged_prefix.erase(tag_pos, 4);
    }
    std::set<irep_idt> filtered;
    for(const auto &pt : primary_templates)
    {
      if(
        id2string(pt).find(prefix) == 0 ||
        id2string(pt).find(untagged_prefix) == 0 || pt == current.identifier)
      {
        filtered.insert(pt);
      }
    }
    if(!filtered.empty() && filtered.size() < primary_templates.size())
      primary_templates = filtered;

    if(primary_templates.size() >= 2)
    {
      // Strip the trailing `::<something>` to get each candidate's
      // declaring class identifier, and translate it into the
      // canonical `tag-<classname><args>` form the symbol table
      // uses.  A primary template identifier looks like
      // `std::allocator<...>::template.rebind<Type0>`; the
      // declaring class's symbol-table identifier is
      // `std::tag-allocator<...>`.
      //
      // Note: `std::string::rfind("::")` is wrong here because the
      // template arguments may themselves contain `::` (e.g.
      // `std::allocator<std::pair<...>>`).  Walk the string
      // tracking angle-bracket depth and only consider separators
      // at depth zero.
      auto last_separator_at_depth_zero =
        [](const std::string &s) -> std::string::size_type
      {
        int depth = 0;
        std::string::size_type result = std::string::npos;
        for(std::string::size_type i = 0; i + 1 < s.size(); ++i)
        {
          char c = s[i];
          if(c == '<')
            ++depth;
          else if(c == '>')
            --depth;
          else if(depth == 0 && c == ':' && s[i + 1] == ':')
          {
            result = i;
            ++i; // skip the second ':'
          }
        }
        return result;
      };
      auto declaring_class =
        [&last_separator_at_depth_zero](const irep_idt &pt) -> irep_idt
      {
        const std::string s = id2string(pt);
        auto p = last_separator_at_depth_zero(s);
        if(p == std::string::npos)
          return irep_idt{};
        std::string scope = s.substr(0, p);
        // Insert "tag-" before the class name (the part after the
        // last depth-0 "::" in the remaining scope).  If the scope
        // has no namespace prefix, prepend "tag-".
        auto q = last_separator_at_depth_zero(scope);
        if(q == std::string::npos)
          return irep_idt{"tag-" + scope};
        return irep_idt{scope.substr(0, q + 2) + "tag-" + scope.substr(q + 2)};
      };
      // Transitive "is base of" walk of the derived-class's ID_bases
      // list in the symbol table.
      auto is_base_of =
        [&](const irep_idt &base, const irep_idt &derived) -> bool
      {
        if(base.empty() || derived.empty())
          return false;
        std::set<irep_idt> visited;
        std::vector<irep_idt> todo{derived};
        while(!todo.empty())
        {
          irep_idt d = todo.back();
          todo.pop_back();
          if(!visited.insert(d).second)
            continue;
          const symbolt *sym = cpp_typecheck.symbol_table.lookup(d);
          if(sym == nullptr)
            continue;
          const irept &bases = sym->type.find(ID_bases);
          for(const auto &b : bases.get_sub())
          {
            const typet &bt = static_cast<const typet &>(b.find(ID_type));
            if(bt.id() != ID_struct_tag)
              continue;
            const irep_idt &bid = to_struct_tag_type(bt).get_identifier();
            if(bid == base)
              return true;
            todo.push_back(bid);
          }
        }
        return false;
      };
      std::set<irep_idt> dominant = primary_templates;
      bool changed = true;
      while(changed && dominant.size() > 1)
      {
        changed = false;
        for(auto it = dominant.begin(); it != dominant.end();)
        {
          irep_idt ci = declaring_class(*it);
          bool dropped = false;
          for(auto jt = dominant.begin(); jt != dominant.end(); ++jt)
          {
            if(it == jt)
              continue;
            irep_idt cj = declaring_class(*jt);
            // If ci is a base of cj, the candidate from ci is
            // hidden by cj's candidate — drop ci.
            if(is_base_of(ci, cj))
            {
              it = dominant.erase(it);
              dropped = true;
              changed = true;
              break;
            }
          }
          if(!dropped)
            ++it;
        }
      }
      if(dominant.size() == 1)
        primary_templates = dominant;
    }
  }

  if(primary_templates.size() >= 2)
  {
    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template scope '" << base_name
                          << "' is ambiguous";
    for(const auto &pt : primary_templates)
      cpp_typecheck.error() << "\n  " << pt;
    cpp_typecheck.error() << messaget::eom;
    throw 0;
  }

  const symbolt &primary_template_symbol =
    cpp_typecheck.lookup(*primary_templates.begin());

  // We typecheck the template arguments in the context
  // of the original scope!
  cpp_template_args_tct full_template_args_tc;

  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    // use template type of 'primary template'
    full_template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, primary_template_symbol, full_template_args);

    for(auto &arg : full_template_args_tc.arguments())
    {
      if(arg.id() == ID_type)
        continue;
      if(arg.id() == ID_symbol)
      {
        const symbol_exprt &s = to_symbol_expr(arg);
        const symbolt &symbol = cpp_typecheck.lookup(s.identifier());

        if(
          cpp_typecheck.cpp_is_pod(symbol.type) &&
          symbol.type.get_bool(ID_C_constant))
        {
          arg = symbol.value;
        }
      }
      simplify(arg, cpp_typecheck);
    }

    // go back to where we used to be
  }

  // find any matches

  std::vector<matcht> matches;

  // the baseline
  matches.push_back(matcht(
    full_template_args_tc,
    full_template_args_tc,
    primary_template_symbol.name));

  for(const auto &id_ptr : id_set)
  {
    const irep_idt id = id_ptr->identifier;
    const symbolt &s = cpp_typecheck.lookup(id);

    if(s.type.get(ID_specialization_of).empty())
      continue;

    const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);

    cpp_template_args_non_tct partial_specialization_args =
      cpp_declaration.partial_specialization_args();

    // [temp.class.spec.match], [temp.arg]/2: a specialization's
    // argument list is completed with the primary template's default
    // arguments.  A full specialization `template<> struct C<X>` of a
    // primary template with a defaulted parameter
    // (`template<class T, class = void> struct C`) has the written
    // argument list <X>, but its effective argument list is <X, void>;
    // a use `C<X>` likewise resolves to <X, void>.  Pad the written
    // arguments with the primary's default arguments so the size check
    // and matching below operate on the completed list.  An incorrect
    // padding cannot cause a spurious match: the exact-equality check
    // against `full_template_args_tc` further below is the final
    // arbiter.
    for(std::size_t i = partial_specialization_args.arguments().size();
        i < full_template_args_tc.arguments().size();
        ++i)
    {
      const auto &primary_params =
        to_cpp_declaration(primary_template_symbol.type)
          .template_type()
          .template_parameters();
      if(i >= primary_params.size())
        break;
      const template_parametert &p =
        static_cast<const template_parametert &>(primary_params[i]);
      if(!p.has_default_argument())
        break;
      partial_specialization_args.arguments().push_back(p.default_argument());
    }

    // alright, set up template arguments as 'unassigned'

    cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.template_map.build_unassigned(
      cpp_declaration.template_type());

    // N5008 [temp.deduct]/5 (via [temp.class.spec.match]): restrict
    // deduction to this partial specialization's own parameters.
    deduction_parameters_guardt deduction_parameters_guard{
      current_deduction_parameters};
    current_deduction_parameters =
      template_parameter_ids(cpp_declaration.template_type());
    deduction_parameters_guardt map_deduction_parameters_guard{
      cpp_typecheck.template_map.deduction_parameters};
    cpp_typecheck.template_map.deduction_parameters =
      current_deduction_parameters;

    // iterate over template instance
    //
    // [temp.spec.partial.match], [temp.deduct.type]: a partial specialization
    // may end in a template parameter pack (`C<..., T...>`) that matches the
    // trailing sequence of the instantiation's arguments.  Such a pack is one
    // written argument but binds zero or more actual arguments, so the arity
    // check must admit an instantiation with at least the number of non-pack
    // arguments, and the deduction below must bind the pack to the rest.
    const std::size_t n_partial =
      partial_specialization_args.arguments().size();
    const std::size_t n_full = full_template_args_tc.arguments().size();
    // The written argument may be wrapped in an `ambiguous` node whose `type`
    // sub holds the actual pattern (a `cpp_name` carrying the pack `...`); look
    // through it, mirroring guess_template_args.
    const auto pattern_of = [](const exprt &arg) -> const irept &
    {
      if(arg.id() == ID_ambiguous)
        return arg.find(ID_type);
      if(arg.id() == ID_type)
        return arg.type();
      return arg;
    };
    bool partial_trailing_pack = false;
    if(n_partial > 0)
    {
      const exprt &last = partial_specialization_args.arguments().back();
      partial_trailing_pack =
        last.get_bool(ID_ellipsis) || pattern_of(last).get_bool(ID_ellipsis);
    }

    if(partial_trailing_pack ? (n_full + 1 < n_partial) : (n_full != n_partial))
    {
      continue;
    }

    // we need to do this in the right scope

    cpp_scopet *template_scope =
      static_cast<cpp_scopet *>(cpp_typecheck.cpp_scopes.id_map[id]);

    if(template_scope == nullptr)
    {
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error()
        << "template identifier: " << id << '\n'
        << "class template instantiation error" << messaget::eom;
      throw 0;
    }

    // enter the scope of the template
    cpp_typecheck.cpp_scopes.go_to(*template_scope);

    for(std::size_t i = 0; i < n_partial; i++)
    {
      const auto &parg = partial_specialization_args.arguments()[i];
      const irept &parg_pat = pattern_of(parg);
      const bool is_pack =
        parg.get_bool(ID_ellipsis) || parg_pat.get_bool(ID_ellipsis);
      if(is_pack)
      {
        // Bind the trailing parameter pack to the remaining instantiation
        // arguments ([temp.variadic]), mirroring the template-id pack
        // deduction in guess_template_args: record its element types and
        // count so build_template_args / typecheck_template_args expand it to
        // the deduced arity.
        const typet &parg_t = static_cast<const typet &>(parg_pat);
        irep_idt pack_id;
        if(parg_t.id() == ID_cpp_name)
        {
          const cpp_namet &pn = to_cpp_name(parg_t);
          if(!pn.is_qualified() && !pn.has_template_args())
          {
            const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
              pn.get_base_name(), cpp_scopet::RECURSIVE);
            for(const auto &id_ptr : ids)
              if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
                pack_id = id_ptr->identifier;
          }
        }
        if(!pack_id.empty())
        {
          std::vector<typet> pack_elems;
          for(std::size_t j = i; j < n_full; j++)
            if(
              full_template_args_tc.arguments()[j].id() == ID_type &&
              full_template_args_tc.arguments()[j].type().id() != ID_empty)
              pack_elems.push_back(full_template_args_tc.arguments()[j].type());
          cpp_typecheck.template_map.pack_size_map[pack_id] = pack_elems.size();
          cpp_typecheck.template_map.pack_args_map[pack_id] = pack_elems;
          if(!pack_elems.empty())
            cpp_typecheck.template_map.type_map[pack_id] = pack_elems.front();
        }
        break;
      }
      if(i >= n_full)
        break;
      if(full_template_args_tc.arguments()[i].id() == ID_type)
        guess_template_args(
          partial_specialization_args.arguments()[i].type(),
          full_template_args_tc.arguments()[i].type());
      else
        guess_template_args(
          partial_specialization_args.arguments()[i],
          full_template_args_tc.arguments()[i]);
    }

    // see if that has worked out

    cpp_template_args_tct guessed_template_args =
      cpp_typecheck.template_map.build_template_args(
        cpp_declaration.template_type());

    if(!guessed_template_args.has_unassigned())
    {
      // [temp.variadic]/5: when the selected partial specialization ends in a
      // template parameter pack (`C<..., A...>`), `build_template_args` emits a
      // single (scalar) convenience argument for the pack -- the front element
      // of the deduced binding.  For the actual instantiation we need the pack
      // expanded into one positional argument per deduced element (mirroring
      // `elaborate_class_template`), so that the specialization is instantiated
      // with the pack bound to ALL trailing arguments and `sizeof...(A)` is
      // correct; otherwise the pack collapses to one element.  This expanded
      // form is kept SEPARATE from `guessed_template_args`: the latter (and
      // hence `matcht::cost`) must keep the un-expanded arity so that
      // partial-ordering selection (which prefers the candidate with the fewer
      // specialization arguments) is not perturbed by the pack size.
      cpp_template_args_tct instantiation_args;
      {
        const auto &tparams =
          cpp_declaration.template_type().template_parameters();
        cpp_template_args_tct::argumentst expanded;
        for(std::size_t i = 0; i < guessed_template_args.arguments().size();
            i++)
        {
          if(i < tparams.size() && tparams[i].get_bool(ID_ellipsis))
          {
            const irep_idt pid = tparams[i].id() == ID_type
                                   ? tparams[i].type().get(ID_identifier)
                                   : tparams[i].get(ID_identifier);
            auto pa_it = cpp_typecheck.template_map.pack_args_map.find(pid);
            if(pa_it != cpp_typecheck.template_map.pack_args_map.end())
            {
              for(const auto &pt : pa_it->second)
                expanded.push_back(exprt(ID_type, pt));
              continue;
            }
          }
          expanded.push_back(guessed_template_args.arguments()[i]);
        }
        instantiation_args.arguments().swap(expanded);
      }

      // check: we can now typecheck the partial_specialization_args
      // If typechecking fails (e.g., accessing a member of a non-class
      // type), treat it as a substitution failure (SFINAE) and skip
      // this specialization.
      cpp_template_args_tct partial_specialization_args_tc;
      bool sfinae_failed = false;
      {
        // [temp.deduct]/8: type-checking the partial specialization's
        // argument list to decide whether it matches is a substitution
        // in the immediate context; a failure here (e.g. an ill-formed
        // `void_t<decltype(false ? a : b)>` SFINAE argument whose
        // conditional has no common type, the libstdc++ common_reference
        // shape) is a deduction failure that removes this specialization
        // from consideration, NOT a diagnosable error.  Use an
        // `sfinae_contextt` (null message handler) so the failure is
        // silent, mirroring the partial-spec verification in
        // `elaborate_class_template`.
        // N5008 [temp.spec.partial.match] + [temp.inst]/1: deciding
        // whether a partial specialization matches is template argument
        // DEDUCTION; it is not a context that requires any
        // completely-defined type, so type-checking the pattern must
        // not implicitly instantiate class templates named in it.
        // Without suppression, disambiguating e.g. `hash<K>` against
        // the pattern `hash<vector<bool, _Alloc>>` (stl_bvector.h)
        // eagerly instantiated `vector` -- with the pattern's
        // parameters resolved through the ENCLOSING instantiation's
        // template map (cross-template capture), producing hybrid
        // instances like vector<bool, allocator<K>> and, transitively,
        // permanently truncated cached instances (__alloc_traits with
        // its rebind/value_type members dropped) that later broke
        // vector<K>::push_back.  elaborate_class_template's matcher
        // already suppresses; mirror it here.
        bool old_suppress_pattern = cpp_typecheck.suppress_elaborate;
        cpp_typecheck.suppress_elaborate = true;
        try
        {
          sfinae_contextt sfinae_guard{cpp_typecheck};
          // For a trailing-pack partial spec the written argument list ends in
          // `T...`, which must be expanded to the deduced pack elements so the
          // completed list can be compared for equality against the
          // instantiation's arguments; keep pack expansion enabled in that
          // case.  Otherwise disable it (the established SFINAE behaviour).
          cpp_typecheck.disable_template_arg_pack_expansion =
            !partial_trailing_pack;
          partial_specialization_args_tc =
            cpp_typecheck.typecheck_template_args(
              source_location,
              primary_template_symbol,
              partial_specialization_args);
          cpp_typecheck.disable_template_arg_pack_expansion = false;
        }
        catch(...)
        {
          cpp_typecheck.disable_template_arg_pack_expansion = false;
          sfinae_failed = true;
        }
        cpp_typecheck.suppress_elaborate = old_suppress_pattern;
      }
      if(sfinae_failed)
        continue;

      // if these match the arguments, we have a match

      // Strip ellipsis flags from cpp_declaration declarators in code
      // type arguments. When a variadic pack parameter (Args...) is
      // substituted with concrete types, the ellipsis flag remains on
      // the declarator but is absent from the full template args.
      for(auto &arg : partial_specialization_args_tc.arguments())
      {
        if(arg.id() != ID_type || arg.type().id() != ID_code)
          continue;
        for(auto &param : arg.type().add(ID_parameters).get_sub())
        {
          if(param.id() != ID_cpp_declaration)
            continue;
          for(auto &decl : static_cast<cpp_declarationt &>(param).declarators())
            decl.remove(ID_ellipsis);
        }
      }

      // If the argument counts differ (e.g. because a pack-expansion
      // argument was expanded on one side but the partial specialization
      // keeps an unexpanded pack), this partial specialization cannot match
      // -- the equality check below requires equal arity.  Skip it rather
      // than asserting.
      if(
        partial_specialization_args_tc.arguments().size() !=
        full_template_args_tc.arguments().size())
      {
        continue;
      }

      if(partial_specialization_args_tc == full_template_args_tc)
      {
        // Also check that cv-qualifiers and #c_type match, since
        // operator== ignores #-prefixed attributes like C_constant,
        // C_volatile, and C_c_type (needed to distinguish char from
        // signed char, and const T* from T*).
        bool qualifiers_match = true;
        for(std::size_t j = 0;
            j < partial_specialization_args_tc.arguments().size();
            j++)
        {
          const exprt &p = partial_specialization_args_tc.arguments()[j];
          const exprt &f = full_template_args_tc.arguments()[j];
          if(p.id() == ID_type)
          {
            if(
              !qualifiers_match_recursively(p.type(), f.type()) ||
              p.type().get(ID_C_c_type) != f.type().get(ID_C_c_type))
            {
              qualifiers_match = false;
              break;
            }
          }
        }

        if(qualifiers_match)
        {
          // Count constrained arguments: arguments in the partial
          // specialization pattern that are not just a plain template
          // parameter name. More constrained = more specialized.
          // Also count repeated parameter names as constraints
          // (e.g., <T, T> constrains both args to be equal).
          std::size_t constrained = 0;
          std::size_t repeated_params = 0;
          std::set<irep_idt> seen_params;
          for(const auto &arg : partial_specialization_args.arguments())
          {
            // Get the actual node, unwrapping ambiguous and type
            const irept *a = &arg;
            if(a->id() == ID_type)
              a = &arg.type();
            if(a->id() == ID_ambiguous)
              a = &a->find(ID_type);

            if(a->id() != ID_cpp_name)
            {
              constrained++;
            }
            else
            {
              // A cpp_name with template arguments (e.g., pack<Rp...>)
              // is more constrained than a plain name.
              bool has_tmpl_args = false;
              irep_idt param_name;
              for(const auto &sub : a->get_sub())
              {
                if(sub.id() == ID_template_args)
                {
                  has_tmpl_args = true;
                  break;
                }
                if(sub.id() == ID_name)
                  param_name = sub.get(ID_identifier);
              }
              if(has_tmpl_args)
                constrained++;
              else if(
                !param_name.empty() && !seen_params.insert(param_name).second)
              {
                // Same parameter used again — equality constraint
                constrained++;
                repeated_params++;
              }
            }
          }
          // Add weight from requires clause constraints.
          // Count the number of atomic constraints (type predicates,
          // function calls) in the expression for proper ordering
          // per [temp.constr.order].
          const auto &req_str =
            cpp_declaration.template_type().get(ID_C_requires_clause);
          if(!req_str.empty() && isdigit(id2string(req_str)[0]))
            constrained += std::stoull(id2string(req_str));
          else if(cpp_declaration.template_type()
                    .find(ID_C_requires_clause)
                    .is_not_nil())
          {
            const auto &req_expr =
              cpp_declaration.template_type().find(ID_C_requires_clause);
            // Count atomic constraints by visiting the expression tree
            std::function<std::size_t(const irept &)> count_atoms =
              [&](const irept &node) -> std::size_t
            {
              if(node.id() == ID_and || node.id() == ID_or)
              {
                std::size_t n = 0;
                for(const auto &sub : node.get_sub())
                  n += count_atoms(sub);
                return n;
              }
              if(node.id() == ID_not)
                return count_atoms(node.get_sub().front());
              return 1;
            };
            constrained += count_atoms(req_expr);
          }

          // [temp.constr.decl]: evaluate the requires clause to check
          // if the constraint is satisfied for the deduced arguments.
          // If not satisfied, skip this specialization.
          //
          // Only evaluate type-predicate constraints (e.g.,
          // __is_pointer(T)) that can be resolved without full
          // type-checking. Complex constraints are deferred to
          // elaborate_class_template.
          {
            const exprt &req_clause = static_cast<const exprt &>(
              cpp_declaration.template_type().find(ID_C_requires_clause));
            if(req_clause.is_not_nil() && req_clause.id() != ID_nil)
            {
              exprt req_copy = req_clause;
              cpp_typecheck.template_map.apply(req_copy);
              // Try to evaluate the constraint. Use typecheck_expr
              // in a safe context: suppress elaboration and catch
              // all errors. If evaluation fails, treat as satisfied
              // and let elaborate_class_template re-check later.
              // error count save/restore instead of null_handler
              const std::size_t sfinae_err_1 =
                cpp_typecheck.get_message_handler().get_message_count(
                  messaget::M_ERROR);
              bool satisfied = true;
              bool evaluated = false;
              // Only attempt evaluation for simple type predicates
              // and boolean combinations. Skip complex expressions
              // that might trigger invariant violations.
              if(
                req_copy.id() == ID_and || req_copy.id() == ID_or ||
                id2string(req_copy.id()).find("__is_") == 0 ||
                id2string(req_copy.id()).find("__has_") == 0)
              {
                try
                {
                  cpp_typecheck.typecheck_expr(req_copy);
                  simplify(req_copy, cpp_typecheck);
                  if(req_copy.is_false())
                    satisfied = false;
                  evaluated = true;
                }
                catch(...)
                {
                }
              }
              cpp_typecheck.get_message_handler().set_message_count(
                messaget::M_ERROR, sfinae_err_1);
              if(evaluated && !satisfied)
                continue;
            }
          }

          matches.push_back(matcht(
            guessed_template_args,
            full_template_args_tc,
            id,
            constrained,
            repeated_params));
          // Record the pack-expanded specialization arguments for instantiation
          // (see [temp.variadic]/5 note above); cost/ordering stay based on the
          // un-expanded `guessed_template_args` passed to the constructor.
          matches.back().instantiation_args = instantiation_args;
        }
      }
    }
  }

  CHECK_RETURN(!matches.empty());

  std::sort(matches.begin(), matches.end());

#if 0
  for(std::vector<matcht>::const_iterator
      m_it=matches.begin();
      m_it!=matches.end();
      m_it++)
  {
    std::cout << "M: " << m_it->cost
              << " " << m_it->id << '\n';
  }

  std::cout << '\n';
#endif

  const matcht &match = *matches.begin();

  const symbolt &choice = cpp_typecheck.lookup(match.id);

#if 0
  // build instance
  const symbolt &instance=
    cpp_typecheck.instantiate_template(
      source_location,
      choice,
      match.specialization_args,
      match.full_args);

  if(instance.type.id()!=ID_struct)
  {
    cpp_typecheck.error().source_location=source_location;
    cpp_typecheck.error() << "template '"
                      << base_name << "' is not a class" << messaget::eom;
    throw 0;
  }

  struct_tag_typet result(instance.name);
  result.add_source_location()=source_location;

  return result;
#else

  // build instance
  const symbolt &instance = cpp_typecheck.class_template_symbol(
    source_location, choice, match.instantiation_args, match.full_args);

  typet result;
  if(instance.type.id() == ID_union)
    result = union_tag_typet(instance.name);
  else
    result = struct_tag_typet(instance.name);
  result.add_source_location() = source_location;

  return result;
#endif
}

typet cpp_typecheck_resolvet::resolve_template_alias(
  const irep_idt &base_name,
  const cpp_scopest::id_sett &id_set,
  const cpp_template_args_non_tct &full_template_args)
{
  // Break mutual-recursion cycles between SFINAE-guarded template
  // aliases: MSVC's `add_rvalue_reference_t<T>` expansion path
  //   add_rvalue_reference_t<T>
  //   -> _Add_reference<T, void_t<T&>>::_Rvalue
  //   -> void_t<T&>  (specialisation selection)
  //   -> requires resolving T&, which re-resolves T
  //   -> re-enters add_rvalue_reference_t<T>...
  // triggers unbounded recursion when T is a partially-elaborated
  // class-template instance.  Detect the cycle by tracking which
  // (base_name, full_template_args) pairs are currently being
  // resolved on this thread and short-circuit a re-entry with
  // an empty type (the most conservative placeholder).
  // Break mutual-recursion cycles between SFINAE-guarded template
  // aliases ([temp.alias]).  A canonical cycle:
  //
  //   add_rvalue_reference_t<T>
  //     -> _Add_reference<T, void_t<T&>>::_Rvalue
  //     -> void_t<T&>  (specialisation selection)
  //     -> resolves T  (may re-enter add_rvalue_reference_t<T>)
  //
  // When T is a partially-elaborated class-template instance, a
  // naive resolver loops unbounded.  Maintain a thread-local set of
  // (alias-name, full-args) pairs that are currently being
  // resolved; re-entry with the same pair returns a conservative
  // placeholder (`empty_typet{}`, which composes like `void_t<...>`
  // does).
  //
  // Note: we deliberately do *not* cache *successful* results
  // across the entire thread lifetime.  Two textually-identical
  // `irept` argument lists may legitimately denote different types
  // depending on the scope in which they are resolved (e.g. a
  // `cpp_name` may resolve differently in one class-body scope vs.
  // another).  A scope-agnostic cache was tried and regressed
  // several CORE tests (cpp11_deque_pushback,
  // cpp11_string_default_arg_sstream, cpp17_deque_basic) by
  // returning stale types from a prior scope.  Keep the fix minimal
  // (cycle break only) until the medium-term lazy-elaboration work
  // introduces scope-keyed memoization.
  static thread_local std::set<std::pair<irep_idt, irept>> active;
  const irept &args_irep = static_cast<const irept &>(full_template_args);
  std::pair<irep_idt, irept> key{base_name, args_irep};
  if(!active.insert(key).second)
    return empty_typet{};
  struct guardt
  {
    std::set<std::pair<irep_idt, irept>> &s;
    std::pair<irep_idt, irept> k;
    ~guardt()
    {
      s.erase(k);
    }
  } guard{active, key};

  // find the template alias symbol
  const symbolt *template_sym = nullptr;
  const cpp_idt *template_id_entry = nullptr;
  for(const auto &id_ptr : id_set)
  {
    const symbolt &s = cpp_typecheck.lookup(id_ptr->identifier);
    if(!s.type.get_bool(ID_is_template))
      continue;
    if(to_cpp_declaration(s.type).is_template_alias())
    {
      template_sym = &s;
      template_id_entry = id_ptr;
      break;
    }
  }

  INVARIANT(template_sym != nullptr, "template alias symbol must exist");

  // N5008 [temp.alias] + [temp.mem]: a member alias template of a
  // class-template SPECIALIZATION is instantiated with the enclosing
  // specialization's template arguments bound in addition to its own
  // (libc++'s `__integer_sequence<_Tp, _Values...>::__to_tuple_indices
  // <_Sp> = __tuple_indices<(_Values + _Sp)...>` needs the instance's
  // _Values pack).  instantiate_template builds only the alias's own
  // parameter map, so pre-bind the enclosing instance's parameters --
  // exactly as add_method_body does for member function bodies.
  cpp_saved_template_mapt saved_enclosing_map(cpp_typecheck.template_map);
  // Gated to the CLANG preprocessor mode: the motivating member alias
  // templates are libc++'s (__integer_sequence::__to_tuple_indices);
  // libstdc++ resolution never needed the enclosing pre-bind, and even
  // the non-overriding form perturbed some libstdc++ shapes.
  if(
    template_id_entry != nullptr &&
    config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::CLANG)
  {
    const cpp_idt *scope_walk = template_id_entry->has_parent()
                                  ? &template_id_entry->get_parent()
                                  : nullptr;
    while(scope_walk != nullptr)
    {
      const irep_idt &class_id = scope_walk->class_identifier.empty()
                                   ? scope_walk->identifier
                                   : scope_walk->class_identifier;
      const symbolt *class_sym = cpp_typecheck.symbol_table.lookup(class_id);
      // N5008 [temp.spec.partial.match]: for an instance of a PARTIAL
      // specialization, the enclosing parameters were bound by deduction
      // against the argument pattern; replay the persisted deduction-time
      // bindings (#spec_template_packs, written by instantiate_template) --
      // the positional pairing below cannot express multi-pack or
      // non-trailing-pack bindings.  Non-overriding, like the rest of
      // this pre-bind.
      if(
        class_sym != nullptr &&
        class_sym->type.find(irep_idt{"#spec_template_packs"}).is_not_nil())
      {
        const irept &bindings =
          class_sym->type.find(irep_idt{"#spec_template_packs"});
        for(const auto &entry : bindings.get_sub())
        {
          const irep_idt pid = entry.get(ID_identifier);
          if(pid.empty())
            continue;
          auto &map = cpp_typecheck.template_map;
          if(entry.id() == irep_idt{"pack_types"})
          {
            if(map.pack_size_map.find(pid) != map.pack_size_map.end())
              continue;
            std::vector<typet> elems;
            for(const auto &t : entry.get_sub())
              elems.push_back(static_cast<const typet &>(t));
            map.pack_size_map[pid] = elems.size();
            if(!elems.empty())
            {
              if(elems.size() == 1)
                map.type_map.emplace(pid, elems.front());
              map.pack_args_map[pid] = std::move(elems);
            }
          }
          else if(entry.id() == irep_idt{"pack_exprs"})
          {
            if(map.pack_size_map.find(pid) != map.pack_size_map.end())
              continue;
            std::vector<exprt> vals;
            for(const auto &e : entry.get_sub())
              vals.push_back(static_cast<const exprt &>(e));
            map.pack_size_map[pid] = vals.size();
            if(!vals.empty())
            {
              if(vals.size() == 1)
                map.expr_map.emplace(pid, vals.front());
              map.pack_expr_map[pid] = std::move(vals);
            }
          }
          else if(
            entry.id() == irep_idt{"scalar_type"} && !entry.get_sub().empty())
          {
            map.type_map.emplace(
              pid, static_cast<const typet &>(entry.get_sub().front()));
          }
          else if(
            entry.id() == irep_idt{"scalar_expr"} && !entry.get_sub().empty())
          {
            map.expr_map.emplace(
              pid, static_cast<const exprt &>(entry.get_sub().front()));
          }
        }
      }

      if(
        class_sym != nullptr &&
        class_sym->type.find(ID_C_template).is_not_nil() &&
        class_sym->type.find(ID_C_template_arguments).is_not_nil())
      {
        // NON-OVERRIDING: bind only parameters that the current map
        // does not already bind.  The resolution may run while another
        // specialization of the same enclosing template is being
        // instantiated; its live bindings are authoritative
        // ([temp.mem], [temp.spec.general]) and overriding them with
        // the alias registration parent's arguments regressed the
        // libstdc++ container tests into state-space blowups.
        const auto &enc_template = static_cast<const template_typet &>(
          class_sym->type.find(ID_C_template));
        const auto &enc_args = static_cast<const cpp_template_args_tct &>(
          class_sym->type.find(ID_C_template_arguments));
        const auto &enc_params = enc_template.template_parameters();
        const auto &enc_arg_list = enc_args.arguments();
        for(std::size_t k = 0; k < enc_params.size() && k < enc_arg_list.size();
            ++k)
        {
          const auto &param = enc_params[k];
          // A parameter PACK consumes a variable number of arguments;
          // beyond it the positional pairing is meaningless, and pack
          // bindings themselves need build()'s pack machinery
          // (pack_args_map).  Stop here -- the packs that motivated
          // this pre-binding (__integer_sequence's _Values) are bound
          // by instantiate_template itself when the alias's OWN
          // arguments cover them; the leading non-pack parameters are
          // what the alias body needs from the enclosing instance.
          if(param.get_bool(ID_ellipsis))
          {
            // A TRAILING pack consumes all remaining arguments; bind
            // it through the pack machinery (mirroring build()), so
            // pack-arithmetic member alias bodies such as
            // `iseqt<T, (Is + S)...>` can expand.  Only when the pack
            // is the LAST parameter -- otherwise the positional
            // pairing is ambiguous -- and only if unbound
            // (non-overriding, as for the scalar entries).
            if(k + 1 != enc_params.size())
              break;
            const irep_idt pack_id = param.id() == ID_type
                                       ? param.type().get(ID_identifier)
                                       : param.get(ID_identifier);
            if(
              pack_id.empty() ||
              cpp_typecheck.template_map.pack_size_map.find(pack_id) !=
                cpp_typecheck.template_map.pack_size_map.end())
            {
              break;
            }
            std::vector<typet> pack_types;
            std::vector<exprt> pack_exprs;
            for(std::size_t j = k; j < enc_arg_list.size(); ++j)
            {
              if(enc_arg_list[j].id() == ID_type)
                pack_types.push_back(enc_arg_list[j].type());
              else
                pack_exprs.push_back(enc_arg_list[j]);
            }
            cpp_typecheck.template_map.pack_size_map[pack_id] =
              enc_arg_list.size() - k;
            if(!pack_types.empty())
            {
              if(pack_types.size() == 1)
                cpp_typecheck.template_map.type_map[pack_id] =
                  pack_types.front();
              cpp_typecheck.template_map.pack_args_map[pack_id] =
                std::move(pack_types);
            }
            else if(!pack_exprs.empty())
            {
              if(pack_exprs.size() == 1)
                cpp_typecheck.template_map.expr_map[pack_id] =
                  pack_exprs.front();
              cpp_typecheck.template_map.pack_expr_map[pack_id] =
                std::move(pack_exprs);
            }
            break;
          }
          const exprt &arg = enc_arg_list[k];
          if(param.id() == ID_type)
          {
            const irep_idt &pid = param.type().get(ID_identifier);
            if(
              !pid.empty() && arg.id() == ID_type &&
              cpp_typecheck.template_map.type_map.find(pid) ==
                cpp_typecheck.template_map.type_map.end())
            {
              cpp_typecheck.template_map.set(param, arg);
            }
          }
          else
          {
            const irep_idt &pid = param.get(ID_identifier);
            if(
              !pid.empty() && arg.id() != ID_type &&
              cpp_typecheck.template_map.expr_map.find(pid) ==
                cpp_typecheck.template_map.expr_map.end())
            {
              cpp_typecheck.template_map.set(param, arg);
            }
          }
        }
        break;
      }
      if(
        (!scope_walk->is_class() && !scope_walk->is_scope) ||
        !scope_walk->has_parent())
      {
        break;
      }
      const cpp_idt &next = scope_walk->get_parent();
      if(&next == scope_walk)
        break;
      scope_walk = &next;
    }
  }

  // typecheck template arguments
  cpp_template_args_tct template_args_tc;
  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
    cpp_typecheck.cpp_scopes.go_to(*original_scope);
    template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, *template_sym, full_template_args);
  }

  const symbolt &instance = cpp_typecheck.instantiate_template(
    source_location, *template_sym, template_args_tc, template_args_tc);

  return instance.type;
}

cpp_scopet &cpp_typecheck_resolvet::resolve_namespace(const cpp_namet &cpp_name)
{
  irep_idt base_name;
  cpp_template_args_non_tct template_args;
  template_args.make_nil();

  cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
  resolve_scope(cpp_name, base_name, template_args);

  // Substitute destructor names: ~_Tp where _Tp is a template parameter.
  if(
    !base_name.empty() && id2string(base_name)[0] == '~' &&
    id2string(base_name).size() > 1)
  {
    std::string after_tilde = id2string(base_name).substr(1);
    for(const auto &entry : cpp_typecheck.template_map.type_map)
    {
      const std::string &key = id2string(entry.first);
      auto p = key.rfind("::");
      std::string suffix = p != std::string::npos ? key.substr(p + 2) : key;
      if(
        suffix == after_tilde && entry.second.id() != ID_unassigned &&
        entry.second.id() != ID_nil && entry.second.id() == ID_struct_tag)
      {
        // Get the struct's base name for the destructor; the final path
        // component must be found ANGLE-AWARE (see the matching
        // substitution in resolve_scope): a naive rfind("::") lands
        // inside a template instance's ARGUMENTS.
        const irep_idt &tag = to_struct_tag_type(entry.second).get_identifier();
        std::string tag_str = id2string(tag);
        {
          std::size_t depth = 0;
          std::size_t final_component = 0;
          for(std::size_t i = 0; i + 1 < tag_str.size(); ++i)
          {
            if(tag_str[i] == '<')
              ++depth;
            else if(tag_str[i] == '>' && depth > 0)
              --depth;
            else if(depth == 0 && tag_str[i] == ':' && tag_str[i + 1] == ':')
              final_component = i + 2;
          }
          tag_str = tag_str.substr(final_component);
        }
        if(tag_str.substr(0, 4) == "tag-")
          tag_str = tag_str.substr(4);
        // Remove template args for destructor name
        auto angle = tag_str.find('<');
        if(angle != std::string::npos)
          tag_str = tag_str.substr(0, angle);
        base_name = "~" + tag_str;
        break;
      }
    }
  }

  bool qualified = cpp_name.is_qualified();
  (void)qualified;

  auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
    base_name, cpp_scopet::RECURSIVE);

  filter_for_namespaces(id_set);

  if(id_set.empty())
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "namespace '" << base_name << "' not found"
                          << messaget::eom;
    throw 0;
  }
  else if(id_set.size() == 1)
  {
    cpp_idt &id = **id_set.begin();
    return (cpp_scopet &)id;
  }
  else
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "namespace '" << base_name << "' is ambiguous"
                          << messaget::eom;
    throw 0;
  }
}

void cpp_typecheck_resolvet::show_identifiers(
  const irep_idt &base_name,
  const resolve_identifierst &identifiers,
  std::ostream &out)
{
  for(const auto &id_expr : identifiers)
  {
    out << "  ";

    if(id_expr.id() == ID_type)
    {
      out << "type " << cpp_typecheck.to_string(id_expr.type());
    }
    else
    {
      irep_idt id;

      if(id_expr.type().get_bool(ID_is_template))
        out << "template ";

      if(id_expr.id() == ID_member)
      {
        out << "member ";
        id = "." + id2string(base_name);
      }
      else if(id_expr.id() == ID_pod_constructor)
      {
        out << "constructor ";
        id.clear();
      }
      else if(id_expr.id() == ID_template_function_instance)
      {
        out << "symbol ";
      }
      else
      {
        out << "symbol ";
        id = cpp_typecheck.to_string(id_expr);
      }

      if(id_expr.type().get_bool(ID_is_template))
      {
      }
      else if(id_expr.type().id() == ID_code)
      {
        const code_typet &code_type = to_code_type(id_expr.type());
        const typet &return_type = code_type.return_type();
        const code_typet::parameterst &parameters = code_type.parameters();
        out << cpp_typecheck.to_string(return_type);
        out << " " << id << "(";

        bool first = true;

        for(const auto &parameter : parameters)
        {
          const typet &parameter_type = parameter.type();

          if(first)
            first = false;
          else
            out << ", ";

          out << cpp_typecheck.to_string(parameter_type);
        }

        if(code_type.has_ellipsis())
        {
          if(!parameters.empty())
            out << ", ";
          out << "...";
        }

        out << ")";
      }
      else
        out << id << ": " << cpp_typecheck.to_string(id_expr.type());

      if(id_expr.id() == ID_symbol)
      {
        const symbolt &symbol = cpp_typecheck.lookup(to_symbol_expr(id_expr));
        out << " (" << symbol.location << ")";
      }
      else if(id_expr.id() == ID_template_function_instance)
      {
        const symbolt &symbol =
          cpp_typecheck.lookup(id_expr.type().get(ID_C_template));
        out << " (" << symbol.location << ")";
      }
    }

    out << '\n';
  }
}

exprt cpp_typecheck_resolvet::resolve(
  const cpp_namet &cpp_name,
  const wantt want,
  const cpp_typecheck_fargst &fargs,
  bool fail_with_exception)
{
  irep_idt base_name;
  cpp_template_args_non_tct template_args;
  template_args.make_nil();

  // Clear any pending "no viable function" marker on entry: it is only
  // meaningful while a specific failed resolution's `throw 0` propagates
  // straight to a body conversion.  Entering another resolution means an
  // intervening (typically recovering) resolution is happening, so a stale
  // marker must not leak into it.
  cpp_typecheck.pending_no_viable_call = false;

  original_scope = &cpp_typecheck.cpp_scopes.current_scope();
  cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

  // this changes the scope
  resolve_scope(cpp_name, base_name, template_args);

  // A pseudo/explicit destructor written with a template-id, e.g.
  // `p->~Foo<T>()` (as in libstdc++'s `__node->~_Rb_tree_node<_Val>()`),
  // names the destructor of the class Foo<T>.  The template arguments only
  // restate the class type; they are not a template-id to be instantiated
  // ([expr.prim.id.dtor], [class.dtor]).  resolve_scope already reduced the
  // base name to `~Foo`, so drop the arguments here too, otherwise
  // resolution would try (and fail) to instantiate `~Foo` as a template.
  if(!base_name.empty() && id2string(base_name)[0] == '~')
    template_args.make_nil();

  // Clang's builtin alias template `__type_pack_element<N, Ts...>`
  // names the N-th type of the pack (libc++ implements
  // tuple_element<I, tuple<Ts...>>::type with it).  It is not an
  // ordinary template; evaluate it directly.
  if(
    base_name == "__type_pack_element" && template_args.is_not_nil() &&
    template_args.arguments().size() >= 1)
  {
    exprt count = template_args.arguments()[0];
    if(count.id() == ID_type || count.id() == ID_ambiguous)
      count =
        static_cast<const exprt &>(static_cast<const irept &>(count.type()));
    // N5008 [temp.param]/8: within an instantiation context a non-type
    // template parameter name denotes its bound argument.  A count that is
    // (still) a bare parameter reference -- e.g. `_Idx` in libc++'s
    // `__apply_cv_t<_Tp, __type_pack_element<_Idx, _Types...>>` after the
    // enclosing expansion bound the packs -- must be substituted from the
    // template map; the general expression resolution below does not
    // consult expr_map for such names and mis-resolves them.
    if(count.id() == ID_cpp_name)
    {
      const auto &csub = static_cast<const irept &>(count).get_sub();
      if(csub.size() == 1 && csub.front().id() == ID_name)
      {
        const irep_idt cname = csub.front().get(ID_identifier);
        for(const auto &entry : cpp_typecheck.template_map.expr_map)
        {
          const std::string key = id2string(entry.first);
          const auto pos = key.rfind("::");
          if(
            (pos != std::string::npos ? key.substr(pos + 2) : key) ==
            id2string(cname))
          {
            count = entry.second;
            break;
          }
        }
      }
    }
    std::optional<mp_integer> n;
    try
    {
      cpp_typecheck.typecheck_expr(count);
      simplify(count, cpp_typecheck);
      n = numeric_cast<mp_integer>(count);
    }
    catch(...)
    {
      // dependent count: fall through to the substitution-failure throw
    }

    // N5008 [temp.variadic]/5: a pack-expansion argument `Ts...`
    // stands for one argument per pack element.  During return-type
    // substitution ([temp.deduct]/5) the arguments still carry the
    // unexpanded expansion node; splice the deduced pack elements
    // from the map before indexing, otherwise the N-th "argument" is
    // the expansion node itself and its type-check rejects the whole
    // candidate (the libc++ std::get<I>(tuple&) return type,
    // KNOWNBUG cpp11_type_pack_element_return).
    std::vector<typet> element_types;
    for(std::size_t ai = 1; ai < template_args.arguments().size(); ++ai)
    {
      const exprt &arg = template_args.arguments()[ai];
      const irept &arg_irep = static_cast<const irept &>(arg);
      const bool is_expansion =
        arg.get_bool(ID_ellipsis) || arg.type().get_bool(ID_ellipsis);
      irep_idt pack_name;
      if(is_expansion)
      {
        const irept *t = &static_cast<const irept &>(arg.type());
        if(arg_irep.id() == ID_cpp_name)
          t = &arg_irep;
        if(t->id() == ID_cpp_name)
        {
          const auto &sub = t->get_sub();
          if(sub.size() == 1 && sub.front().id() == ID_name)
            pack_name = sub.front().get(ID_identifier);
        }
      }
      if(!pack_name.empty())
      {
        // find the pack binding by short name
        const std::vector<typet> *pack = nullptr;
        for(const auto &entry : cpp_typecheck.template_map.pack_args_map)
        {
          const std::string key = id2string(entry.first);
          const auto pos = key.rfind("::");
          if(
            (pos != std::string::npos ? key.substr(pos + 2) : key) ==
            id2string(pack_name))
          {
            pack = &entry.second;
            break;
          }
        }
        if(pack == nullptr)
        {
          // unexpandable here: dependent context
          throw 0;
        }
        for(const auto &pt : *pack)
          element_types.push_back(pt);
      }
      else if(arg.id() == ID_type || arg.id() == ID_ambiguous)
      {
        element_types.push_back(arg.type());
      }
      else if(arg_irep.id() == ID_cpp_name || arg_irep.id() == ID_merged_type)
      {
        element_types.push_back(static_cast<const typet &>(arg_irep));
      }
      else
      {
        // not a type argument shape we can evaluate here
        throw 0;
      }
    }

    if(n.has_value() && *n >= 0 && *n < mp_integer(element_types.size()))
    {
      typet result = element_types[numeric_cast_v<std::size_t>(*n)];
      // An `ambiguous` argument may carry a nil type (an
      // expression-flavoured argument); that is not a type pack
      // element -- substitution failure, not a crash in
      // typecheck_type.
      if(result.is_nil())
        throw 0;
      cpp_typecheck.typecheck_type(result);
      exprt result_expr{ID_type};
      result_expr.type() = result;
      return result_expr;
    }
    // Dependent or out-of-range: substitution failure.
    throw 0;
  }

#ifdef DEBUG
  std::cout << "base name: " << base_name << '\n';
  std::cout << "template args: " << template_args.pretty() << '\n';
  std::cout << "original-scope: " << original_scope->prefix << '\n';
  std::cout << "scope: " << cpp_typecheck.cpp_scopes.current_scope().prefix
            << '\n';
#endif

  bool qualified = cpp_name.is_qualified();

  // do __CPROVER scope
  if(qualified)
  {
    if(cpp_typecheck.cpp_scopes.current_scope().identifier == "__CPROVER")
      return do_builtin(base_name, fargs, template_args);
  }
  else
  {
    if(
      base_name == "__func__" || base_name == "__FUNCTION__" ||
      base_name == "__PRETTY_FUNCTION__")
    {
      // __func__ is an ANSI-C standard compliant hack to get the function name
      // __FUNCTION__ and __PRETTY_FUNCTION__ are GCC-specific
      string_constantt s(source_location.get_function());
      s.add_source_location() = source_location;
      return std::move(s);
    }
  }

  cpp_scopest::id_sett id_set;

  cpp_scopet::lookup_kindt lookup_kind = cpp_scopet::RECURSIVE;

  if(template_args.is_nil())
  {
    id_set =
      cpp_typecheck.cpp_scopes.current_scope().lookup(base_name, lookup_kind);

    if(id_set.empty() && !cpp_typecheck.builtin_factory(base_name))
    {
      cpp_idt &builtin_id =
        cpp_typecheck.cpp_scopes.get_root_scope().insert(base_name);
      builtin_id.identifier = base_name;
      builtin_id.id_class = cpp_idt::id_classt::SYMBOL;

      id_set.insert(&builtin_id);
    }
  }
  else
    id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
      base_name, lookup_kind, cpp_idt::id_classt::TEMPLATE);

  // If no template was found, check if the name is a template template
  // parameter and resolve it via the template map.
  if(id_set.empty() && template_args.is_not_nil())
  {
    const auto param_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
      base_name, lookup_kind, cpp_idt::id_classt::TEMPLATE_PARAMETER);
    if(!param_set.empty())
    {
      const cpp_idt &param_id = **param_set.begin();
      exprt e = cpp_typecheck.template_map.lookup(param_id.identifier);
      if(e.is_nil() || (e.id() == ID_type && e.type().is_nil()))
      {
        const std::string id_str = id2string(param_id.identifier);
        auto p = id_str.rfind("::");
        if(p != std::string::npos)
          e = cpp_typecheck.template_map.lookup_by_suffix(
            id_str.substr(p + 2), param_id.identifier);
      }
      if(
        e.id() == ID_type && e.type().id() == ID_template_parameter_symbol_type)
      {
        const irep_idt &tmpl_id =
          to_template_parameter_symbol_type(e.type()).get_identifier();
        // The template identifier is like "template.MyVec<Type0>" or
        // "std::template.MyVec<Type0>". Look up the template symbol
        // in the symbol table and find its scope entry.
        if(cpp_typecheck.symbol_table.has_symbol(tmpl_id))
        {
          const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
          irep_idt tmpl_base = tmpl_sym.base_name;
          // Search from root scope to find the template
          auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
            tmpl_base, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
          for(const auto &f : found)
            id_set.insert(f);
        }
      }
    }
  }

  // Argument-dependent name lookup (ADL / Koenig lookup):
  // For unqualified calls, also search in the namespaces of the
  // argument types. This is required for e.g. operator+(string, string)
  // to be found when called from outside namespace std.
  //
  // N5008 [basic.lookup.argdep]/3.1: if the ordinary unqualified lookup of the
  // name finds the declaration of a class member, the associated namespaces and
  // classes are NOT considered (ADL is suppressed).  Without this an unqualified
  // member call such as `find(x)` inside a member function -- which ordinary
  // lookup resolves to `this->find` -- would also pull in a same-named member of
  // the argument's class (e.g. `std::basic_string::find` when `x` is a
  // `std::string`), making the call ambiguous.  Operators are excluded: they use
  // the separate [over.match.oper] candidate-gathering, which always includes
  // ADL-found non-member operators regardless of any member operator.
  bool ordinary_lookup_found_member = false;
  for(const auto *id : id_set)
  {
    if(!id->class_identifier.empty())
    {
      ordinary_lookup_found_member = true;
      break;
    }
  }
  const bool is_operator_name =
    id2string(base_name).compare(0, 8, "operator") == 0 &&
    cpp_typecheck.operator_expr_lookup_depth > 0;
  // Snapshot the candidates produced by ordinary (scope) lookup, before
  // ADL augments the set below.  The [class.member.lookup]/4 hiding rule
  // must only prune base-class members that resolve_with_arguments (ADL)
  // conservatively *added*.  A base-class member that ordinary lookup
  // already found in the derived class's scope is there because a
  // using-declaration (N5008 [namespace.udecl]/3) imported it into the
  // derived class; per [namespace.udecl]/16 such a member joins the derived
  // class's members of the same name in a single overload set and is NOT
  // hidden.  (Members merely visible through inheritance are represented as
  // flattened `from_base` components whose declaring class is the derived
  // class, so they never trip the base-of test in the first place.)
  const cpp_scopest::id_sett ordinary_lookup_id_set = id_set;

  if(
    !qualified && !fargs.has_object &&
    !(ordinary_lookup_found_member && !is_operator_name))
    resolve_with_arguments(id_set, base_name, fargs);

  // Apply the [class.member.lookup]/4 hiding rule to the combined
  // candidate set: if the set contains members declared in distinct
  // classes B and D, and D derives (directly or transitively) from B,
  // then D's member hides B's same-named member — drop the B entry.
  //
  // CBMC's resolve_with_arguments above conservatively also adds
  // members of associated classes to the ADL candidate set (which is
  // not strictly correct per [basic.lookup.argdep] — only friends
  // declared inside an associated class participate in ADL).  Once
  // that conservative addition has happened, the same hiding rule
  // applies and produces the answer the standard requires.
  //
  // Skip filtering when the lookup is qualified (`B::name`) — in that
  // case the user has explicitly requested the base-class member.
  if(!qualified && id_set.size() >= 2)
  {
    auto is_base_of = [&](const irep_idt &base, const irep_idt &derived) -> bool
    {
      if(base.empty() || derived.empty() || base == derived)
        return false;
      std::set<irep_idt> visited;
      std::vector<irep_idt> todo{derived};
      while(!todo.empty())
      {
        irep_idt d = todo.back();
        todo.pop_back();
        if(!visited.insert(d).second)
          continue;
        const symbolt *sym = cpp_typecheck.symbol_table.lookup(d);
        if(sym == nullptr)
          continue;
        const irept &bases = sym->type.find(ID_bases);
        for(const auto &b : bases.get_sub())
        {
          const typet &bt = static_cast<const typet &>(b.find(ID_type));
          if(bt.id() != ID_struct_tag)
            continue;
          const irep_idt &bid = to_struct_tag_type(bt).get_identifier();
          if(bid == base)
            return true;
          todo.push_back(bid);
        }
      }
      return false;
    };
    cpp_scopest::id_sett filtered;
    for(auto *cand : id_set)
    {
      const irep_idt &cand_class = cand->class_identifier;
      if(cand_class.empty())
      {
        filtered.insert(cand);
        continue;
      }
      // A candidate found by ordinary lookup (i.e. present before ADL
      // augmented the set) is never hidden here: if its declaring class is
      // a base class, it was brought into the derived class by a
      // using-declaration and participates in overload resolution
      // ([namespace.udecl]/16).  Only ADL-added base members are subject to
      // the hiding rule below.
      if(ordinary_lookup_id_set.find(cand) != ordinary_lookup_id_set.end())
      {
        filtered.insert(cand);
        continue;
      }
      bool hidden = false;
      for(auto *other : id_set)
      {
        if(other == cand)
          continue;
        const irep_idt &other_class = other->class_identifier;
        if(other_class.empty() || other_class == cand_class)
          continue;
        // Drop `cand` if its declaring class is a base of `other`'s.
        if(is_base_of(cand_class, other_class))
        {
          hidden = true;
          break;
        }
      }
      if(!hidden)
        filtered.insert(cand);
    }
    if(!filtered.empty() && filtered.size() < id_set.size())
      id_set.swap(filtered);
  }

  // N5008 [over.match.oper]/3.3: for an operator expression `a @ b`, the set of
  // non-member candidates is the result of the unqualified lookup of operator@
  // in the context of the expression "except that all member functions are
  // ignored".  When the expression appears inside a member function of a class
  // that itself declares operator@ -- e.g. `static_cast<std::ostream &>(*this)
  // << x` inside messaget::mstreamt::operator<< -- ordinary unqualified lookup
  // finds that member operator@ and, left in the candidate set, it competes
  // with (and hides) a free operator@ found by argument-dependent lookup (here
  // the standard library's operator<<(basic_ostream<C> &, const char *)),
  // making the free operator unselectable and the built-in shift the only
  // fallback.  Drop genuine member functions (is_method) from the non-member
  // operator candidate set.  Non-member friends declared inside a class have
  // is_method == false and are NOT members, so ADL-found hidden friends still
  // participate ([over.match.oper]/3.3 second bullet, [basic.lookup.argdep]).
  // This only applies to the non-member resolution (has_object == false,
  // unqualified): the member candidate set is gathered by the separate
  // has_object == true resolution in operator_is_overloaded.
  const bool op_nonmember_lookup =
    !qualified && !fargs.has_object && is_operator_name;
  if(op_nonmember_lookup && !id_set.empty())
  {
    cpp_scopest::id_sett non_members;
    for(auto *cand : id_set)
    {
      if(!cand->is_method)
        non_members.insert(cand);
    }
    // Only strip members when a genuine non-member candidate remains.  A set
    // containing ONLY member candidates is left intact: CBMC also reaches this
    // non-member resolution as a fallback for a member operator@ whose
    // has_object resolution did not select a candidate (e.g. a compound-
    // assignment operator@= that is only a member), and emptying the set there
    // would spuriously make the operator "unknown".  The [over.match.oper]/3.3
    // exclusion only needs to fire when a free/ADL operator@ would otherwise be
    // hidden by an in-scope member operator@ of the same name.
    if(!non_members.empty() && non_members.size() < id_set.size())
      id_set.swap(non_members);
  }

  if(id_set.empty() && qualified)
  {
    // The scope might be an un-elaborated template class instance.
    // Try to elaborate it and retry the lookup.
    const cpp_scopet &cur = cpp_typecheck.cpp_scopes.current_scope();
    const auto *scope_sym = cpp_typecheck.symbol_table.lookup(cur.identifier);
    if(
      scope_sym &&
      (scope_sym->type.id() == ID_struct || scope_sym->type.id() == ID_union) &&
      (scope_sym->type.get_bool(ID_template_class_instance) ||
       scope_sym->type.find(ID_C_template).is_not_nil()))
    {
      bool old_suppress = cpp_typecheck.suppress_elaborate;
      cpp_typecheck.suppress_elaborate = false;
      try
      {
        typet tag = scope_sym->type.id() == ID_struct
                      ? static_cast<typet>(struct_tag_typet{scope_sym->name})
                      : static_cast<typet>(union_tag_typet{scope_sym->name});
        cpp_typecheck.elaborate_class_template(tag);
      }
      catch(...)
      {
      }
      cpp_typecheck.suppress_elaborate = old_suppress;
      // Retry lookup after elaboration
      id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::SCOPE_ONLY);
    }
  }

  if(id_set.empty())
  {
    if(!fail_with_exception)
      return nil_exprt();

    cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
    cpp_typecheck.error().source_location = source_location;

    if(qualified)
    {
      // Per [temp.deduct]/8: qualified lookup failure during
      // template instantiation is a substitution failure.
      // Throw silently so SFINAE can handle it.
      throw 0;
    }
    else
    {
      // Destructor names (~X): destructors are implicitly noexcept
      // in C++11+. When a destructor can't be resolved (e.g., because
      // the class isn't fully elaborated during noexcept evaluation),
      // return a dummy noexcept destructor symbol instead of throwing.
      if(!base_name.empty() && id2string(base_name)[0] == '~')
      {
        // Destructor not found — return nil to signal failure
        // without throwing. The noexcept handler will catch this.
        if(!fail_with_exception)
          return nil_exprt();
        // For fail_with_exception=true, throw so the noexcept
        // handler's catch block returns true.
        throw 0;
      }
      // Template template parameters may have "template." prefix.
      // Strip it and retry.
      if(id2string(base_name).substr(0, 9) == "template.")
      {
        irep_idt stripped = id2string(base_name).substr(9);
        id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          stripped, qualified ? cpp_scopet::QUALIFIED : cpp_scopet::RECURSIVE);
        if(!id_set.empty())
          goto resolved_after_strip;
      }
      // C++ [dcl.link]: extern "C" only affects linkage, not name
      // lookup. Try tag-name fallback for struct/class/union tags.
      {
        irep_idt tag_name = "tag-" + id2string(base_name);
        const symbolt *tag_sym = cpp_typecheck.symbol_table.lookup(tag_name);
        if(tag_sym)
        {
          // Found as a tag — create a type expression
          struct_tag_typet tag_type(tag_name);
          exprt type_expr(ID_type);
          type_expr.type() = tag_type;
          type_expr.add_source_location() = source_location;
          return type_expr;
        }
      }
      // If `base_name` already looks like a fully-qualified tag
      // identifier (contains `tag-`), look it up directly.  This
      // happens when pack expansion substitutes a struct_tag's full
      // identifier into a name node (see cpp_instantiate_template.cpp).
      if(id2string(base_name).find("tag-") != std::string::npos)
      {
        const symbolt *tag_sym = cpp_typecheck.symbol_table.lookup(base_name);
        if(tag_sym && tag_sym->is_type)
        {
          struct_tag_typet tag_type(base_name);
          exprt type_expr(ID_type);
          type_expr.type() = tag_type;
          type_expr.add_source_location() = source_location;
          return type_expr;
        }
      }
      // Fallback: the name may be a template parameter that's out
      // of scope (e.g., a method template parameter referenced via
      // a qualified call where resolve_scope has shifted to the
      // target class). Look it up in template_map.
      {
        const std::string bn = id2string(base_name);
        for(const auto &tm : cpp_typecheck.template_map.type_map)
        {
          const std::string full = id2string(tm.first);
          auto p = full.rfind("::");
          const std::string sn =
            p != std::string::npos ? full.substr(p + 2) : full;
          if(sn == bn && tm.second.id() != ID_unassigned)
          {
            exprt type_expr(ID_type);
            type_expr.type() = tm.second;
            type_expr.add_source_location() = source_location;
            return type_expr;
          }
        }
      }
      cpp_typecheck.error() << "symbol '" << base_name << "' is unknown";
    }

    cpp_typecheck.error() << messaget::eom;
    throw 0;
  }
resolved_after_strip:

  resolve_identifierst identifiers;

  if(template_args.is_not_nil())
  {
    // first figure out if we are doing functions/methods or
    // classes
    bool have_classes = false, have_methods = false;
    bool have_aliases = false;

    for(auto it = id_set.begin(); it != id_set.end();)
    {
      const irep_idt id = (*it)->identifier;
      const symbolt &s = cpp_typecheck.lookup(id);
      if(!s.type.get_bool(ID_is_template))
      {
        it = id_set.erase(it);
        continue;
      }
      const cpp_declarationt &cpp_declaration = to_cpp_declaration(s.type);
      if(cpp_declaration.is_template_alias())
        have_aliases = true;
      else if(cpp_declaration.is_class_template())
        have_classes = true;
      else
        have_methods = true;
      ++it;
    }

    if(want == wantt::BOTH && have_classes && have_methods)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
      cpp_typecheck.error().source_location = source_location;
      cpp_typecheck.error() << "template symbol '" << base_name
                            << "' is ambiguous" << messaget::eom;
      throw 0;
    }

    if(have_aliases)
    {
      // template alias — instantiate and return the aliased type.
      // Substitution may fail (e.g., enable_if with false condition);
      // treat as SFINAE when fail_with_exception is false.
      try
      {
        typet result = resolve_template_alias(base_name, id_set, template_args);
        // N5008 [class.mem.general]/26 + [temp.inst]/2: when the alias
        // names a class template specialization, contexts that require a
        // complete type (a non-static data member declaration, sizeof,
        // base clauses) need the specialization instantiated.  The
        // class-template branch below elaborates; without doing the same
        // here a member declared through an alias leaves its class
        // incomplete, and e.g. cpp_is_pod later mis-judges the enclosing
        // class as POD (skipping the implicit default constructor, so the
        // object is never initialised).
        if(
          result.id() == ID_struct_tag &&
          !cpp_typecheck.skip_typechecking_elaborate)
        {
          struct_tag_typet instance = to_struct_tag_type(result);
          instance.add_source_location() = source_location;
          cpp_typecheck.elaborate_class_template(instance);
        }
        identifiers.push_back(exprt(ID_type, result));
      }
      catch(int)
      {
        if(fail_with_exception)
          throw;
        return nil_exprt();
      }
    }
    else if(want == wantt::TYPE || have_classes)
    {
      typet instance = disambiguate_template_classes(
        base_name, id_set, template_args, qualified);

      if(!cpp_typecheck.skip_typechecking_elaborate)
        cpp_typecheck.elaborate_class_template(instance);

      identifiers.push_back(exprt(ID_type, instance));
    }
    else
    {
      // Check for variable templates (concepts) with explicit args.
      // These need to be instantiated as variable templates, not
      // as function templates.
      bool handled_variable_template = false;
      if(template_args.is_not_nil())
      {
        for(const auto *id_ptr : id_set)
        {
          const symbolt &s = cpp_typecheck.lookup(id_ptr->identifier);
          if(!s.type.get_bool(ID_is_template))
            continue;
          const cpp_declarationt &decl = to_cpp_declaration(s.type);
          // Variable templates have declarators but are not class
          // templates and not function templates (no function type).
          // Skip partial specializations — they are matched later
          // by instantiate_template, not used for direct instantiation.
          if(decl.is_class_template() || decl.is_template_alias())
            continue;
          if(!s.type.get(ID_specialization_of).empty())
            continue;
          if(
            !decl.declarators().empty() &&
            decl.declarators()[0].type().id() != ID_function_type)
          {
            // This is a variable template (e.g., concept).
            // Instantiate with explicit template args.
            cpp_template_args_tct tc_args;
            try
            {
              tc_args = cpp_typecheck.typecheck_template_args(
                source_location, s, template_args);
            }
            catch(...)
            {
              continue;
            }
            // N5008 [temp.variadic]/7: a template parameter pack given no
            // arguments (an explicit empty list, `__and_v<>`) matches ZERO
            // elements.  typecheck_template_args leaves the pack's slot as
            // an `unassigned` placeholder, which instantiate_template
            // rejects; replace it with the empty_typet zero-length-pack
            // sentinel that template_mapt::build recognises (libstdc++'s
            // _Requires<> = enable_if_t<__and_v<>, bool> in std::optional's
            // constructor constraints).
            {
              const auto &vt_params =
                decl.template_type().template_parameters();
              auto &vt_args = tc_args.arguments();
              for(std::size_t k = 0; k < vt_params.size() && k < vt_args.size();
                  ++k)
              {
                if(
                  vt_params[k].get_bool(ID_ellipsis) &&
                  (vt_args[k].id() == ID_unassigned ||
                   vt_args[k].type().id() == ID_unassigned))
                {
                  vt_args[k] = exprt(ID_type, empty_typet());
                }
              }
            }
            const symbolt &inst_sym = cpp_typecheck.instantiate_template(
              source_location, s, tc_args, tc_args);
            // The instantiated symbol is a constexpr variable.
            // Return its value, evaluating any remaining constexpr
            // function calls.
            if(inst_sym.value.is_not_nil())
            {
              exprt val = inst_sym.value;
              if(!val.is_constant())
              {
                // Try constexpr evaluation of function calls
                std::function<void(exprt &)> eval_calls;
                eval_calls = [&](exprt &e)
                {
                  for(auto &op : e.operands())
                    eval_calls(op);
                  if(
                    e.id() == ID_side_effect &&
                    e.get(ID_statement) == ID_function_call)
                  {
                    exprt r = try_evaluate_constexpr(
                      e, cpp_typecheck.symbol_table, cpp_typecheck);
                    if(r.is_not_nil())
                      e = r;
                  }
                  // Handle dereference(function_call) for reference-
                  // returning functions like std::max(const T&, const T&)
                  if(
                    e.id() == ID_dereference && e.operands().size() == 1 &&
                    e.operands()[0].id() == ID_side_effect &&
                    e.operands()[0].get(ID_statement) == ID_function_call)
                  {
                    exprt r = try_evaluate_constexpr(
                      e.operands()[0],
                      cpp_typecheck.symbol_table,
                      cpp_typecheck);
                    if(r.is_not_nil())
                      e = r;
                  }
                  simplify(e, cpp_typecheck);
                  // Unwrap dereference(constant) from ref-returning constexpr
                  if(
                    e.id() == ID_dereference && e.operands().size() == 1 &&
                    e.operands()[0].is_constant())
                  {
                    e = e.operands()[0];
                  }
                };
                eval_calls(val);
              }
              // Store the evaluated constant back in the symbol table
              // so subsequent lookups get the constant directly.
              if(val.is_constant())
              {
                symbolt *writable =
                  cpp_typecheck.symbol_table.get_writeable(inst_sym.name);
                if(writable)
                  writable->value = val;
              }
              val.add_source_location() = source_location;
              identifiers.push_back(val);
              handled_variable_template = true;
            }
            else
            {
              // No value — return the symbol
              symbol_exprt sym_expr{inst_sym.name, inst_sym.type};
              sym_expr.add_source_location() = source_location;
              identifiers.push_back(sym_expr);
              handled_variable_template = true;
            }
            break;
          }
        }
      }
      if(!handled_variable_template)
      {
        // methods and functions
        convert_identifiers(id_set, fargs, identifiers);

        apply_template_args(identifiers, template_args, fargs);
      }
    }
  }
  else
  {
    convert_identifiers(id_set, fargs, identifiers);
  }

  // change types into constructors if we want a constructor
  if(want == wantt::VAR)
  {
    // Per [dcl.type.simple]/2: when a name with template arguments
    // resolves to a class type and no function arguments are
    // provided, it is a type-name, not a constructor call.
    bool has_class_type_no_args = false;
    if(template_args.is_not_nil() && !fargs.in_use)
    {
      for(const auto &id : identifiers)
      {
        if(id.id() == ID_type && id.type().id() == ID_struct_tag)
        {
          has_class_type_no_args = true;
          break;
        }
      }
    }
    if(!has_class_type_no_args)
    {
      // N5008 [basic.scope.hiding]/2: a class or enumeration name is hidden by
      // a variable, function, or enumerator of the same name declared in the
      // same scope, wherever that non-type name is visible.  When ordinary
      // lookup for a value (want == VAR) yields both a type and such a
      // *different* entity of the same name, the type name is hidden and must
      // not contribute a constructor candidate.  Without this, a C-style
      // declaration pair such as `struct S { ... }; S S(void);` -- e.g. POSIX
      // `struct stat`/`stat()` or glibc `struct mallinfo`/`mallinfo()`
      // (memory_info.cpp) -- makes the call `S()` ambiguous between the
      // function and the hidden type's constructor.
      //
      // The hiding entity must be a *different* declaration, not the type's own
      // members: a class's constructors resolve under the class's name too
      // (their base_name is the class name) but are part of the type, and an
      // uninstantiated constructor template appears as a non-code
      // cpp_declaration.  So only a genuine function -- an ID_code symbol whose
      // return type is not ID_constructor -- counts as hiding here; this keeps
      // ordinary construction (e.g. `allocator`, `basic_string`) unaffected.
      // (Type and hiding function necessarily share a scope: RECURSIVE scope
      // lookup stops at the first scope that declares the name.)
      auto is_hiding_function = [](const exprt &e)
      {
        return e.id() != ID_type && e.type().id() == ID_code &&
               to_code_type(e.type()).return_type().id() != ID_constructor;
      };
      const bool has_hiding_function =
        std::any_of(identifiers.begin(), identifiers.end(), is_hiding_function);
      if(has_hiding_function)
      {
        identifiers.erase(
          std::remove_if(
            identifiers.begin(),
            identifiers.end(),
            [](const exprt &e) { return e.id() == ID_type; }),
          identifiers.end());
      }

      // N5008 [temp.inst]/2: constructing an object of a class template
      // specialization is a context that requires a completely-defined type,
      // which implicitly instantiates the specialization.  An identifier here
      // may name a specialization that was registered but left INCOMPLETE
      // (e.g. std::pair<K,V> referenced internally by std::unordered_map from a
      // typedef type-checked while elaboration was suppressed).  Elaborate such
      // an instance before gathering its constructors -- otherwise
      // make_constructors would find only the implicit members of an incomplete
      // class ("found no match for symbol '...'").  This fires at the actual
      // construction site (want == VAR), not while elaboration is suppressed,
      // so it does not disturb the deferred elaboration of e.g.
      // std::basic_string.
      for(auto &id : identifiers)
      {
        if(
          id.id() == ID_type &&
          (id.type().id() == ID_struct_tag || id.type().id() == ID_union_tag))
        {
          const symbolt *instance_sym = cpp_typecheck.symbol_table.lookup(
            to_tag_type(id.type()).get_identifier());
          if(
            instance_sym != nullptr &&
            (instance_sym->type.id() == ID_struct ||
             instance_sym->type.id() == ID_union) &&
            instance_sym->type.get_bool(ID_template_class_instance) &&
            to_struct_union_type(instance_sym->type).is_incomplete())
          {
            cpp_typecheck.elaborate_class_template(id.type());
          }
        }
      }
      make_constructors(identifiers);
      remove_duplicates(identifiers);
    }
  }

  filter(identifiers, want);

#ifdef DEBUG
  std::cout << "P0 " << base_name << " " << identifiers.size() << '\n';
  show_identifiers(base_name, identifiers, std::cout);
  std::cout << '\n';
#endif

  exprt result;

  // We disambiguate functions
  resolve_identifierst new_identifiers = identifiers;

  remove_templates(new_identifiers);

#ifdef DEBUG
  std::cout << "P1 " << base_name << " " << new_identifiers.size() << '\n';
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << '\n';
#endif

  // we only want _exact_ matches, without templates!
  exact_match_functions(new_identifiers, fargs);

#ifdef DEBUG
  std::cout << "P2 " << base_name << " " << new_identifiers.size() << '\n';
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << '\n';
#endif

  // no exact matches? Try again with function template guessing.
  if(new_identifiers.empty())
  {
    new_identifiers = identifiers;

    // C++20 concept subsumption: before instantiation, filter out
    // function-template candidates that are strictly less constrained than a
    // sibling candidate (N5008 [temp.constr.order]/1 + [over.match.best]/2.6).
    // Subsumption is computed on the normal forms of the associated constraints
    // (template_constraint_strictly_subsumes), not by a textual comparison of
    // constraint names; e.g. `Cheap` is preferred over `Cheap || Rare` because
    // Cheap subsumes Cheap||Rare, even though the latter's name is longer.
    if(new_identifiers.size() > 1)
    {
      auto candidate_decl = [&](const exprt &id) -> const cpp_declarationt *
      {
        const irep_idt sym_id = id.get(ID_identifier);
        if(sym_id.empty())
          return nullptr;
        const auto *sym = cpp_typecheck.symbol_table.lookup(sym_id);
        if(
          sym == nullptr || !sym->type.get_bool(ID_is_template) ||
          sym->type.id() != ID_cpp_declaration)
          return nullptr;
        return &to_cpp_declaration(sym->type);
      };

      std::vector<const cpp_declarationt *> decls;
      std::vector<std::string> cstr;
      decls.reserve(new_identifiers.size());
      cstr.reserve(new_identifiers.size());
      for(const auto &id : new_identifiers)
      {
        const cpp_declarationt *d = candidate_decl(id);
        // Only consider constrained templates, so an unconstrained or
        // non-template candidate is never dropped here (it is ordered by the
        // normal best-match/partial-ordering rules instead).
        const bool constrained = d != nullptr && template_is_constrained(*d);
        decls.push_back(constrained ? d : nullptr);
        cstr.push_back(
          constrained ? constraint_name_string(*d) : std::string{});
      }

      std::vector<bool> subsumed(new_identifiers.size(), false);
      for(std::size_t i = 0; i < decls.size(); ++i)
      {
        if(decls[i] == nullptr || decls[i]->declarators().empty())
          continue;
        for(std::size_t j = 0; j < decls.size(); ++j)
        {
          if(i == j || decls[j] == nullptr || decls[j]->declarators().empty())
            continue;
          // Constraint subsumption only breaks ties between candidates that
          // are otherwise equivalent ([over.match.best]/2.6).  Restrict the
          // drop to candidates with the SAME function signature (same
          // parameter pattern and return type) -- precisely the same-signature
          // overloads that would otherwise collide -- so we never eliminate a
          // distinct-signature overload (e.g. a different std::span
          // constructor) on constraints alone, before argument matching.
          if(
            decls[i]->declarators().front().type() !=
              decls[j]->declarators().front().type() ||
            decls[i]->type() != decls[j]->type())
            continue;
          // Primary: normal-form subsumption ([temp.constr.order]/1) -- drop i
          // if j is strictly more constrained.
          if(template_constraint_strictly_subsumes(
               cpp_typecheck.symbol_table, *decls[j], *decls[i]))
          {
            subsumed[i] = true;
          }
          // Fallback: when normal-form subsumption is inconclusive (a
          // constraint we cannot fully decompose, e.g. some library ranges
          // concepts), use the historical name-substring heuristic -- but only
          // when the correct comparison has NOT shown i to be the strictly
          // more-constrained candidate, so the better overload is never
          // dropped (the bug this fixes, e.g. Cheap vs Cheap||Rare).
          else if(
            !template_constraint_strictly_subsumes(
              cpp_typecheck.symbol_table, *decls[i], *decls[j]) &&
            !cstr[i].empty() && !cstr[j].empty() && cstr[i] != cstr[j] &&
            cstr[j].find(cstr[i]) != std::string::npos)
          {
            subsumed[i] = true;
          }
        }
      }

      resolve_identifierst filtered;
      auto it = new_identifiers.begin();
      for(std::size_t i = 0; i < new_identifiers.size(); ++i, ++it)
        if(!subsumed[i])
          filtered.push_back(*it);
      if(!filtered.empty() && filtered.size() < new_identifiers.size())
        new_identifiers = filtered;
    }

    {
      guess_function_template_args(new_identifiers, fargs);

      // Remove uninstantiated template entries
      new_identifiers.erase(
        std::remove_if(
          new_identifiers.begin(),
          new_identifiers.end(),
          [](const exprt &e) { return e.type().get_bool(ID_is_template); }),
        new_identifiers.end());

      if(new_identifiers.empty())
      {
        new_identifiers = identifiers;
        // Template deduction failed for all templates, so remove them
        // to prevent raw template declarations from entering
        // disambiguate_functions.
        remove_templates(new_identifiers);
      }
    }

    disambiguate_functions(new_identifiers, fargs);
    // If template-instantiated candidates were all rejected by
    // disambiguate_functions, fall back to non-template overloads
    // which may match via implicit conversions.
    if(new_identifiers.empty())
    {
      new_identifiers = identifiers;
      remove_templates(new_identifiers);
      disambiguate_functions(new_identifiers, fargs);
    }

#ifdef DEBUG
    std::cout << "P3 " << base_name << " " << new_identifiers.size() << '\n';
    show_identifiers(base_name, new_identifiers, std::cout);
    std::cout << '\n';
#endif
  }
  else
  {
    remove_duplicates(new_identifiers);
    // Remove uninstantiated template entries
    new_identifiers.erase(
      std::remove_if(
        new_identifiers.begin(),
        new_identifiers.end(),
        [](const exprt &e) { return e.type().get_bool(ID_is_template); }),
      new_identifiers.end());
  }

#ifdef DEBUG
  std::cout << "P4 " << base_name << " " << new_identifiers.size() << '\n';
  show_identifiers(base_name, new_identifiers, std::cout);
  std::cout << '\n';
#endif

  if(new_identifiers.size() == 1)
  {
    result = *new_identifiers.begin();

    if(result.id() == ID_template_function_instance)
    {
      // template_function_instance should have been instantiated
      // by guess_function_template_args; if it wasn't, return nil
      // so the caller can try other resolution paths.
      if(!fail_with_exception)
        return nil_exprt();
    }
  }
  else
  {
    // nothing or too many
    if(!fail_with_exception)
      return nil_exprt();

    // When multiple candidates remain and no function arguments are
    // available for disambiguation (e.g., std::endl used as an
    // argument to operator<<), prefer the char-based instantiation
    // over wchar_t as a pragmatic default.
    bool resolved_by_filtering = false;
    if(new_identifiers.size() > 1 && !fargs.in_use)
    {
      resolve_identifierst filtered;
      for(const auto &id : new_identifiers)
      {
        const irep_idt &ident = id.get(ID_identifier);
        if(id2string(ident).find("wchar_t") == std::string::npos)
          filtered.push_back(id);
      }
      if(filtered.size() == 1)
      {
        result = filtered.front();
        resolved_by_filtering = true;
      }
    }

    if(!resolved_by_filtering)
    {
      if(new_identifiers.empty())
      {
        // Destructor overload resolution failure: return a dummy
        // destructor. Destructors are implicitly noexcept in C++11+.

        if(!base_name.empty() && id2string(base_name)[0] == '~')
        {
          // Last-chance direct lookup in the struct's components
          // list: `put_compound_into_scope` occasionally misses the
          // destructor for a template class (e.g. std::basic_string),
          // so the name-based lookup above returns nothing even
          // though the destructor IS present in the struct.  Before
          // falling back to the fully-dummy destructor below, scan
          // the current scope's struct components for a matching
          // destructor and return a member expression pointing at
          // it.  This lets callers (typecheck_expr_member on a
          // member access, or cpp_destructor on a synthesised dtor
          // call for a data member) build a valid function call.
          const irep_idt &cur_scope_id =
            cpp_typecheck.cpp_scopes.current_scope().identifier;
          const symbolt *scope_sym =
            cpp_typecheck.symbol_table.lookup(cur_scope_id);
          if(
            scope_sym != nullptr && scope_sym->is_type &&
            (scope_sym->type.id() == ID_struct ||
             scope_sym->type.id() == ID_union))
          {
            const auto &components =
              to_struct_union_type(scope_sym->type).components();
            for(const auto &c : components)
            {
              if(
                c.type().id() == ID_code &&
                to_code_type(c.type()).return_type().id() == ID_destructor &&
                c.get_base_name() == base_name)
              {
                // Build a member expression equivalent to what the
                // regular SYMBOL-class code at line ~786 produces
                // for non-static member lookups: ID_member with
                // component_name set to the destructor's full
                // identifier and the object as the single operand.
                //
                // Pull the object from fargs if the caller supplied
                // one (member access of the form obj.~T()); else
                // leave the operand list empty — the member-call
                // path in typecheck_side_effect_function_call fills
                // in the enclosing object when needed.
                //
                // Strip cv-qualifiers from the object's type: per
                // [class.dtor]/13 a destructor may be invoked on a
                // const-qualified object, and CBMC's subsequent
                // reference-binding check would otherwise reject
                // the implicit cast.
                exprt dtor_member(ID_member, c.type());
                dtor_member.set(ID_component_name, c.get_name());
                if(fargs.has_object && !fargs.operands.empty())
                {
                  exprt obj = fargs.operands.front();
                  typet obj_t = obj.type();
                  obj_t.remove(ID_C_constant);
                  obj_t.remove(ID_C_volatile);
                  obj.type() = obj_t;
                  // Patch the `this` parameter type on a local copy
                  // of the dtor code_type so it matches the
                  // (possibly-const) object without requiring an
                  // implicit const-to-non-const conversion.  The
                  // actual dtor symbol's type in the symbol table
                  // stays unchanged.
                  code_typet patched_type = to_code_type(c.type());
                  if(
                    !patched_type.parameters().empty() &&
                    patched_type.parameters().front().get_this() &&
                    patched_type.parameters().front().type().id() == ID_pointer)
                  {
                    typet this_base =
                      to_pointer_type(patched_type.parameters().front().type())
                        .base_type();
                    if(fargs.operands.front().type().get_bool(ID_C_constant))
                      this_base.set(ID_C_constant, true);
                    patched_type.parameters().front().type() =
                      pointer_type(this_base);
                  }
                  dtor_member.type() = patched_type;
                  dtor_member.copy_to_operands(std::move(obj));
                }
                dtor_member.add_source_location() = source_location;
                return dtor_member;
              }
            }
          }

          exprt dtor{ID_symbol};
          dtor.type() = code_typet{{}, empty_typet{}};
          dtor.type().set(ID_destructor, true);
          dtor.add_source_location() = source_location;
          return dtor;
        }
        // [temp.deduct]/8: template argument deduction failure is
        // not an error when the deduction occurs in an SFINAE
        // context.  CBMC's caller chain here (body elaboration of
        // an inline function in a user header calling a variadic
        // template with forwarding references) is indistinguishable
        // at this point from a legitimate SFINAE probe.  When every
        // remaining candidate is a function template (meaning no
        // non-template overload matched and deduction failed for
        // each template), silently throw instead of emitting a
        // user-visible diagnostic — the caller's body will be
        // discarded by the catch in convert_function, matching the
        // behaviour of true SFINAE contexts.
        bool all_templates = !identifiers.empty();
        for(const auto &id : identifiers)
        {
          if(!id.type().get_bool(ID_is_template))
          {
            all_templates = false;
            break;
          }
        }
        if(all_templates)
        {
          // Deduction failed for every candidate and there is no non-template
          // overload: a substitution failure ([temp.deduct]/8).  Keep the
          // silent `throw 0` (a recoverable caller can absorb it via
          // catch(int) and try alternatives, exactly as before -- do NOT
          // change this to a distinct exception, which would bypass those
          // recovery paths).  But when NOT inside a SFINAE context, record the
          // failure so that, if this throw propagates straight to a function
          // body's conversion (i.e. is not recovered), the body's handler can
          // diagnose the genuinely ill-formed "no viable function" call rather
          // than silently swallowing it as unsupported-STL leniency.  The
          // marker is cleared at the next resolve() entry, so a recovered
          // failure never leaks.
          if(cpp_typecheck.sfinae_context_depth == 0)
          {
            cpp_typecheck.pending_no_viable_call = true;
            cpp_typecheck.pending_no_viable_base_name = base_name;
            cpp_typecheck.pending_no_viable_location = source_location;
          }
          throw 0;
        }
        cpp_typecheck.error().source_location = source_location;
        cpp_typecheck.error() << "found no match for symbol '" << base_name
                              << "', candidates are:\n";
        show_identifiers(base_name, identifiers, cpp_typecheck.error());
      }
      else
      {
        cpp_typecheck.error().source_location = source_location;
        cpp_typecheck.error()
          << "symbol '" << base_name << "' does not uniquely resolve:\n";
        show_identifiers(base_name, new_identifiers, cpp_typecheck.error());

#ifdef DEBUG
        exprt e1 = *new_identifiers.begin();
        exprt e2 = *(++new_identifiers.begin());
        cpp_typecheck.error() << "e1==e2: " << (e1 == e2) << '\n';
        cpp_typecheck.error()
          << "e1.type==e2.type: " << (e1.type() == e2.type()) << '\n';
        cpp_typecheck.error()
          << "e1.id()==e2.id(): " << (e1.id() == e2.id()) << '\n';
        cpp_typecheck.error()
          << "e1.iden==e2.iden: "
          << (e1.get(ID_identifier) == e2.get(ID_identifier)) << '\n';
        cpp_typecheck.error() << "e1.iden:: " << e1.get(ID_identifier) << '\n';
        cpp_typecheck.error() << "e2.iden:: " << e2.get(ID_identifier) << '\n';
#endif
      }

      if(fargs.in_use)
      {
        cpp_typecheck.error() << "\nargument types:\n";

        for(const auto &op : fargs.operands)
        {
          cpp_typecheck.error()
            << "  " << cpp_typecheck.to_string(op.type()) << '\n';
        }
      }

      if(!cpp_typecheck.instantiation_stack.empty())
      {
        cpp_typecheck.show_instantiation_stack(cpp_typecheck.error());
      }

      cpp_typecheck.error() << messaget::eom;
      throw 0;
    }
  }

  // we do some checks before we return

  // The scope from which member accessibility is judged ([class.access]):
  // the genuine point of use.  For an explicit-object member access the
  // caller (typecheck_expr_member) records the enclosing class/function
  // in fargs.naming_scope, because resolve_scope() has since moved the
  // current scope into the object's class.  Otherwise the scope captured
  // at resolution time (original_scope) already is the point of use.
  cpp_scopet *access_scope =
    fargs.naming_scope != nullptr ? fargs.naming_scope : original_scope;

  // Access control check for class members resolved via qualified names.
  // The get_component path sets ID_C_not_accessible, but qualified name
  // resolution bypasses get_component, so we check here.
  // resolve_scope() changed the current scope to the target class, so we
  // must temporarily restore the access scope for check_component_access.
  if(
    !result.get_bool(ID_C_not_accessible) &&
    !cpp_typecheck.disable_access_control && access_scope != nullptr)
  {
    irep_idt result_id = result.get(ID_identifier);
    if(result_id.empty() && result.id() == ID_symbol)
      result_id = to_symbol_expr(result).get_identifier();

    if(!result_id.empty())
    {
      const std::string id_str = id2string(result_id);
      auto pos = id_str.rfind("::");
      if(pos != std::string::npos)
      {
        const std::string class_name = "tag-" + id_str.substr(0, pos);
        const symbolt *class_sym =
          cpp_typecheck.symbol_table.lookup(class_name);
        if(class_sym != nullptr && class_sym->type.id() == ID_struct)
        {
          const struct_typet &struct_type = to_struct_type(class_sym->type);
          for(const auto &comp : struct_type.components())
          {
            if(comp.get_name() == result_id)
            {
              // Temporarily restore the access scope for the access check.
              cpp_scopet *saved = cpp_typecheck.cpp_scopes.current_scope_ptr;
              cpp_typecheck.cpp_scopes.current_scope_ptr = access_scope;
              bool not_ok =
                cpp_typecheck.check_component_access(comp, struct_type);
              cpp_typecheck.cpp_scopes.current_scope_ptr = saved;

              if(not_ok)
              {
                // If access check fails, silently mark as inaccessible
                // rather than throwing. This allows overload resolution
                // to proceed with other candidates (e.g., MSVC's
                // bad_alloc has a private const char* ctor alongside
                // the public default ctor).
                if(!fail_with_exception)
                  return nil_exprt();

                // Mark as inaccessible but don't throw — the caller
                // may have other overloads to try.
                result.set(ID_C_not_accessible, true);
                break;
              }
              break;
            }
          }
        }
      }
    }
  }

  if(result.get_bool(ID_C_not_accessible))
  {
    // Re-check access from the access scope (the genuine point of use),
    // since resolve_scope() may have changed the current scope to the
    // target class, causing check_component_access to give a false
    // positive.
    bool still_not_accessible = true;
    if(access_scope != nullptr)
    {
      irep_idt comp_name = result.get(ID_component_name);
      if(comp_name.empty())
      {
        comp_name = result.get(ID_identifier);
        if(comp_name.empty() && result.id() == ID_symbol)
          comp_name = to_symbol_expr(result).get_identifier();
      }

      if(!comp_name.empty())
      {
        const std::string id_str = id2string(comp_name);
        auto pos = id_str.rfind("::");
        if(pos != std::string::npos)
        {
          const std::string class_name = "tag-" + id_str.substr(0, pos);
          const symbolt *class_sym =
            cpp_typecheck.symbol_table.lookup(class_name);
          if(class_sym != nullptr && class_sym->type.id() == ID_struct)
          {
            const struct_typet &struct_type = to_struct_type(class_sym->type);
            for(const auto &comp : struct_type.components())
            {
              if(comp.get_name() == comp_name)
              {
                cpp_scopet *saved = cpp_typecheck.cpp_scopes.current_scope_ptr;
                cpp_typecheck.cpp_scopes.current_scope_ptr = access_scope;
                still_not_accessible =
                  cpp_typecheck.check_component_access(comp, struct_type);
                cpp_typecheck.cpp_scopes.current_scope_ptr = saved;
                break;
              }
            }
          }
        }
      }
    }

    if(still_not_accessible)
    {
      // In system headers, silently ignore access violations —
      // they may result from incomplete modelling of friend
      // declarations or visibility attributes.
      const auto &loc = result.source_location();
      const std::string file = id2string(loc.get_file());
      if(
        !file.empty() && (file.find("/include/") != std::string::npos ||
                          file.find("\\include\\") != std::string::npos))
      {
        still_not_accessible = false;
      }
    }

    if(still_not_accessible)
    {
      if(!fail_with_exception)
        return nil_exprt();

      // For ordinary members ID_component_name carries the name; for a
      // constructor (and other synthesized references) it is empty, so
      // fall back to the resolved identifier for a meaningful message.
      irep_idt display_name = result.get(ID_component_name);
      if(display_name.empty())
        display_name = result.get(ID_identifier);
      if(display_name.empty() && result.id() == ID_symbol)
        display_name = to_symbol_expr(result).get_identifier();

      cpp_typecheck.error().source_location = result.source_location();
      cpp_typecheck.error()
        << "member '" << display_name << "' is not accessible" << messaget::eom;
      throw 0;
    }
  }

  switch(want)
  {
  case wantt::VAR:
    if(result.id() == ID_type && !cpp_typecheck.cpp_is_pod(result.type()))
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location = source_location;

      cpp_typecheck.error()
        << "expected expression, but got type '"
        << cpp_typecheck.to_string(result.type()) << "'" << messaget::eom;

      throw 0;
    }
    break;

  case wantt::TYPE:
    if(result.id() != ID_type)
    {
      if(!fail_with_exception)
        return nil_exprt();

      cpp_typecheck.error().source_location = source_location;

      cpp_typecheck.error()
        << "expected type, but got expression '"
        << cpp_typecheck.to_string(result) << "'" << messaget::eom;

      throw 0;
    }
    break;

  case wantt::BOTH:
    break;
  }

  return result;
}

void cpp_typecheck_resolvet::guess_template_args(
  const exprt &template_expr,
  const exprt &desired_expr)
{
  // An ambiguous node may contain a cpp_name that is a template parameter.
  // Extract the name for matching.
  const exprt &expr_to_match =
    template_expr.id() == ID_ambiguous
      ? static_cast<const exprt &>(
          static_cast<const irept &>(template_expr.type()))
      : template_expr;

  if(expr_to_match.id() == ID_cpp_name)
  {
    const cpp_namet &cpp_name = to_cpp_name(expr_to_match);

    if(!cpp_name.is_qualified())
    {
      cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

      cpp_template_args_non_tct template_args;
      irep_idt base_name;
      resolve_scope(cpp_name, base_name, template_args);

      const auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::RECURSIVE);

      // alright, rummage through these
      for(const auto &id_ptr : id_set)
      {
        const cpp_idt &id = *id_ptr;
        // template parameter?
        if(id.id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
        {
          // see if unassigned
          exprt &e = cpp_typecheck.template_map.expr_map[id.identifier];
          if(e.id() == ID_unassigned)
          {
            e = desired_expr;
          }
        }
      }
    }
  }
}

/// Deduce template arguments by comparing a type pattern P against an
/// actual type A.  This implements [temp.deduct.type] from the C++ standard.
///
/// The type P (template_type) is composed from template parameters and
/// concrete types.  The type A (desired_type) is a fully resolved type.
/// The function attempts to find template argument values that make P
/// match A, recording them in the template_map.
///
/// Decomposition rules implemented (per [temp.deduct.type]/3):
///  - [temp.deduct.type]/8  reference types (is_reference branch)
///  - [temp.deduct.type]/9  pointer types (ID_pointer branch)
///  - [temp.deduct.type]/10 array types (ID_array branch)
///  - [temp.deduct.type]/11 function types (ID_code/ID_function_type branch)
///  - [temp.deduct.type]/3.3 class template specializations (cpp_name with
///    template_args — matches instantiation arguments
///    from ID_C_template_arguments)
///  - [temp.deduct.type]/14 cv-qualified types (ID_merged_type branch)
void cpp_typecheck_resolvet::guess_template_args(
  const typet &template_type,
  const typet &desired_type)
{
  // Defensive backstop against unbounded recursion on a pathological type
  // graph.  The root cause of the known case (a member alias template whose
  // qualified expansion was re-treated as the unqualified alias) is fixed
  // below by only alias-expanding unqualified template-ids; this depth guard
  // remains as a cheap safety net for any other cyclic type graph reached
  // during deduction, so a front-end bug degrades to an incomplete deduction
  // rather than a stack-exhausting crash.
  static thread_local unsigned guess_template_args_depth = 0;
  if(guess_template_args_depth > 128)
    return;
  struct depth_guardt
  {
    unsigned &d;
    explicit depth_guardt(unsigned &d) : d(d)
    {
      ++d;
    }
    ~depth_guardt()
    {
      --d;
    }
  } depth_guard(guess_template_args_depth);

#ifdef DEBUG
  std::cout << "guess_template_args: TT.id=" << template_type.id()
            << " DT.id=" << desired_type.id() << '\n';
#endif

  // T
  // const T
  // volatile T
  // T&
  // T*
  // T[10]
  // A<T>
  // C(*)(T)
  // T(*)()
  // T(*)(U)
  // T C::*
  // C T::*
  // T U::*
  // T (C::*)()
  // C (T::*)()
  // D (C::*)(T)
  // C (T::*)(U)
  // T (C::*)(U)
  // T (U::*)()
  // T (U::*)(V)
  // E[10][i]
  // B<i>
  // TT<T>
  // TT<i>
  // TT<C>

#if 0
  std::cout << "TT: " << template_type.pretty() << '\n';
  std::cout << "DT: " << desired_type.pretty() << '\n';
#endif

  if(template_type.id() == ID_cpp_name)
  {
    // we only care about cpp_names that are template parameters!
    const cpp_namet &cpp_name = to_cpp_name(template_type);

    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    if(cpp_name.has_template_args())
    {
      // Check if this is a template alias — if so, expand it and
      // re-try deduction with the underlying type pattern.
      //
      // Only an *unqualified* template-id can name an alias that is in scope
      // for this expansion: the lookup below resolves the base name in the
      // current scope, ignoring any qualification.  A qualified template-id
      // (e.g. `ns::Matcher<...>`, typically the alias's own resolved target)
      // must NOT be treated as the unqualified alias -- doing so re-expands
      // the alias's target back into the alias and loops indefinitely
      // (N5008 [temp.alias]: alias expansion is a one-step substitution to the
      // fully-resolved underlying type, not a repeated re-lookup).  This is
      // the libstdc++ regex shape, where a member alias template
      // `_BracketMatcher<icase, collate>` expands to
      // `__detail::_BracketMatcher<_TraitsT, icase, collate>`; without the
      // guard, matching the expansion re-finds the member alias and recurses
      // until the stack is exhausted.
      // Look up the alias template.  An UNqualified name is found in the
      // current scope chain.  A QUALIFIED alias template-id (e.g.
      // std::index_sequence, the parameter type of std::apply's __apply_impl)
      // must be resolved through its qualifiers.  Proper qualified lookup --
      // unlike the old base-name-only recursive lookup, which is why qualified
      // names were previously skipped altogether -- resolves an alias's own
      // expansion target (a qualified class-template-id such as the libstdc++
      // regex `__detail::_BracketMatcher`) to the CLASS TEMPLATE, not back to
      // the member alias, so alias expansion terminates naturally without a
      // recursion guard (N5008 [temp.alias]: expansion is a one-step
      // substitution to the fully-resolved underlying type).
      {
        cpp_scopet::id_sett id_set;
        if(!cpp_name.is_qualified())
        {
          id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
            cpp_name.get_base_name(), cpp_scopet::RECURSIVE);
        }
        else
        {
          // A resolution failure in this (deduction / possibly SFINAE) context
          // is not an error -- just skip alias expansion.  resolve_scope moves
          // the current scope to the alias's declaring scope, so restore it
          // immediately (an inner cpp_save_scopet) before the substitution and
          // recursive deduction below, which must resolve the ENCLOSING
          // function template's pack parameter in its own scope.
          cpp_save_scopet inner_save_scope(cpp_typecheck.cpp_scopes);
          try
          {
            irep_idt qual_base_name;
            cpp_template_args_non_tct qual_template_args;
            cpp_scopet &alias_scope =
              resolve_scope(cpp_name, qual_base_name, qual_template_args);
            id_set = alias_scope.lookup(qual_base_name, cpp_scopet::QUALIFIED);
          }
          catch(...)
          {
          }
        }
        for(const auto &id_ptr : id_set)
        {
          if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE)
          {
            const symbolt *sym =
              cpp_typecheck.symbol_table.lookup(id_ptr->identifier);
            if(
              sym != nullptr && sym->type.get_bool(ID_is_template) &&
              to_cpp_declaration(sym->type).is_template_alias())
            {
              // Get the alias's underlying type pattern
              const cpp_declarationt &alias_decl =
                to_cpp_declaration(sym->type);
              const cpp_declaratort &alias_declarator =
                alias_decl.declarators().front();
              typet alias_type = alias_declarator.merge_type(alias_decl.type());
              cpp_convert_plain_type(
                alias_type, cpp_typecheck.get_message_handler());

              // The alias template parameters map to the template
              // arguments in the cpp_name. Substitute them.
              const auto &alias_params =
                alias_decl.template_type().template_parameters();
              const auto &name_args = cpp_name.get_sub().back();
              const irept::subt &targs = name_args.find(ID_arguments).get_sub();

              // Build a substitution from alias params to the
              // template arguments (which are themselves template
              // parameters of the enclosing function template).
              // For each alias param, find the corresponding targ
              // and substitute in alias_type.
              for(std::size_t i = 0;
                  i < alias_params.size() && i < targs.size();
                  ++i)
              {
                // The targ is a cpp_name referencing the function
                // template's parameter. We need to substitute the
                // alias param name in alias_type with this cpp_name.
                const irept &targ = targs[i];
                const irept &targ_type =
                  targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
                if(targ_type.id() != ID_cpp_name)
                  continue;

                // The alias parameter's base name.  A type parameter carries
                // it in ID_C_base_name; a NON-type parameter is stored as a
                // symbol whose name is only the suffix of its scoped identifier
                // (e.g. `template::20::I`) with an empty ID_C_base_name (the
                // shape of std::index_sequence's `size_t... _Idx`).  Derive it
                // robustly so a non-type parameter pack is substituted too;
                // without this the alias body keeps the alias's own parameter
                // name and the enclosing function's pack is never deduced.
                irep_idt alias_param_base = alias_params[i].get(ID_C_base_name);
                if(alias_param_base.empty())
                  alias_param_base = alias_params[i].get(ID_base_name);
                if(alias_param_base.empty())
                {
                  std::string id =
                    id2string(alias_params[i].get(ID_identifier));
                  if(id.empty())
                    id = id2string(alias_params[i].type().get(ID_identifier));
                  const auto pos = id.rfind("::");
                  alias_param_base = irep_idt{
                    pos != std::string::npos ? id.substr(pos + 2) : id};
                }
                if(alias_param_base.empty())
                  continue;

                // Find the alias param name in alias_type and replace
                std::function<void(irept &)> subst;
                subst = [&](irept &t)
                {
                  if(t.id() == ID_cpp_name)
                  {
                    const cpp_namet &n =
                      to_cpp_name(static_cast<const typet &>(t));
                    if(
                      !n.is_qualified() && !n.has_template_args() &&
                      n.get_base_name() == alias_param_base)
                    {
                      t = targ_type;
                      return;
                    }
                  }
                  for(auto &sub : t.get_sub())
                    subst(sub);
                  for(auto &ns : t.get_named_sub())
                    subst(ns.second);
                };
                subst(static_cast<irept &>(alias_type));
              }

              // Now deduce with the expanded alias type
              guess_template_args(alias_type, desired_type);
              return;
            }
          }
        }
      }

      // This could be something like my_template<T>, and we need
      // to match 'T'. Then 'desired_type' has to be a template instance.

      const auto &name_args = cpp_name.get_sub().back();
      if(name_args.id() != ID_template_args)
        return;

      const irept::subt &targs = name_args.find(ID_arguments).get_sub();

      // Helper: when deduction for C<T> fails (desired type is not an
      // instantiation of C), mark any template parameters in targs
      // as deduction-failed. This uses ID_nil as a poison value that
      // prevents later assignment from other parameters and causes
      // has_unassigned() to fail (since ID_nil != any valid type).
      auto mark_targs_conflicting = [&]()
      {
        for(const auto &targ : targs)
        {
          const irept &t =
            targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
          if(t.id() != ID_cpp_name)
            continue;
          const cpp_namet &tn = to_cpp_name(static_cast<const typet &>(t));
          if(tn.is_qualified() || tn.has_template_args())
            continue;
          irep_idt bname = tn.get_base_name();
          const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
            bname, cpp_scopet::RECURSIVE);
          for(const auto &id_ptr : ids)
          {
            if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
            {
              auto it =
                cpp_typecheck.template_map.type_map.find(id_ptr->identifier);
              if(it != cpp_typecheck.template_map.type_map.end())
              {
                // Mark as deduction-failed using ID_nil.
                // This prevents later assignment from other parameters
                // (the simple T case checks for ID_unassigned, and
                // ID_nil != ID_unassigned).
                it->second = typet(ID_nil);
              }
            }
          }
        }
      };

      // desired_type must be a struct/union tag that was instantiated
      // from a template
      irep_idt desired_id;
      if(desired_type.id() == ID_struct_tag)
        desired_id = to_struct_tag_type(desired_type).get_identifier();
      else if(desired_type.id() == ID_union_tag)
        desired_id = to_union_tag_type(desired_type).get_identifier();
      else
      {
        mark_targs_conflicting();
        return;
      }

      const symbolt *desired_sym =
        cpp_typecheck.symbol_table.lookup(desired_id);
      if(desired_sym == nullptr)
      {
        mark_targs_conflicting();
        return;
      }

      // Check if it was instantiated from a template
      if(desired_sym->type.find(ID_C_template).is_nil())
      {
        // N5008 [temp.deduct.call]/4: the argument type A need not itself be a
        // specialization of the class template named by P -- A may be a
        // (non-template) class DERIVED from such a specialization, in which
        // case deduction is performed against the base-class specialization.
        // The main derived-to-base dispatch below only runs once A has been
        // confirmed to be a template instantiation, so a plain
        // `struct D : Base<...>` would otherwise be rejected here.  Walk A's
        // bases for one that is an instantiation of the template named by P and
        // retry deduction against it (the recursion descends to deeper bases as
        // needed).
        if(desired_type.id() == ID_struct_tag)
        {
          const irep_idt dtb_tmpl_name = cpp_name.get_base_name();
          if(!dtb_tmpl_name.empty())
          {
            const irept &dtb_bases = desired_sym->type.find(ID_bases);
            for(const auto &base : dtb_bases.get_sub())
            {
              const typet &base_type =
                static_cast<const typet &>(base.find(ID_type));
              if(
                base_type.id() != ID_struct_tag &&
                base_type.id() != ID_union_tag)
                continue;
              const irep_idt base_id =
                base_type.id() == ID_struct_tag
                  ? to_struct_tag_type(base_type).get_identifier()
                  : to_union_tag_type(base_type).get_identifier();
              const symbolt *base_sym =
                cpp_typecheck.symbol_table.lookup(base_id);
              if(base_sym == nullptr || base_sym->base_name != dtb_tmpl_name)
                continue;
              const bool saved_dab = deducing_against_base;
              deducing_against_base = true;
              guess_template_args(template_type, base_type);
              deducing_against_base = saved_dab;
              return; // dispatched to the base subobject
            }
          }
        }
        mark_targs_conflicting();
        return;
      }

      // Verify that the template name in the cpp_name matches the
      // template the desired type was instantiated from. Without this
      // check, template argument deduction would incorrectly match
      // unrelated template instantiations (e.g., deducing I=char from
      // move_iterator<I> when the argument is basic_string<char>).
      {
        irep_idt tmpl_base_name = cpp_name.get_base_name();
        if(!tmpl_base_name.empty() && tmpl_base_name != desired_sym->base_name)
        {
          // Check if the template name is a template template parameter.
          // If so, assign it to the desired type's template.
          bool is_tt_param = false;
          const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
            tmpl_base_name, cpp_scopet::RECURSIVE);
          for(const auto &id_ptr : ids)
          {
            if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
            {
              auto it =
                cpp_typecheck.template_map.type_map.find(id_ptr->identifier);
              if(
                it != cpp_typecheck.template_map.type_map.end() &&
                it->second.id() == ID_unassigned)
              {
                // Assign the template template parameter to the
                // template that the desired type was instantiated from.
                it->second = desired_type;
                is_tt_param = true;
              }
            }
          }
          if(!is_tt_param)
          {
            // Per [temp.deduct.call]/4.3: if P is a class template-id
            // and A is a derived class, the template arguments may be
            // deduced from the base class of A that is an instantiation
            // of P.  Walk the base-class list of desired_sym and retry
            // deduction against the first base that is an instantiation
            // of a template whose base_name matches tmpl_base_name.
            // N5008 [temp.deduct.call]/4.3: A may be a class derived
            // DIRECTLY OR INDIRECTLY from the deduced class template --
            // e.g. basic_stringstream -> basic_iostream -> basic_ostream
            // for the <iomanip> inserters.  Breadth-first search the
            // whole base-class lattice for an instantiation of the
            // template, preferring the shallowest match ([class.member.
            // lookup]-style unambiguity is approximated by first hit).
            bool found_base = false;
            std::deque<typet> base_worklist;
            {
              const irept &bases = desired_sym->type.find(ID_bases);
              for(const auto &base : bases.get_sub())
                base_worklist.push_back(
                  static_cast<const typet &>(base.find(ID_type)));
            }
            std::set<irep_idt> bases_seen;
            while(!base_worklist.empty())
            {
              const typet base_type = base_worklist.front();
              base_worklist.pop_front();
              if(
                base_type.id() != ID_struct_tag &&
                base_type.id() != ID_union_tag)
                continue;
              const irep_idt base_id =
                base_type.id() == ID_struct_tag
                  ? to_struct_tag_type(base_type).get_identifier()
                  : to_union_tag_type(base_type).get_identifier();
              if(!bases_seen.insert(base_id).second)
                continue;
              const symbolt *base_sym =
                cpp_typecheck.symbol_table.lookup(base_id);
              if(base_sym == nullptr)
                continue;
              if(base_sym->base_name != tmpl_base_name)
              {
                // not this one: enqueue ITS bases (indirect derivation)
                const irept &sub_bases = base_sym->type.find(ID_bases);
                for(const auto &sub_base : sub_bases.get_sub())
                  base_worklist.push_back(
                    static_cast<const typet &>(sub_base.find(ID_type)));
                continue;
              }
              // Found a base class that is an instantiation of the
              // template we're deducing against.  Retry deduction
              // against this base.
              // [temp.deduct.call]/4.3: this is the derived-to-base case;
              // mark it so the pack-matching code records any pack it deduces
              // as requiring full-arity expansion in build_template_args.
              const bool saved_dab = deducing_against_base;
              deducing_against_base = true;
              guess_template_args(template_type, base_type);
              deducing_against_base = saved_dab;
              found_base = true;
              break;
            }
            if(!found_base)
            {
              mark_targs_conflicting();
              return;
            }
            // We dispatched to the base class — nothing else to do
            // here.
            return;
          }
        }
      }
      // N5008 [temp.deduct.type]: compare against the instance's template
      // arguments relative to the PRIMARY template (which is what the
      // pattern P names).  ID_C_template_arguments is
      // specialization-relative (empty for a `template<>` full
      // specialization -- deducing packs from it collapses them to zero
      // elements); prefer the primary-relative ID_full_template_args
      // recorded when the instance was created.
      const irept &full_inst_args =
        desired_sym->type.find(ID_full_template_args);
      const irept &inst_args =
        full_inst_args.is_not_nil()
          ? full_inst_args
          : desired_sym->type.find(ID_C_template_arguments);
      if(inst_args.is_nil())
      {
        mark_targs_conflicting();
        return;
      }

      const auto &inst_arguments =
        static_cast<const cpp_template_args_tct &>(inst_args).arguments();

      // N5008 [temp.deduct.call]/4.3 (same template family): P (template_type)
      // and A (desired_type) may name the same class template, yet a non-type
      // template parameter of P that is already fixed -- e.g. an explicitly
      // specified index, as in libstdc++'s
      // `__get_helper<__i>(_Tuple_impl<__i, _Head, _Tail...>&)` called on a
      // `_Tuple_impl<0, ...>` argument -- can differ from A's corresponding
      // argument.  A is then not itself a specialization of P, but may be
      // DERIVED from one (its base subobject).  Detect a fixed non-type
      // parameter whose bound value differs from A's argument and, if A has a
      // base that is a specialization of the same template, retry deduction
      // against that base (the recursion descends to deeper bases as needed).
      {
        bool fixed_mismatch = false;
        for(std::size_t i = 0; i < targs.size() && i < inst_arguments.size();
            ++i)
        {
          const irept &tn = targs[i];
          const irept &tt = tn.id() == ID_ambiguous ? tn.find(ID_type) : tn;
          if(tn.get_bool(ID_ellipsis) || tt.get_bool(ID_ellipsis))
            break; // a pack absorbs the remaining arguments
          if(inst_arguments[i].id() != ID_constant)
            continue; // only fixed non-type (constant) arguments here
          std::function<bool(const irept &)> refs_fixed_neq =
            [&](const irept &n) -> bool
          {
            if(n.id() == ID_name && !n.get(ID_identifier).empty())
            {
              const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
                n.get(ID_identifier), cpp_scopet::RECURSIVE);
              for(const auto *p : ids)
              {
                if(p->id_class != cpp_idt::id_classt::TEMPLATE_PARAMETER)
                  continue;
                const auto eit =
                  cpp_typecheck.template_map.expr_map.find(p->identifier);
                if(
                  eit != cpp_typecheck.template_map.expr_map.end() &&
                  eit->second.id() == ID_constant &&
                  eit->second.get(ID_value) != inst_arguments[i].get(ID_value))
                  return true;
              }
            }
            for(const auto &sub : n.get_sub())
              if(refs_fixed_neq(sub))
                return true;
            for(const auto &ns : n.get_named_sub())
              if(refs_fixed_neq(ns.second))
                return true;
            return false;
          };
          if(refs_fixed_neq(tn))
          {
            fixed_mismatch = true;
            break;
          }
        }
        if(fixed_mismatch)
        {
          const irep_idt tmpl_bn = cpp_name.get_base_name();
          const irept &fm_bases = desired_sym->type.find(ID_bases);
          for(const auto &base : fm_bases.get_sub())
          {
            const typet &base_type =
              static_cast<const typet &>(base.find(ID_type));
            if(
              base_type.id() != ID_struct_tag && base_type.id() != ID_union_tag)
              continue;
            const irep_idt base_id =
              base_type.id() == ID_struct_tag
                ? to_struct_tag_type(base_type).get_identifier()
                : to_union_tag_type(base_type).get_identifier();
            const symbolt *base_sym =
              cpp_typecheck.symbol_table.lookup(base_id);
            if(base_sym == nullptr || base_sym->base_name != tmpl_bn)
              continue;
            const bool saved_dab = deducing_against_base;
            deducing_against_base = true;
            guess_template_args(template_type, base_type);
            deducing_against_base = saved_dab;
            return; // dispatched to the base subobject
          }
          // No base is a specialization of the same template: A is genuinely
          // not (derived from) a specialization of P.
          mark_targs_conflicting();
          return;
        }
      }

      // Match each template arg from the cpp_name against the
      // corresponding instantiation arg
      for(std::size_t i = 0; i < targs.size(); i++)
      {
        // [temp.deduct.type] / [temp.variadic]: a pack-expansion argument
        // (e.g. the `Types...` in `mytuple<Types...>`) matches the remaining
        // template arguments of the instantiation, deducing the parameter
        // pack.  Detect it and bind the whole pack, then stop (it consumes the
        // rest).  Without this a partial specialization such as
        // `tuple_size<tuple<Types...>>` never matches a concrete instantiation.
        const irept &targ_node = targs[i];
        const irept &targ_t =
          targ_node.id() == ID_ambiguous ? targ_node.find(ID_type) : targ_node;
        const bool is_pack =
          targ_node.get_bool(ID_ellipsis) || targ_t.get_bool(ID_ellipsis);

        if(is_pack)
        {
          // Resolve the pack parameter's identifier (the bare cpp_name being
          // expanded, e.g. `Types`).
          irep_idt pack_id;
          if(targ_t.id() == ID_cpp_name)
          {
            const cpp_namet &pn =
              to_cpp_name(static_cast<const typet &>(targ_t));
            if(!pn.is_qualified() && !pn.has_template_args())
            {
              const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
                pn.get_base_name(), cpp_scopet::RECURSIVE);
              for(const auto &id_ptr : ids)
                if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
                  pack_id = id_ptr->identifier;
            }
          }

          if(!pack_id.empty())
          {
            // [temp.variadic]/7: skip the empty_typet zero-length-pack
            // sentinel (used in a class instance's recorded template
            // arguments to mark a trailing pack that matched no elements,
            // e.g. the empty `_Tail` of `_Tuple_impl<1, int>`).  Counting it
            // as a real element would deduce a one-element pack `<void>`.
            std::vector<typet> pack_elems;
            // [temp.deduct.type] + [temp.variadic]: a NON-type template
            // argument (e.g. the `1, 2` of `seq<1,2>`) deduces the pack's
            // element VALUES, recorded in pack_expr_map -- the value analogue
            // of pack_args_map -- so a later pack expansion over it (e.g.
            // `add(I...)`) has the concrete values to substitute.
            std::vector<exprt> pack_exprs;
            for(std::size_t j = i; j < inst_arguments.size(); j++)
            {
              if(inst_arguments[j].id() == ID_type)
              {
                if(inst_arguments[j].type().id() != ID_empty)
                  pack_elems.push_back(inst_arguments[j].type());
              }
              else if(inst_arguments[j].id() != ID_unassigned)
                pack_exprs.push_back(
                  static_cast<const exprt &>(inst_arguments[j]));
            }

            cpp_typecheck.template_map.pack_size_map[pack_id] =
              pack_elems.size() + pack_exprs.size();
            // [temp.deduct.call]/4.3: if this pack was deduced from a
            // base-class subobject of a derived-class argument, record it so
            // build_template_args' single placeholder is later expanded to
            // the full deduced arity.
            if(deducing_against_base)
              derived_to_base_deduced_packs.insert(pack_id);
            // Record the pack arguments.  For a genuine TYPE pack (or an empty
            // pack) record pack_args_map -- an explicit empty entry lets a
            // zero-length pack expansion in the matched pattern expand to no
            // arguments.  For a NON-type (value) pack do NOT record an empty
            // pack_args_map entry: the pack-name matcher checks pack_args_map
            // before pack_expr_map, so an empty type entry would shadow the
            // deduced values and expand `add(I...)` to zero arguments.
            if(pack_exprs.empty())
              cpp_typecheck.template_map.pack_args_map[pack_id] = pack_elems;
            if(!pack_exprs.empty())
            {
              cpp_typecheck.template_map.pack_expr_map[pack_id] = pack_exprs;
              // Keep the pack resolvable as a single value outside a pack
              // expansion (mirror of the type_map convenience below).
              cpp_typecheck.template_map.expr_map[pack_id] = pack_exprs.front();
            }
            else if(!pack_elems.empty())
            {
              // Keep the pack parameter resolvable as a single type (the
              // first element) outside a pack expansion; build_template_args
              // emits the full pack.
              cpp_typecheck.template_map.type_map[pack_id] = pack_elems.front();
            }
            // A zero-length pack leaves the parameter ID_unassigned; the
            // caller encodes it as a zero-length expansion.
          }
          break;
        }

        if(i >= inst_arguments.size())
          break;

        if(inst_arguments[i].id() == ID_type)
        {
          // The targ might be an "ambiguous" node with a type sub
          const typet &targ_type =
            targs[i].id() == ID_ambiguous
              ? static_cast<const typet &>(targs[i].find(ID_type))
              : static_cast<const typet &>(
                  static_cast<const irept &>(targs[i]));
          guess_template_args(targ_type, inst_arguments[i].type());
        }
        else
        {
          guess_template_args(
            static_cast<const exprt &>(targs[i]), inst_arguments[i]);
        }
      }
    }
    else
    {
      // template parameters aren't qualified
      if(!cpp_name.is_qualified())
      {
        irep_idt base_name;
        cpp_template_args_non_tct template_args;
        resolve_scope(cpp_name, base_name, template_args);

        const auto id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
          base_name, cpp_scopet::RECURSIVE);

        // alright, rummage through these
        for(const auto &id_ptr : id_set)
        {
          const cpp_idt &id = *id_ptr;

          // template argument?
          if(id.id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
          {
            // N5008 [temp.deduct]/5: deduction binds only the parameters
            // of the template being deduced.  The RECURSIVE scope lookup
            // above also surfaces same-short-name parameters of unrelated
            // enclosing templates (the caller's `P2` while deducing a
            // member constructor template's own `P2` -- the
            // std::chrono::duration converting-constructor shape); binding
            // or conflict-checking those poisons the enclosing map and
            // spuriously rejects the candidate.  Skip identifiers that are
            // not parameters of the current deduction.
            if(
              !current_deduction_parameters.empty() &&
              current_deduction_parameters.count(id.identifier) == 0)
            {
              continue;
            }
            // see if unassigned
            typet &t = cpp_typecheck.template_map.type_map[id.identifier];
            if(t.id() == ID_unassigned)
            {
              t = desired_type;
            }
            else
            {
              // Already assigned — check for conflict.
              // Strip cv-qualifiers for comparison.
              typet existing = t;
              typet incoming = desired_type;
              existing.remove(ID_C_constant);
              existing.remove(ID_C_volatile);
              incoming.remove(ID_C_constant);
              incoming.remove(ID_C_volatile);
              if(existing != incoming)
                t.id(ID_unassigned); // mark as conflicting
            }
          }
        }
      }
    }
  }
  else if(template_type.id() == ID_merged_type)
  {
    // Strip cv-qualifiers from the desired type when the merged_type
    // contains them, so that e.g. const T matched against const char
    // deduces T=char rather than T=const char.
    typet desired = desired_type;
    for(const auto &t : to_merged_type(template_type).subtypes())
    {
      if(t.id() == ID_const)
        desired.remove(ID_C_constant);
      else if(t.id() == ID_volatile)
        desired.remove(ID_C_volatile);
      else
        guess_template_args(t, desired);
    }
  }
  // [temp.deduct.type]/14: cv-qualified types — strip cv and recurse
  else if(is_reference(template_type) || is_rvalue_reference(template_type))
  {
    // [temp.deduct.type]/8: if P is a reference type, the referred-to
    // type is used for type deduction.
    typet desired = desired_type;
    if(is_reference(desired) || is_rvalue_reference(desired))
    {
      // The reference qualifier of P is part of the pattern: an
      // lvalue-reference pattern (`T&`) is matched only by an
      // lvalue-reference argument and an rvalue-reference pattern (`T&&`)
      // only by an rvalue-reference argument.  In CBMC an rvalue
      // reference is a pointer carrying *both* C_reference and
      // C_rvalue_reference, so the kinds are distinguished by the rvalue
      // flag.  This matters for class-template partial-specialization
      // matching ([temp.spec.partial.match], [temp.deduct.type]) of
      // libstdc++'s reference-qualifier-keyed
      // `__common_ref_impl<_Xp&, _Yp&&>` family.
      if(is_rvalue_reference(template_type) != is_rvalue_reference(desired))
        return; // reference kinds differ -> deduction failure
      desired = to_reference_type(desired).base_type();
    }
    guess_template_args(to_reference_type(template_type).base_type(), desired);
  }
  else if(template_type.id() == ID_pointer)
  {
    if(desired_type.id() == ID_pointer)
      guess_template_args(
        to_pointer_type(template_type).base_type(),
        to_pointer_type(desired_type).base_type());
  }
  else if(template_type.id() == ID_frontend_pointer)
  {
    if(desired_type.id() == ID_pointer)
    {
      // Reference-qualifier match, as in the reference branch above.
      // Before type-checking, a reference pattern (`_Xp&` / `_Yp&&`) is a
      // `frontend_pointer` flagged C_reference (and additionally
      // C_rvalue_reference for `&&`); the argument is an already-checked
      // pointer with the same flag convention.  An lvalue-reference
      // pattern must not match an rvalue-reference argument or vice
      // versa: conflating them lets the wrong libstdc++ `__common_ref_impl`
      // partial specialization match, and for
      // `__common_ref_impl<_Xp&, _Yp&&> : __common_ref_impl<_Yp&&, _Xp&>`
      // the substituted base then equals the specialization itself --
      // a self-inheriting class ([class.derived.general]/2), which aborts
      // class-body elaboration and, via the C++20 iterator-concept chain,
      // truncates `basic_string`.  [temp.spec.partial.match],
      // [temp.deduct.type].
      const bool pattern_is_ref = template_type.get_bool(ID_C_reference) ||
                                  template_type.get_bool(ID_C_rvalue_reference);
      const bool desired_is_ref = desired_type.get_bool(ID_C_reference) ||
                                  desired_type.get_bool(ID_C_rvalue_reference);
      if(
        pattern_is_ref && desired_is_ref &&
        template_type.get_bool(ID_C_rvalue_reference) !=
          desired_type.get_bool(ID_C_rvalue_reference))
        return; // reference kinds differ -> deduction failure
      guess_template_args(
        to_type_with_subtype(template_type).subtype(),
        to_pointer_type(desired_type).base_type());
    }
  }
  else if(template_type.id() == ID_array)
  {
    if(desired_type.id() == ID_array)
    {
      // look at subtype first
      guess_template_args(
        to_array_type(template_type).element_type(),
        to_array_type(desired_type).element_type());

      // size (e.g., buffer size guessing)
      guess_template_args(
        to_array_type(template_type).size(),
        to_array_type(desired_type).size());
    }
  }
  else if(template_type.id() == ID_function_type)
  {
    // function_type is the pre-conversion form of code type.
    // Match return type and parameter types.
    if(desired_type.id() == ID_code)
    {
      const code_typet &desired_code = to_code_type(desired_type);

      // Match return type (stored as subtype in function_type)
      if(template_type.has_subtype())
      {
        guess_template_args(
          to_type_with_subtype(template_type).subtype(),
          desired_code.return_type());
      }

      // Match parameter types
      const irept::subt &tmpl_params =
        template_type.find(ID_parameters).get_sub();
      const code_typet::parameterst &desired_params = desired_code.parameters();

      auto d_it = desired_params.begin();
      for(const auto &tp : tmpl_params)
      {
        if(tp.id() == ID_ellipsis)
          break;
        if(d_it == desired_params.end())
          break;

        if(tp.id() == ID_cpp_declaration)
        {
          const cpp_declarationt &decl = to_cpp_declaration(tp);
          if(!decl.declarators().empty())
          {
            try
            {
              typet param_type =
                decl.declarators().front().merge_type(decl.type());
              cpp_convert_plain_type(
                param_type, cpp_typecheck.get_message_handler());
              guess_template_args(param_type, d_it->type());
            }
            catch(...)
            {
              // ignore conversion errors
            }
          }
        }

        ++d_it;
      }
    }
  }
  else if(template_type.id() == ID_code)
  {
    // Both template and desired are code types; their parameters may
    // still be in pre-conversion (cpp_declaration) form, in which case
    // the parameter's reference/pointer/array part is carried by the
    // declarator rather than by its `type()`.  Recover the full
    // parameter type so e.g. a reference parameter is deduced as a
    // reference ([temp.deduct.type] applied to function-type
    // parameters), not as its bare referent.
    if(desired_type.id() == ID_code)
    {
      const code_typet &tmpl_code = to_code_type(template_type);
      const code_typet &desired_code = to_code_type(desired_type);

      guess_template_args(tmpl_code.return_type(), desired_code.return_type());

      const auto &tmpl_params = tmpl_code.parameters();
      const auto &desired_params = desired_code.parameters();
      std::size_t d_index = 0;
      for(const auto &tp : tmpl_params)
      {
        // [temp.deduct.type]/9-10: a function parameter pack `P...`
        // is deduced by comparing the pattern P against each of the
        // remaining argument types.  The deduced element types are
        // collected so the pack can later be expanded.
        bool is_pack = false;
        if(tp.id() == ID_cpp_declaration)
        {
          const cpp_declarationt &decl = to_cpp_declaration(tp);
          is_pack = !decl.declarators().empty() &&
                    decl.declarators().front().get_has_ellipsis();
        }

        if(is_pack)
        {
          deduce_function_parameter_pack(
            to_cpp_declaration(tp), desired_type, d_index);
          // A function parameter pack is necessarily the last
          // parameter ([temp.param]/11).
          break;
        }

        if(d_index >= desired_params.size())
          break;
        guess_template_args(
          tp.type(), full_function_parameter_type(desired_params[d_index]));
        ++d_index;
      }
    }
  }
}

/// Recover a function parameter's full (merged) type.
///
/// When a parameter is still in pre-conversion (cpp_declaration) form, the
/// reference/pointer/array part is carried by the declarator rather than by
/// its `type()`; merge them, keeping the result in frontend form so it
/// compares equal to the (also unconverted) desired argument during
/// specialization matching.
static typet full_function_parameter_type(const exprt &param)
{
  if(param.id() == ID_cpp_declaration)
  {
    const cpp_declarationt &decl = to_cpp_declaration(param);
    if(!decl.declarators().empty())
      return decl.declarators().front().merge_type(decl.type());
  }
  return param.type();
}

void cpp_typecheck_resolvet::deduce_function_parameter_pack(
  const cpp_declarationt &pack_decl,
  const typet &desired_code_type,
  std::size_t start_index)
{
  const code_typet::parameterst &desired_params =
    to_code_type(desired_code_type).parameters();

  // The element pattern is the declarator without its ellipsis flag
  // merged with the declaration's base type.
  cpp_declaratort elem_declarator = pack_decl.declarators().front();
  elem_declarator.remove(ID_ellipsis);
  const typet elem_pattern = elem_declarator.merge_type(pack_decl.type());

  // Resolve the pack parameter's identifier from the declaration's
  // base type (a bare cpp_name naming a template parameter pack).
  irep_idt pack_id;
  if(pack_decl.type().id() == ID_cpp_name)
  {
    const cpp_namet &pn = to_cpp_name(pack_decl.type());
    if(!pn.is_qualified() && !pn.has_template_args())
    {
      const auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
        pn.get_base_name(), cpp_scopet::RECURSIVE);
      for(const auto &id_ptr : ids)
        if(id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
          pack_id = id_ptr->identifier;
    }
  }

  std::vector<typet> pack_elems;
  for(std::size_t i = start_index; i < desired_params.size(); ++i)
  {
    const typet desired_elem = full_function_parameter_type(desired_params[i]);
    if(pack_id.empty())
    {
      // Could not identify the pack parameter; fall back to using the
      // argument type directly (correct for a bare `A...` pattern).
      pack_elems.push_back(desired_elem);
      continue;
    }

    // Deduce one element by matching the element pattern against this
    // argument, reading back the value bound to the pack parameter.
    typet unassigned(ID_unassigned);
    unassigned.set(ID_identifier, pack_id);
    cpp_typecheck.template_map.type_map[pack_id] = unassigned;
    guess_template_args(elem_pattern, desired_elem);
    auto it = cpp_typecheck.template_map.type_map.find(pack_id);
    if(
      it != cpp_typecheck.template_map.type_map.end() &&
      it->second.id() != ID_unassigned && it->second.id() != ID_nil)
      pack_elems.push_back(it->second);
    else
      pack_elems.push_back(desired_elem);
  }

  if(pack_id.empty())
    return;

  cpp_typecheck.template_map.pack_size_map[pack_id] = pack_elems.size();
  if(!pack_elems.empty())
  {
    cpp_typecheck.template_map.pack_args_map[pack_id] = pack_elems;
    // Per [temp.variadic]/7: keep the pack parameter resolvable as a
    // single type (the first element) so substitutions outside a pack
    // expansion still work; build_template_args() emits the full pack.
    cpp_typecheck.template_map.type_map[pack_id] = pack_elems.front();
  }
  // For a zero-length pack the parameter is left ID_unassigned so the
  // caller's empty-pack handling encodes it as a zero-length expansion.
}

/// True if \p n contains a function-call argument marked as a pack expansion
/// (ID_ellipsis), so the default-argument operand must be expanded (by the
/// template map's apply()) before it is type-checked ([temp.variadic]/5).
static bool contains_call_argument_pack(const irept &n)
{
  if(n.id() == ID_side_effect && n.get(ID_statement) == ID_function_call)
  {
    for(const auto &child : n.get_sub())
      if(child.id() == ID_arguments)
        for(const auto &a : child.get_sub())
          if(a.get_bool(ID_ellipsis))
            return true;
  }
  for(const auto &s : n.get_sub())
    if(contains_call_argument_pack(s))
      return true;
  for(const auto &ns : n.get_named_sub())
    if(contains_call_argument_pack(ns.second))
      return true;
  return false;
}

/// Deduce template arguments for a function template from a function call.
///
/// Implements [temp.deduct.call]: for each function template parameter type P
/// that contains template parameters, compare P with the type of the
/// corresponding call argument A.  Also implements [temp.deduct.funcaddr]
/// when called with synthetic fargs from known class template instantiations.
///
/// Key rules implemented:
///  - [temp.deduct.call]/1: P/A comparison for each parameter
///  - [temp.deduct.call]/3: forwarding references (T&& with lvalue → T&)
///  - [temp.deduct.call]/4: cv-stripping when P is just T (not T&, T*, etc.)
///  - [temp.deduct.call]/4: array-to-pointer decay
///  - [temp.deduct.funcaddr]: deduction from function address target type

exprt cpp_typecheck_resolvet::guess_function_template_args(
  const exprt &expr,
  const cpp_typecheck_fargst &fargs)
{
  // Each resolution starts with no derived-to-base-deduced packs recorded;
  // the set is populated by guess_template_args during this call and consumed
  // by the type-internal-pack expansion below.
  derived_to_base_deduced_packs.clear();

  const typet &tmp =
    expr.type().id() == ID_struct_tag
      ? static_cast<const typet &>(
          cpp_typecheck.follow_tag(to_struct_tag_type(expr.type())))
    : expr.type().id() == ID_union_tag
      ? static_cast<const typet &>(
          cpp_typecheck.follow_tag(to_union_tag_type(expr.type())))
    : expr.type().id() == ID_c_enum_tag
      ? static_cast<const typet &>(
          cpp_typecheck.follow_tag(to_c_enum_tag_type(expr.type())))
      : expr.type();

  if(!tmp.get_bool(ID_is_template))
    return nil_exprt(); // not a template

  PRECONDITION(expr.id() == ID_symbol);

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration = to_cpp_declaration(tmp);

  // Class templates require explicit template arguments,
  // no guessing!
  if(cpp_declaration.is_class_template())
    return nil_exprt();

  // we need function arguments for guessing
  if(fargs.operands.empty() && expr.find(ID_C_template_arguments).is_nil())
  {
    // C++11: check if all template parameters have default values
    // or are variadic packs (per [temp.variadic]/7: a pack can match
    // zero arguments).
    const auto &params = cpp_declaration.template_type().template_parameters();
    bool all_have_defaults = !params.empty();
    for(const auto &p : params)
    {
      if(p.find(ID_C_default_value).is_nil() && !p.get_bool(ID_ellipsis))
      {
        all_have_defaults = false;
        break;
      }
    }
    if(!all_have_defaults)
    {
      // [temp.deduct.funcaddr]: try to deduce template arguments
      // from the function's parameter types by matching against
      // known class template instantiations in the symbol table.
      // Build synthetic fargs from the instantiation types and
      // let the existing deduction code handle the matching.
      bool deduced_from_context = false;
      if(
        cpp_declaration.declarators().size() == 1 &&
        cpp_declaration.declarators()[0].type().id() == ID_function_type)
      {
        const auto &fn_params =
          cpp_declaration.declarators()[0].type().find(ID_parameters);
        for(const auto &param : fn_params.get_sub())
        {
          if(param.id() != ID_cpp_declaration)
            continue;
          const auto &pdecl =
            to_cpp_declaration(static_cast<const exprt &>(param));
          if(pdecl.declarators().empty())
            continue;
          typet ptype = pdecl.declarators()[0].merge_type(pdecl.type());
          // Strip reference
          bool is_ref = false;
          if(ptype.id() == ID_frontend_pointer || ptype.id() == ID_pointer)
          {
            if(!ptype.get_sub().empty())
              ptype = static_cast<const typet &>(ptype.get_sub()[0]);
            is_ref = true;
          }
          if(ptype.id() != ID_cpp_name)
            continue;
          irep_idt base = to_cpp_name(ptype).get_base_name();
          if(base.empty())
            continue;
          // Search for a complete instantiation
          std::string search = "tag-" + id2string(base) + "<";
          for(const auto &entry : cpp_typecheck.symbol_table.symbols)
          {
            const std::string &eid = id2string(entry.first);
            if(eid.find(search) == std::string::npos)
              continue;
            // Skip virtual tables and other non-type symbols
            if(eid.find("virtual_table") != std::string::npos)
              continue;
            if(
              entry.second.type.id() != ID_struct ||
              to_struct_type(entry.second.type).is_incomplete())
              continue;
            // Build a synthetic fargs with this instantiation type
            // and re-call guess_function_template_args
            typet arg_type{struct_tag_typet{entry.first}};
            if(is_ref)
              arg_type = reference_type(arg_type);
            symbol_exprt synthetic{"funcaddr_synthetic", arg_type};
            cpp_typecheck_fargst synthetic_fargs;
            synthetic_fargs.operands.push_back(synthetic);
            exprt result;
            try
            {
              result = guess_function_template_args(expr, synthetic_fargs);
            }
            catch(...)
            {
              continue;
            }
            if(result.is_not_nil())
            {
              deduced_from_context = true;
              return result;
            }
          }
          break; // only try the first parameter
        }
      }
      if(!deduced_from_context)
        return nil_exprt(); // give up
    }
  }

  // We need to guess in the case of function templates!

  irep_idt template_identifier = to_symbol_expr(expr).identifier();

  const symbolt &template_symbol = cpp_typecheck.lookup(template_identifier);

  // alright, set up template arguments as 'unassigned'

  cpp_saved_template_mapt saved_map(cpp_typecheck.template_map);

  cpp_typecheck.template_map.build_unassigned(cpp_declaration.template_type());

  // N5008 [temp.deduct]/5: restrict unqualified-name deduction to THIS
  // template's parameters (see current_deduction_parameters).
  deduction_parameters_guardt deduction_parameters_guard{
    current_deduction_parameters};
  current_deduction_parameters =
    template_parameter_ids(cpp_declaration.template_type());
  deduction_parameters_guardt map_deduction_parameters_guard{
    cpp_typecheck.template_map.deduction_parameters};
  cpp_typecheck.template_map.deduction_parameters =
    current_deduction_parameters;

  // If this is a template constructor inside an instantiated template class,
  // pre-populate the template map with the class template arguments so that
  // class template parameters (e.g., Alloc) are resolved.
  // The enclosing class tag for a member template, used both to bind the
  // class template arguments during deduction (below) and to propagate
  // ID_C_class onto the deduced function type so that instantiate_template
  // can rebuild the class template map when the member is instantiated.
  irep_idt member_class_tag;
  {
    irep_idt class_tag = expr.get(ID_C_class);

    // If ID_C_class is not set, try to derive it from the template
    // identifier.  A member template (constructor or member function
    // template) of a class template has an identifier of the form
    // "ClassName<...>::template.MemberName<...>(...)->(...)".  The
    // enclosing class's template arguments must be bound into the template
    // map even for a non-constructor member template, because the member's
    // signature may depend on the class's parameters -- e.g.
    // `reference_wrapper<T>::operator()` whose dependent return type is
    // `invoke_result_t<T&, _Args...>` (binding only the member's own
    // parameter pack `_Args` leaves the class parameter `T` unresolved, so
    // the dependent return type fails to elaborate and the deduction is
    // rejected).  The member's own parameters are independent and are set up
    // separately by build_unassigned above, so binding the (differently
    // named) class parameters does not disturb them.
    if(class_tag.empty())
    {
      const std::string &tid = id2string(template_identifier);
      auto pos = tid.find("::template.");
      if(pos != std::string::npos)
      {
        // The enclosing class's qualified name is the prefix before
        // "::template.".  The symbol-table name of a tag type is
        // "<namespace-qualification>tag-<unqualified-name>", i.e.,
        // the "tag-" prefix is inserted immediately before the
        // unqualified class name, AFTER any namespace qualification
        // (e.g., `std::tag-optional<int>`, not
        // `tag-std::optional<int>`).  Inserting "tag-" at the very
        // front only happens to be correct for a class in the global
        // namespace; for any namespaced class template (such as
        // every type in `std`), it produces a name that does not
        // exist in the symbol table, so the class template
        // arguments are never bound into the template map.  The
        // converting constructor's SFINAE constraints that reference
        // the class template parameter `_Tp` (e.g.,
        // `is_constructible<_Tp, _Up>` in `std::optional`'s
        // `optional(_Up&&)`) then fail to resolve, the deduction is
        // rejected, and copy-initialization such as `return v;` into
        // a `std::optional<T>` reports the spurious
        //   invalid implicit conversion from 'T' to 'struct optional'.
        //
        // Insert "tag-" before the last "::"-separated component that
        // sits at template-bracket depth 0 (so the "::" inside
        // template arguments like `optional<a::b>` is ignored).
        const std::string class_name = tid.substr(0, pos);
        std::size_t insert_pos = 0;
        int depth = 0;
        for(std::size_t i = 0; i + 1 < class_name.size(); ++i)
        {
          const char c = class_name[i];
          if(c == '<')
            ++depth;
          else if(c == '>')
            --depth;
          else if(depth == 0 && c == ':' && class_name[i + 1] == ':')
            insert_pos = i + 2;
        }
        class_tag = class_name.substr(0, insert_pos) + "tag-" +
                    class_name.substr(insert_pos);
      }
    }

    if(!class_tag.empty())
    {
      const symbolt *class_sym = cpp_typecheck.symbol_table.lookup(class_tag);
      if(
        class_sym != nullptr &&
        class_sym->type.find(ID_C_template).is_not_nil() &&
        class_sym->type.find(ID_C_template_arguments).is_not_nil())
      {
        cpp_typecheck.template_map.build(
          static_cast<const template_typet &>(
            class_sym->type.find(ID_C_template)),
          static_cast<const cpp_template_args_tct &>(
            class_sym->type.find(ID_C_template_arguments)));
      }
      member_class_tag = class_tag;
    }
  }

  // If explicit template arguments were provided (partial explicit args),
  // pre-populate the template map with them before deduction.
  const irept &stored_args = expr.find(ID_C_template_arguments);
  if(stored_args.is_not_nil())
  {
    const cpp_template_args_tct &explicit_args =
      to_cpp_template_args_tc(stored_args);
    const auto &params = cpp_declaration.template_type().template_parameters();
    for(std::size_t i = 0;
        i < explicit_args.arguments().size() && i < params.size();
        i++)
    {
      if(
        explicit_args.arguments()[i].id() != ID_unassigned &&
        explicit_args.arguments()[i].type().id() != ID_unassigned)
      {
        // Per [temp.arg]/2: resolve template parameter references
        // in explicit args using the enclosing template_map.
        exprt resolved_arg = explicit_args.arguments()[i];
        if(resolved_arg.id() == ID_type)
          cpp_typecheck.template_map.apply(resolved_arg.type());
        cpp_typecheck.template_map.set(params[i], resolved_arg);
      }
    }
  }

  // there should be exactly one declarator
  PRECONDITION(cpp_declaration.declarators().size() == 1);

  const cpp_declaratort &function_declarator =
    cpp_declaration.declarators().front();

  // and that needs to have function type
  if(function_declarator.type().id() != ID_function_type)
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "expected function type for function template"
                          << messaget::eom;
    throw 0;
  }

  cpp_save_scopet cpp_saved_scope(cpp_typecheck.cpp_scopes);

  // we need the template scope
  cpp_scopet *template_scope = static_cast<cpp_scopet *>(
    cpp_typecheck.cpp_scopes.id_map[template_identifier]);

  if(template_scope == nullptr)
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error() << "template identifier: " << template_identifier
                          << '\n'
                          << "function template instantiation error"
                          << messaget::eom;
    throw 0;
  }

  // enter the scope of the template
  cpp_typecheck.cpp_scopes.go_to(*template_scope);

  // walk through the function parameters
  const irept::subt &parameters =
    function_declarator.type().find(ID_parameters).get_sub();

  exprt::operandst::const_iterator it = fargs.operands.begin();

  // Skip the implicit 'this' object argument for member functions.
  if(fargs.has_object && it != fargs.operands.end())
    ++it;

  // Track pack expansion size for non-empty packs
  std::size_t pack_expansion_size = 0;
  bool has_non_empty_pack = false;
  std::vector<typet> pack_deduced_types;

  for(const auto &parameter : parameters)
  {
    if(it == fargs.operands.end())
      break;

    if(parameter.id() == ID_cpp_declaration)
    {
      const cpp_declarationt &arg_declaration = to_cpp_declaration(parameter);

      // again, there should be one declarator
      DATA_INVARIANT(
        arg_declaration.declarators().size() == 1, "exactly one declarator");

      const cpp_declaratort &declarator = arg_declaration.declarators().front();

      // Check if this is a parameter pack (e.g., Args... args)
      bool is_pack = declarator.get_bool(ID_ellipsis) ||
                     declarator.type().get_bool(ID_ellipsis);

      // Per [temp.deduct.call]/3: detect forwarding references (T&&)
      // before type conversion, by checking if the declarator has
      // rvalue_reference type and the base is a template parameter.
      // This applies to a forwarding-reference parameter pack
      // (Args&&... args) as well as a single forwarding reference.
      bool is_forwarding_ref = false;
      if(
        (declarator.type().id() == ID_frontend_pointer ||
         declarator.type().id() == ID_pointer) &&
        declarator.type().get_bool(ID_C_rvalue_reference))
      {
        // The base type (from the declaration) should be a template param
        const auto &base = arg_declaration.type();
        if(
          base.id() == ID_cpp_name ||
          base.id() == ID_template_parameter_symbol_type)
          is_forwarding_ref = true;
      }

      // turn into type
      typet arg_type = declarator.merge_type(arg_declaration.type());

      // We only convert the arg_type,
      // and don't typecheck it -- that could cause all
      // sorts of trouble.
      cpp_convert_plain_type(arg_type, cpp_typecheck.get_message_handler());

      // Per [temp.deduct.call]/1: resolve remaining simple cpp_name
      // types to actual types for deduction via scope lookup.
      if(
        arg_type.id() == ID_cpp_name && arg_type.get_sub().size() == 1 &&
        arg_type.get_sub().front().id() == ID_name)
      {
        irep_idt name = arg_type.get_sub().front().get(ID_identifier);
        if(!name.empty())
        {
          auto ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
            name, cpp_scopet::RECURSIVE);
          for(const auto *id_ptr : ids)
          {
            if(id_ptr->is_class())
            {
              arg_type = struct_tag_typet{id_ptr->identifier};
              break;
            }
          }
        }
      }

      // For pack parameters, deduce from all remaining arguments
      if(is_pack)
      {
        pack_expansion_size =
          static_cast<std::size_t>(fargs.operands.end() - it);
        has_non_empty_pack = pack_expansion_size > 0;
        // Collect each argument's type for heterogeneous packs
        for(; it != fargs.operands.end(); ++it)
        {
          // [temp.deduct.call]/3 applied per pack element: for a
          // forwarding-reference pack (Args&&... args), an lvalue
          // argument of type A deduces the corresponding pack element
          // as "lvalue reference to A"; an rvalue argument deduces it
          // as A.  Without this the element was deduced as a plain
          // rvalue reference (Args&& with Args=A), so an lvalue
          // argument bound through a dangling/garbage rvalue reference.
          // This is the pack analogue of the single forwarding-
          // reference case handled below.
          if(is_forwarding_ref)
          {
            bool elem_is_lvalue = it->get_bool(ID_C_lvalue);
            if(
              elem_is_lvalue && it->id() == ID_dereference &&
              it->operands().size() == 1 &&
              it->operands().front().type().id() == ID_pointer &&
              it->operands().front().type().get_bool(ID_C_rvalue_reference) &&
              it->operands().front().id() != ID_symbol)
            {
              elem_is_lvalue = false;
            }
            typet deduced_type =
              elem_is_lvalue ? ::reference_type(it->type()) : it->type();
            pack_deduced_types.push_back(deduced_type);
            guess_template_args(arg_declaration.type(), deduced_type);
            continue;
          }

          typet arg_actual_type = it->type();
          if(arg_type.id() == ID_cpp_name)
          {
            arg_actual_type.remove(ID_C_constant);
            arg_actual_type.remove(ID_C_volatile);
            if(arg_actual_type.id() == ID_array)
              arg_actual_type =
                pointer_type(to_array_type(arg_actual_type).element_type());
          }
          pack_deduced_types.push_back(arg_actual_type);
          guess_template_args(arg_type, arg_actual_type);
        }
        continue;
      }

      // [temp.deduct.call]/3: forwarding reference — if the parameter is
      // T&& where T is a template parameter, and the argument is an
      // lvalue, deduce T as "lvalue reference to A".
      // Exception: a dereference of an rvalue reference (e.g., the
      // result of std::move) is an xvalue, not an lvalue.
      // Named rvalue reference variables are lvalues, not xvalues.
      bool is_lvalue = it->get_bool(ID_C_lvalue);
      if(
        is_lvalue && it->id() == ID_dereference && it->operands().size() == 1 &&
        it->operands().front().type().id() == ID_pointer &&
        it->operands().front().type().get_bool(ID_C_rvalue_reference) &&
        it->operands().front().id() != ID_symbol)
      {
        is_lvalue = false;
      }
      if(is_forwarding_ref && is_lvalue)
      {
        // Per [temp.deduct.call]/3: for forwarding reference T&&
        // and lvalue argument of type A, deduce T as "lvalue
        // reference to A" (preserving cv-qualifiers).
        typet lvalue_ref_type = ::reference_type(it->type());
        guess_template_args(arg_declaration.type(), lvalue_ref_type);
      }
      else if(
        is_rvalue_reference(arg_type) && is_lvalue &&
        (to_pointer_type(arg_type).base_type().id() == ID_cpp_name ||
         to_pointer_type(arg_type).base_type().id() ==
           ID_template_parameter_symbol_type))
      {
        typet lvalue_ref_type = ::reference_type(it->type());
        guess_template_args(
          to_pointer_type(arg_type).base_type(), lvalue_ref_type);
      }
      else
      {
        // [temp.deduct.call]/4: when P is just T (not T&, T*, etc.),
        // top-level cv-qualifiers on A are ignored.
        // Also, array types decay to pointer types per [temp.deduct.call]/4.
        // Exception: for forwarding references (T&&), cv-qualifiers
        // are preserved per [temp.deduct.call]/3.
        typet arg_actual_type = it->type();
        if(arg_type.id() == ID_cpp_name && !is_forwarding_ref)
        {
          arg_actual_type.remove(ID_C_constant);
          arg_actual_type.remove(ID_C_volatile);
          if(arg_actual_type.id() == ID_array)
            arg_actual_type =
              pointer_type(to_array_type(arg_actual_type).element_type());
        }
        if(is_forwarding_ref && is_rvalue_reference(arg_type))
          guess_template_args(
            to_pointer_type(arg_type).base_type(), arg_actual_type);
        else
          guess_template_args(arg_type, arg_actual_type);
      }
    }

    ++it;
  }

  // see if that has worked out

  cpp_template_args_tct template_args =
    cpp_typecheck.template_map.build_template_args(
      cpp_declaration.template_type());

  // [temp.deduct.call]/4.3: when P has the form of a simple-template-id and
  // the argument A is a class derived from a specialization of that template,
  // the template arguments are deduced from the base-class subobject of A
  // (see [temp.deduct.call] Example 5: deducing `T...` in `f(const X<T...>&)`
  // from `struct D : X<int>` yields `f<int>`).  When such a deduced pack is a
  // template parameter pack appearing inside a parameter *type* (the `U...`
  // in `Base<0, U...>`, as opposed to a function parameter pack `U... args`),
  // guess_template_args records the full set of deduced elements in
  // pack_args_map, but build_template_args above emits only a single
  // placeholder argument for the pack (it looks up the scalar type_map
  // binding).  Expand that placeholder to the full set of deduced elements so
  // the instantiated specialization has the correct arity.  Without this, e.g.
  // packsize(Der<int,int>) deducing `U = <int, int>` is instantiated as the
  // 1-element packsize<int> whose body wrongly evaluates sizeof...(U) to 1.
  // The function-parameter-pack case (has_non_empty_pack) is handled
  // separately by the block below using pack_deduced_types, so this is
  // confined to the disjoint type-internal-pack case.
  if(!has_non_empty_pack)
  {
    const auto &params = cpp_declaration.template_type().template_parameters();
    auto &args = template_args.arguments();
    for(std::size_t i = 0; i < params.size() && i < args.size(); ++i)
    {
      if(!(params[i].get_bool(ID_ellipsis) && params[i].id() == ID_type))
        continue;
      const irep_idt pack_id = params[i].type().get(ID_identifier);
      if(pack_id.empty())
        continue;
      // Expand packs deduced via the derived-to-base rule
      // ([temp.deduct.call]/4.3), and -- while draining the deferred
      // method-body queue (instantiating_deferred_body) -- also directly
      // deduced packs.  A directly-deduced pack in an eagerly-converted body
      // (e.g. a call in main that the constexpr evaluator folds) is left to
      // the existing machinery: expanding it there would materialise a runtime
      // instance and suppress the constant-folding the call relies on.  When
      // the call is instead resolved during the method-body drain it is a real
      // (non-constant-evaluated) call whose instance must have the deduced
      // arity, so the single placeholder build_template_args emitted is
      // expanded here ([temp.variadic]).
      if(
        derived_to_base_deduced_packs.find(pack_id) ==
          derived_to_base_deduced_packs.end() &&
        !cpp_typecheck.instantiating_deferred_body)
        continue;
      const auto pa_it = cpp_typecheck.template_map.pack_args_map.find(pack_id);
      if(pa_it == cpp_typecheck.template_map.pack_args_map.end())
        continue;
      const std::vector<typet> &elems = pa_it->second;
      if(elems.size() <= 1)
        continue;
      args[i] = exprt(ID_type);
      args[i].type() = elems[0];
      for(std::size_t j = 1; j < elems.size(); ++j)
      {
        exprt arg(ID_type);
        arg.type() = elems[j];
        args.insert(args.begin() + i + j, arg);
      }
      break;
    }
  }

  // [temp.variadic]/5: the same full-arity expansion for a NON-type parameter
  // pack deduced from a class-template-id argument (the `I` in matching
  // `seq<I...>` against `seq<1,2>`).  build_template_args emits a single scalar
  // placeholder (the pack's first VALUE via expr_map); expand it to the full
  // set of deduced element values recorded in pack_expr_map so the signature --
  // e.g. a `decltype(add(I...))` return type, or the body `add(I...)` -- sees
  // the correct arity.  Without this the deduced pack collapses to a single
  // element and the call has the wrong number of arguments ("no match").
  {
    const auto &params = cpp_declaration.template_type().template_parameters();
    auto &args = template_args.arguments();
    for(std::size_t i = 0; i < params.size() && i < args.size(); ++i)
    {
      if(!params[i].get_bool(ID_ellipsis) || params[i].id() == ID_type)
        continue;
      const irep_idt pack_id = params[i].get(ID_identifier);
      if(pack_id.empty())
        continue;
      const auto pe_it = cpp_typecheck.template_map.pack_expr_map.find(pack_id);
      if(pe_it == cpp_typecheck.template_map.pack_expr_map.end())
        continue;
      const std::vector<exprt> &vals = pe_it->second;
      if(vals.size() <= 1)
        continue;
      args[i] = vals[0];
      for(std::size_t j = 1; j < vals.size(); ++j)
        args.insert(args.begin() + i + j, vals[j]);
      break;
    }
  }

  // For non-empty variadic packs, expand the single deduced pack type
  // to N copies in the template args so that template instantiation
  // sees the correct number of arguments.
  if(has_non_empty_pack && pack_expansion_size > 1)
  {
    const auto &params = cpp_declaration.template_type().template_parameters();
    auto &args = template_args.arguments();
    // Find the pack parameter (last one with ellipsis)
    for(std::size_t i = 0; i < params.size() && i < args.size(); ++i)
    {
      if(params[i].get_bool(ID_ellipsis))
      {
        // Use individually deduced types for heterogeneous packs
        if(pack_deduced_types.size() == pack_expansion_size)
        {
          // Replace the single deduced type with the first, then
          // insert the rest
          args[i] = exprt(ID_type);
          args[i].type() = pack_deduced_types[0];
          for(std::size_t j = 1; j < pack_expansion_size; ++j)
          {
            exprt arg(ID_type);
            arg.type() = pack_deduced_types[j];
            args.insert(args.begin() + i + j, arg);
          }
        }
        else
        {
          // Fallback: duplicate the single deduced type
          exprt pack_arg = args[i];
          for(std::size_t j = 1; j < pack_expansion_size; ++j)
            args.insert(args.begin() + i + j, pack_arg);
        }
        break;
      }
    }
  }

  // Convert deduction-failed markers (ID_nil) to ID_unassigned so that
  // has_unassigned() detects them and rejects the template.  Keep the
  // failure distinguishable (#deduction_failed): for a parameter PACK,
  // ID_unassigned normally means "zero elements deduced", which the
  // default-application loop below legitimately turns into an empty pack
  // ([temp.variadic]/7) -- but a pack POISONED by a form mismatch (N5008
  // [temp.deduct.type]/8: P and A with incompatible forms make the entire
  // deduction fail) must reject the candidate instead of being resurrected
  // as an empty pack.  Otherwise e.g. the constrained tuple-swap overload
  // `swap(tuple<_Elements...>&, ...)` probed with `int*` arguments binds
  // _Elements to the zero-length-pack sentinel and collaterally
  // instantiates `swap<void>` from its enable_if constraint.
  for(auto &arg : template_args.arguments())
  {
    if(arg.type().id() == ID_nil)
    {
      arg.type().id(ID_unassigned);
      arg.set("#deduction_failed", true);
    }
  }

  // Apply default template arguments for any remaining unassigned parameters.
  // For example, template<typename T, typename R = T, ...> where R is not
  // deducible from function parameters but has a default value.
  // Also handle variadic packs with zero arguments.
  bool variadic_pack_empty = false;
  irep_idt pack_param_name;
  if(template_args.has_unassigned())
  {
    const auto &params = cpp_declaration.template_type().template_parameters();
    auto &args = template_args.arguments();

    // N5008 [temp.param]/11: a template parameter pack of a function template
    // may be followed by further template parameters, provided they are
    // deducible from the parameter-type-list or have default arguments.  When a
    // non-empty pack has been expanded above, it occupies `pack_expansion_size`
    // slots in `args` instead of one, so every template parameter that FOLLOWS
    // the pack is shifted right in `args` by (pack_expansion_size - 1).  Map an
    // argument position back to its template parameter accordingly, and iterate
    // over every argument position (not only the first params.size()) so a
    // trailing parameter whose default must be applied (e.g. `class X = void`
    // after `class... W`) is not skipped and left spuriously unassigned.
    // Locate this function/constructor template's own parameter pack (if any).
    // It need not be the last template parameter ([temp.param]/11), and it may
    // be empty (pack_expansion_size == 0) in this instantiation.
    std::size_t pack_param_index = params.size();
    for(std::size_t p = 0; p < params.size(); ++p)
    {
      if(params[p].get_bool(ID_ellipsis))
      {
        pack_param_index = p;
        break;
      }
    }
    const std::size_t pack_extra =
      (has_non_empty_pack && pack_expansion_size > 0 &&
       pack_param_index < params.size())
        ? pack_expansion_size - 1
        : 0;

    // N5008 [temp.variadic]/8 + [basic.scope.temp]/2: `sizeof...(pack)` counts
    // the elements of the pack named in the current scope.  A template
    // parameter that FOLLOWS the pack may have a default argument that queries
    // the pack size -- e.g. std::_Tuple_impl's forwarding constructor
    // constraint `enable_if_t<sizeof...(_Tail) == sizeof...(_UTail)>` on the
    // defaulted trailing parameter.  The pack's size is otherwise recorded (in
    // pack_size_map) only AFTER this default-application loop, so the default
    // would evaluate `sizeof...(pack)` against a stale count.  Record it now --
    // including the EMPTY case (size 0): in a recursive instantiation an
    // enclosing instance's same-named pack is still in pack_size_map, so unless
    // THIS instance's (possibly empty) pack is recorded, the scope-qualified
    // lookup in the sizeof... evaluation finds nothing and falls back to a
    // suffix match against the stale outer pack (mis-sizing the constraint and
    // wrongly rejecting the constructor -- the std::_Tuple_impl terminal
    // recursion).
    if(pack_param_index < params.size())
    {
      const irep_idt pack_id =
        params[pack_param_index].type().get(ID_identifier);
      if(!pack_id.empty())
        cpp_typecheck.template_map.pack_size_map[pack_id] = pack_expansion_size;
    }

    // An EMPTY pack (deduced to zero elements) occupies one placeholder slot in
    // `args` (emitted by build_template_args) but zero real arguments.  When
    // template parameters FOLLOW the pack ([temp.param]/11), dropping the
    // placeholder shifts those parameters one position ahead of their argument
    // slots; track that shift so their defaults are still applied (rather than
    // truncating them away with the pack).
    std::size_t empty_pack_shift = 0;

    for(std::size_t i = 0; i < args.size(); i++)
    {
      // Template-parameter index corresponding to argument position i: a
      // non-empty pack occupies (pack_extra + 1) argument slots, so parameters
      // after it are reached at an argument index shifted right by pack_extra;
      // an already-dropped EMPTY pack leaves its following parameters one
      // position ahead of their argument slots (empty_pack_shift).
      std::size_t pi = i + empty_pack_shift;
      if(pack_extra > 0 && i > pack_param_index + pack_extra)
        pi = i - pack_extra;
      if(pi >= params.size())
        continue;

      if(args[i].id() == ID_unassigned || args[i].type().id() == ID_unassigned)
      {
        const template_parametert &param =
          static_cast<const template_parametert &>(params[pi]);

        // Variadic pack with zero arguments.
        if(param.get_bool(ID_ellipsis))
        {
          // N5008 [temp.deduct.type]/8: if the pack was poisoned by a form
          // mismatch (P names a class-template specialization the argument
          // is not an instance of), the entire deduction has FAILED; the
          // pack is not "empty", the candidate is not viable.
          if(args[i].get_bool("#deduction_failed"))
          {
            return nil_exprt();
          }

          const std::string full_id =
            id2string(param.type().get(ID_identifier));
          auto pos = full_id.rfind("::");
          pack_param_name =
            pos != std::string::npos ? full_id.substr(pos + 2) : full_id;
          variadic_pack_empty = true;

          // N5008 [temp.param]/11: if further template parameters follow the
          // (empty) pack, do NOT truncate them away -- the empty pack simply
          // contributes no arguments.  Remove only its placeholder slot and
          // continue so the trailing parameters still receive their (deducible
          // or default) arguments.  `first(5)` for
          // `template<class U, class... W, class X = void> ... first(U, W...)`
          // must keep and default `X`; truncating dropped it, leaving the call
          // unresolvable (the residual std::_Tuple_impl terminal recursion).
          if(pi + 1 < params.size())
          {
            args.erase(args.begin() + i);
            ++empty_pack_shift;
            --i; // ++i re-examines the now-shifted trailing parameter's slot
            continue;
          }

          // The pack is the last template parameter: truncate at it.
          args.resize(i);
          break;
        }

        if(param.has_default_argument() && param.id() == ID_type)
        {
          typet default_type = param.default_argument().type();
          // Evaluate the default argument in a SFINAE context: suppress
          // error messages and treat failure as deduction failure.
          // error count save/restore instead of null_handler
          const std::size_t sfinae_err_2 =
            cpp_typecheck.get_message_handler().get_message_count(
              messaget::M_ERROR);
          try
          {
            cpp_save_scopet saved_scope(cpp_typecheck.cpp_scopes);
            cpp_idt *tscope =
              cpp_typecheck.cpp_scopes.id_map[template_symbol.name];
            if(tscope != nullptr)
              cpp_typecheck.cpp_scopes.go_to(*tscope);
            // N5008 [temp.variadic]/5: if the default argument's operand
            // contains a function-call argument pack expansion over the
            // enclosing class parameter pack (e.g. a constructor's
            // `decltype(declval<F&>()(declval<A>()...))` SFINAE constraint),
            // expand it into one argument per deduced element and substitute
            // the deduced template arguments BEFORE type-checking the
            // operand.  Otherwise the bare pack reference is rejected (only
            // the single-element convenience binding works), so e.g. a
            // multi-argument std::function fails to construct.  The plain
            // (no-pack) path keeps the original typecheck-then-apply order.
            if(contains_call_argument_pack(default_type))
            {
              // The default argument's operand contains a function-call
              // argument pack expansion over the enclosing class parameter
              // pack.  apply() expands it (and substitutes the deduced
              // arguments); run it BEFORE type-checking so the operand is
              // concrete -- otherwise the bare pack reference is rejected and
              // a necessary user-defined conversion is silently dropped (e.g.
              // a multi-argument std::function fails to construct).
              cpp_typecheck.template_map.apply(default_type);
              cpp_typecheck.typecheck_type(default_type);
            }
            else
            {
              cpp_typecheck.typecheck_type(default_type);
              cpp_typecheck.template_map.apply(default_type);
            }
            args[i] = exprt(ID_type);
            args[i].type() = default_type;
            cpp_typecheck.template_map.set(param, args[i]);
            cpp_typecheck.get_message_handler().set_message_count(
              messaget::M_ERROR, sfinae_err_2);
          }
          catch(...)
          {
            cpp_typecheck.get_message_handler().set_message_count(
              messaget::M_ERROR, sfinae_err_2);
            // If this is an anonymous type parameter, the default
            // argument is a SFINAE constraint (e.g.,
            // typename = enable_if_t<...>).
            const irep_idt &param_id = param.type().get(ID_identifier);
            bool is_anonymous = param_id.empty();
            if(!is_anonymous)
            {
              const std::string pid = id2string(param_id);
              auto pos = pid.rfind("::");
              const std::string local =
                pos != std::string::npos ? pid.substr(pos + 2) : pid;
              is_anonymous = local.empty() || local.find("anon") == 0;
            }
            if(is_anonymous)
            {
              // SFINAE constraint evaluation failed — reject the
              // template (substitution failure is not an error).
              return nil_exprt();
            }
          }
        }
        else if(param.has_default_argument() && param.id() != ID_type)
        {
          // Non-type parameter with default value (e.g.,
          // typename enable_if<...>::type = 0).
          // Evaluate the parameter type in a SFINAE context.
          // error count save/restore instead of null_handler
          const std::size_t sfinae_err_3 =
            cpp_typecheck.get_message_handler().get_message_count(
              messaget::M_ERROR);
          try
          {
            // [temp.point] p1,7: the context of a template instantiation
            // includes both the definition and instantiation contexts.
            // Use the current (instantiation) scope rather than the
            // template (definition) scope, because the template scope
            // may lack using-scope links to enclosing inline namespaces
            // (e.g., std::__1 in libc++). The instantiation scope has
            // full visibility of the enclosing namespace.
            // N5008 [temp.deduct]/5: the values of deduced template
            // parameters are available when subsequent default template
            // arguments are instantiated.  A default whose SFINAE guard
            // names this function template's parameter pack in an explicit
            // template-argument list (e.g. std::tuple's constructor
            // constraint `enable_if_t<..._is_implicitly_constructible
            // <_UElements...>(), bool> = true`) needs the pack's deduced
            // ELEMENT TYPES bound in the map; the map at this point holds
            // only enclosing bindings, so the `_UElements...` expansion
            // collapses to an empty argument list and the constraint is
            // folded over no arguments, wrongly disabling the constructor.
            // Try the historical order first (some constraints only resolve
            // against the enclosing map); on failure, retry with the pack's
            // deduced element types bound.
            auto eval_default = [&]() -> exprt
            {
              typet param_type = param.type();
              cpp_typecheck.template_map.apply(param_type);
              cpp_typecheck.typecheck_type(param_type);
              // Use the default value
              exprt default_val = param.default_argument();
              cpp_typecheck.template_map.apply(default_val);
              cpp_typecheck.typecheck_expr(default_val);
              return default_val;
            };
            exprt default_val;
            try
            {
              default_val = eval_default();
            }
            catch(...)
            {
              if(pack_param_index >= params.size())
                throw; // no pack to bind: nothing more to try
              const irep_idt pack_id =
                params[pack_param_index].type().get(ID_identifier);
              if(pack_id.empty())
                throw;
              std::vector<typet> deduced_types;
              std::vector<exprt> deduced_exprs;
              for(std::size_t j = pack_param_index;
                  j < pack_param_index + pack_expansion_size && j < args.size();
                  ++j)
              {
                if(args[j].id() == ID_unassigned)
                  continue;
                if(args[j].id() == ID_type)
                {
                  if(
                    args[j].type().id() != ID_unassigned &&
                    args[j].type().id() != ID_nil)
                    deduced_types.push_back(args[j].type());
                }
                else
                  deduced_exprs.push_back(args[j]);
              }
              if(deduced_types.empty() && deduced_exprs.empty())
                throw;
              cpp_saved_template_mapt retry_map(cpp_typecheck.template_map);
              if(!deduced_types.empty())
                cpp_typecheck.template_map.pack_args_map[pack_id] =
                  deduced_types;
              else
                cpp_typecheck.template_map.pack_expr_map[pack_id] =
                  deduced_exprs;
              cpp_typecheck.get_message_handler().set_message_count(
                messaget::M_ERROR, sfinae_err_3);
              default_val = eval_default();
            }
            args[i] = default_val;
            cpp_typecheck.template_map.set(param, args[i]);
            cpp_typecheck.get_message_handler().set_message_count(
              messaget::M_ERROR, sfinae_err_3);
          }
          catch(...)
          {
            cpp_typecheck.get_message_handler().set_message_count(
              messaget::M_ERROR, sfinae_err_3);
            // SFINAE: substitution failure in parameter type
            return nil_exprt();
          }
        }
      }
    }
  }

  if(template_args.has_unassigned())
    return nil_exprt(); // give up

  // Build the type of the function.

  typet function_type = function_declarator.merge_type(cpp_declaration.type());

  // When a variadic pack is empty, remove pack-expanded parameters from
  // the function type before typechecking, since the pack type name
  // (e.g. Base) has no mapping in the template map.
  if(variadic_pack_empty && function_type.id() == ID_function_type)
  {
    irept::subt &params = function_type.add(ID_parameters).get_sub();
    // Remove parameters whose declarator has ellipsis (the pack parameter)
    params.erase(
      std::remove_if(
        params.begin(),
        params.end(),
        [](const irept &p)
        {
          if(p.id() == ID_cpp_declaration)
          {
            const auto &decl = to_cpp_declaration(p);
            if(!decl.declarators().empty())
            {
              const auto &d = decl.declarators().front();
              return d.get_bool(ID_ellipsis) || d.type().get_bool(ID_ellipsis);
            }
          }
          return p.id() == ID_ellipsis;
        }),
      params.end());
    // Also strip ellipsis and pack parameter from nested function pointer types
    for(auto &p : params)
    {
      if(p.id() == ID_cpp_declaration)
      {
        auto &decl = to_cpp_declaration(p);
        if(!decl.declarators().empty())
        {
          irept &dtype = decl.declarators().front().type();
          if(dtype.id() == ID_frontend_pointer)
          {
            if(
              !dtype.get_sub().empty() &&
              dtype.get_sub().front().id() == ID_function_type)
            {
              irept::subt &inner_params =
                dtype.get_sub().front().add(ID_parameters).get_sub();
              inner_params.erase(
                std::remove_if(
                  inner_params.begin(),
                  inner_params.end(),
                  [&pack_param_name](const irept &ip)
                  {
                    if(ip.id() == ID_ellipsis)
                      return true;
                    if(ip.id() == ID_cpp_declaration)
                    {
                      const auto &d = to_cpp_declaration(ip);
                      if(d.type().id() == ID_cpp_name)
                      {
                        for(const auto &sub : d.type().get_sub())
                        {
                          if(
                            sub.id() == ID_name &&
                            sub.get(ID_identifier) == pack_param_name)
                            return true;
                        }
                      }
                    }
                    return false;
                  }),
                inner_params.end());
            }
          }
        }
      }
    }
  }

  // When a variadic pack is non-empty, expand the pack parameter to
  // N copies in the function type so that it matches the argument count.
  if(has_non_empty_pack && function_type.id() == ID_function_type)
  {
    irept::subt &fparams = function_type.add(ID_parameters).get_sub();
    irept::subt expanded;
    for(const auto &p : fparams)
    {
      bool is_pack_param = false;
      if(p.id() == ID_cpp_declaration)
      {
        const auto &decl = to_cpp_declaration(p);
        if(!decl.declarators().empty())
        {
          const auto &d = decl.declarators().front();
          is_pack_param =
            d.get_bool(ID_ellipsis) || d.type().get_bool(ID_ellipsis);
        }
      }
      else if(p.id() == ID_ellipsis)
      {
        is_pack_param = true;
      }

      if(is_pack_param)
      {
        // Create N copies of the pack parameter without the ellipsis flag
        for(std::size_t i = 0; i < pack_expansion_size; ++i)
        {
          if(p.id() == ID_cpp_declaration)
          {
            irept copy = p;
            auto &decl = static_cast<cpp_declarationt &>(copy);
            if(!decl.declarators().empty())
            {
              auto &d = decl.declarators().front();
              d.set(ID_ellipsis, false);
              d.type().set(ID_ellipsis, false);
            }
            // For heterogeneous packs, set the type from the
            // individually deduced types
            if(i < pack_deduced_types.size())
              decl.type() = pack_deduced_types[i];
            expanded.push_back(std::move(copy));
          }
        }
      }
      else
      {
        expanded.push_back(p);
      }
    }
    fparams = std::move(expanded);
  }

  // [temp.deduct.call]/1 + [temp.variadic]/5: a deduced function parameter
  // pack must be recorded as a pack (pack_args_map / pack_size_map), not only
  // as a scalar type binding in type_map, so that a pack expansion in the
  // (dependent) return type -- e.g. `typename invoke_result<F, A...>::type` --
  // expands the pack's elements and drops the `...` expansion marker.  With a
  // scalar binding alone, `apply` substitutes the single deduced type but
  // leaves a dangling expansion marker on it, and the subsequent
  // pack-expansion of a non-pack type fails (rejecting the deduction).  This
  // recording is confined to the deduction by the saved_map guard above.
  if(has_non_empty_pack && !pack_deduced_types.empty())
  {
    for(const auto &param :
        cpp_declaration.template_type().template_parameters())
    {
      if(param.get_bool(ID_ellipsis) && param.id() == ID_type)
      {
        const irep_idt pack_id = param.type().get(ID_identifier);
        if(!pack_id.empty())
        {
          cpp_typecheck.template_map.pack_args_map[pack_id] =
            pack_deduced_types;
          cpp_typecheck.template_map.pack_size_map[pack_id] =
            pack_expansion_size;
        }
        break;
      }
    }
  }
  else
  {
    // N5008 [temp.deduct.call], [temp.arg.explicit]/4 (Note 1): a trailing
    // function parameter pack supplied no arguments is deduced as an empty
    // pack.  The deduction loop above stops when the argument list is
    // exhausted, before reaching the pack, so the pack keeps only its
    // build_unassigned placeholder (an ID_unassigned type_map entry) and is
    // recorded nowhere as empty.  Record it with size 0 -- treating the
    // unassigned placeholder as unbound -- so that a pack expansion
    // referencing it in the (trailing-return) decltype, e.g. `f(a...)`,
    // collapses to zero arguments ([temp.variadic]/5,7) instead of leaving a
    // dangling `...` over a parameter that no longer exists.
    for(const auto &param :
        cpp_declaration.template_type().template_parameters())
    {
      if(param.get_bool(ID_ellipsis) && param.id() == ID_type)
      {
        const irep_idt pack_id = param.type().get(ID_identifier);
        const auto tm_it = cpp_typecheck.template_map.type_map.find(pack_id);
        const bool bound = tm_it != cpp_typecheck.template_map.type_map.end() &&
                           tm_it->second.id() != ID_unassigned &&
                           tm_it->second.id() != ID_nil;
        if(
          !pack_id.empty() && !bound &&
          cpp_typecheck.template_map.pack_args_map.find(pack_id) ==
            cpp_typecheck.template_map.pack_args_map.end())
          cpp_typecheck.template_map.pack_size_map[pack_id] = 0;
        break;
      }
    }
  }

  // Type-check the function type in a SFINAE context: suppress error
  // count so that substitution failures (e.g., enable_if with false
  // condition in the return type) are silently discarded.
  message_handlert &old_handler = cpp_typecheck.get_message_handler();
  const std::size_t sfinae_errors =
    old_handler.get_message_count(messaget::M_ERROR);
  try
  {
    // Apply template map to the function type before typechecking.
    // This handles template template parameters where C<T> in the
    // function type needs to be replaced with the actual instantiated type.
    cpp_typecheck.template_map.apply(function_type);
    // Also apply to parameters stored as cpp_declarations
    if(function_type.id() == ID_function_type)
    {
      irept::subt &params = function_type.add(ID_parameters).get_sub();
      for(auto &p : params)
      {
        if(p.id() == ID_cpp_declaration)
        {
          auto &decl = static_cast<cpp_declarationt &>(p);
          cpp_typecheck.template_map.apply(decl.type());
        }
      }

      // For trailing return types with decltype referencing parameters,
      // put function parameters temporarily into scope.  N5008 [expr.type]:
      // the decltype operand may be nested inside the return type (e.g. as a
      // template argument, `-> ranget<decltype(c.begin())>`), not only be the
      // whole return type (`-> decltype(c.begin())`); scan the return type for
      // any decltype so the parameter names it references resolve during the
      // type-check below.
      std::function<bool(const irept &)> contains_decltype =
        [&](const irept &t) -> bool
      {
        if(t.id() == ID_decltype)
          return true;
        for(const auto &s : t.get_sub())
          if(contains_decltype(s))
            return true;
        for(const auto &ns : t.get_named_sub())
          if(contains_decltype(ns.second))
            return true;
        return false;
      };
      // N5008 [over.match.viable]/2: a call that supplies more arguments than
      // a non-variadic overload has parameters can never select that overload.
      // Do not insert synthetic parameter symbols (needed only to resolve a
      // `decltype` naming a parameter in the trailing return type) for such a
      // non-viable overload: those symbols are keyed by template scope +
      // parameter name and are not removed, so speculatively type-checking a
      // non-viable overload's return type would leave a stale symbol of the
      // wrong type behind, poisoning a later, viable resolution of the same
      // template (e.g. the one-parameter container overload of `make_range`
      // deducing its parameter from the first argument of a two-argument
      // iterator call, then that stale symbol breaking `make_range(container)`
      // whose `decltype(c.begin())` is evaluated against the wrong type).
      std::size_t non_variadic_param_count = 0;
      bool has_variadic_param = false;
      for(const auto &p : params)
      {
        if(p.id() == ID_ellipsis)
        {
          has_variadic_param = true;
          continue;
        }
        if(p.id() != ID_cpp_declaration)
          continue;
        const auto &pd = static_cast<const cpp_declarationt &>(p);
        if(
          !pd.declarators().empty() &&
          (pd.declarators().front().get_bool(ID_ellipsis) ||
           pd.declarators().front().type().get_bool(ID_ellipsis) ||
           pd.type().get_bool(ID_ellipsis)))
          has_variadic_param = true;
        else
          ++non_variadic_param_count;
      }
      const bool too_many_arguments =
        fargs.in_use && !fargs.has_object && !has_variadic_param &&
        fargs.operands.size() > non_variadic_param_count;
      if(
        !too_many_arguments && function_type.has_subtype() &&
        contains_decltype(to_type_with_subtype(function_type).subtype()))
      {
        for(const auto &p : params)
        {
          if(p.id() != ID_cpp_declaration)
            continue;
          const auto &pdecl = static_cast<const cpp_declarationt &>(p);
          if(pdecl.declarators().empty())
            continue;
          typet ptype = pdecl.type();
          cpp_typecheck.typecheck_type(ptype);
          const auto &pname_sub = pdecl.declarators().front().name().get_sub();
          if(pname_sub.empty())
            continue;
          const irep_idt &pname = pname_sub.front().get(ID_identifier);
          if(pname.empty())
            continue;
          const std::string sym_name =
            id2string(cpp_typecheck.cpp_scopes.current_scope().prefix) +
            id2string(pname);
          if(!cpp_typecheck.symbol_table.has_symbol(sym_name))
          {
            auxiliary_symbolt psym;
            psym.name = sym_name;
            psym.base_name = pname;
            psym.type = ptype;
            psym.mode = ID_cpp;
            psym.is_parameter = true;
            cpp_typecheck.symbol_table.insert(std::move(psym));
            const symbolt &inserted =
              cpp_typecheck.symbol_table.lookup_ref(sym_name);
            cpp_idt &id = cpp_typecheck.cpp_scopes.put_into_scope(inserted);
            id.id_class = cpp_idt::id_classt::SYMBOL;
          }
        }
      }
    }
    cpp_typecheck.typecheck_type(function_type);
    old_handler.set_message_count(messaget::M_ERROR, sfinae_errors);
  }
  catch(...)
  {
    old_handler.set_message_count(messaget::M_ERROR, sfinae_errors);
    return nil_exprt();
  }

  // Apply the template map to default values in the function parameters,
  // so that unresolved template parameter names (e.g., Alloc()) are
  // substituted before the function type is used for disambiguation.
  if(function_type.id() == ID_code)
  {
    for(auto &param : to_code_type(function_type).parameters())
    {
      if(param.default_value().is_not_nil())
        cpp_typecheck.template_map.apply(param.default_value());
    }
  }

  // When a variadic template parameter pack (e.g., Base...) appears in a
  // function pointer parameter type like T(*)(const C*, C**, Base...),
  // the pack expansion produces an ellipsis node that gets converted to
  // a C-style ellipsis by read_function_type. After template substitution,
  // the pack is expanded to concrete types, so the ellipsis must be removed
  // from nested function pointer types.
  if(function_type.id() == ID_code)
  {
    bool has_variadic_pack = false;
    for(const auto &p : cpp_declaration.template_type().template_parameters())
    {
      if(p.get_bool(ID_ellipsis))
      {
        has_variadic_pack = true;
        break;
      }
    }

    if(has_variadic_pack)
    {
      for(auto &param : to_code_type(function_type).parameters())
      {
        if(param.type().id() == ID_pointer)
        {
          typet &base = to_pointer_type(param.type()).base_type();
          if(base.id() == ID_code)
          {
            code_typet &ct = to_code_type(base);
            if(ct.has_ellipsis())
              ct.remove_ellipsis();
          }
        }
      }
    }
  }

  // Remember that this was a template

  function_type.set(ID_C_template, template_symbol.name);
  function_type.set(ID_C_template_arguments, template_args);

  // Propagate the class tag for member templates in instantiated template
  // classes, so that instantiate_template can build the class template map.
  // Prefer the tag carried on the resolved symbol; fall back to the tag
  // derived from the member template's identifier above (which is what makes
  // a non-constructor member template -- e.g. reference_wrapper::operator() --
  // see its enclosing class's arguments at instantiation time).
  const irep_idt expr_class_tag = expr.get(ID_C_class);
  const irep_idt &class_tag =
    !expr_class_tag.empty() ? expr_class_tag : member_class_tag;
  if(!class_tag.empty())
    function_type.set(ID_C_class, class_tag);

  // Verify that the actual arguments are compatible with the deduced
  // parameter types.  Template argument deduction may succeed even when
  // the deduced types don't match (e.g., deducing T=int from the second
  // parameter of operator-(const complex<T>&, const T&) when the first
  // argument is an enum, not complex<int>).
  if(function_type.id() == ID_code && fargs.in_use)
  {
    const auto &params = to_code_type(function_type).parameters();
    auto arg_it = fargs.operands.begin();
    // N5008 [over.match.funcs]/2: the implicit object argument pairs with
    // the implicit object parameter -- skip BOTH together.  fargs.operands
    // begins with the object when has_object is set; the deduced
    // function_type of a member template may or may not carry a `this`
    // parameter yet.  Pairing the object operand against the first REAL
    // parameter (the historical off-by-one) made e.g. a member template
    // `construct(_Up*, pc_t, ...)` compare the object against `pc_t` and
    // wrongly reject the candidate as not-convertible.
    const bool has_this = !params.empty() && params.front().get_this();
    std::size_t start = has_this ? 1 : 0;
    if(fargs.has_object && arg_it != fargs.operands.end())
      ++arg_it;
    for(std::size_t i = start;
        i < params.size() && arg_it != fargs.operands.end();
        ++i, ++arg_it)
    {
      const typet &param_type = params[i].type();
      typet arg_type = arg_it->type();
      typet target = param_type;
      if(is_reference(target))
        target = to_reference_type(target).base_type();
      target.remove(ID_C_constant);
      target.remove(ID_C_volatile);
      arg_type.remove(ID_C_constant);
      arg_type.remove(ID_C_volatile);
      // If the parameter is a class/struct type and the argument is
      // not, the template is not a valid match.
      if(
        (target.id() == ID_struct_tag || target.id() == ID_struct) &&
        target != arg_type && arg_type.id() != ID_struct_tag &&
        arg_type.id() != ID_struct)
      {
        // Allow reference-to-struct to match struct_tag target
        if(
          arg_type.id() == ID_pointer &&
          (arg_type.get_bool(ID_C_reference) ||
           arg_type.get_bool(ID_C_rvalue_reference)))
        {
          // The base type of the reference should match the target
          // (this handles the case where _Compare&& deduces _Compare
          // from an lvalue reference argument)
        }
        else
        {
          // N5008 [over.match.funcs], [over.ics.user]: a non-class argument
          // may still be convertible to the struct parameter through a
          // user-defined conversion (e.g. `const char*` -> S when S has a
          // converting constructor `S(const char*)`, as in
          // report_invariant_failure's `std::string` parameters).  Only reject
          // the candidate when NO implicit conversion sequence exists; genuine
          // viability and ranking are done later by disambiguate_functions.
          // Without this, such a function template was wrongly dropped from the
          // overload set ("found no match").
          bool convertible = false;
          const std::size_t errs_before =
            old_handler.get_message_count(messaget::M_ERROR);
          try
          {
            unsigned rank = 0;
            convertible = cpp_typecheck.implicit_conversion_sequence(
              *arg_it, param_type, rank);
          }
          catch(...)
          {
            convertible = false;
          }
          old_handler.set_message_count(messaget::M_ERROR, errs_before);
          if(!convertible)
            return nil_exprt();
        }
      }
    }
  }

  // Seems we got an instance for all parameters. Let's return that.

  exprt template_function_instance(
    ID_template_function_instance, function_type);

  // N5008 [temp.variadic]/5,8: when the template-parameter-list contains
  // MORE THAN ONE parameter pack (e.g. std::pair's piecewise constructor
  // `template<class... _Args1, class... _Args2>`, or its delegation
  // target `template<class... _Args1, size_t... _Indexes1, ...>`), the
  // flat ID_C_template_arguments list recorded on the pseudo-instance
  // cannot encode how the deduced arguments split between the packs.
  // Record the deduction-time pack bindings on the instance so the final
  // instantiation (whose template_map has been restored by the nested
  // cpp_saved_template_mapt by then) can replay them.  A TYPE pack's
  // elements live in pack_args_map; a NON-TYPE pack's element VALUES live
  // in pack_expr_map -- record both, marking each entry's kind.
  {
    const auto &t_params =
      cpp_declaration.template_type().template_parameters();
    std::size_t n_packs = 0;
    for(const auto &tp : t_params)
      if(tp.get_bool(ID_ellipsis))
        ++n_packs;
    if(n_packs > 1)
    {
      irept packs("deduced_packs");
      for(const auto &tp : t_params)
      {
        if(!tp.get_bool(ID_ellipsis))
          continue;
        const irep_idt pid = tp.id() == ID_type ? tp.type().get(ID_identifier)
                                                : tp.get(ID_identifier);
        const auto pa_it = cpp_typecheck.template_map.pack_args_map.find(pid);
        const auto pe_it = cpp_typecheck.template_map.pack_expr_map.find(pid);
        irept entry(tp.id() == ID_type ? ID_type : ID_expression);
        entry.set(ID_identifier, pid);
        if(tp.id() == ID_type)
        {
          if(pa_it != cpp_typecheck.template_map.pack_args_map.end())
            for(const auto &t : pa_it->second)
              entry.get_sub().push_back(t);
        }
        else
        {
          if(pe_it != cpp_typecheck.template_map.pack_expr_map.end())
            for(const auto &v : pe_it->second)
              entry.get_sub().push_back(v);
        }
        packs.get_sub().push_back(entry);
      }
      template_function_instance.type().add("#deduced_packs") = packs;
    }
  }

  return template_function_instance;
}

void cpp_typecheck_resolvet::apply_template_args(
  exprt &expr,
  const cpp_template_args_non_tct &template_args_non_tc,
  const cpp_typecheck_fargst &fargs)
{
  if(expr.id() != ID_symbol)
    return; // templates are always symbols

  const symbolt &template_symbol =
    cpp_typecheck.lookup(to_symbol_expr(expr).identifier());

  if(!template_symbol.type.get_bool(ID_is_template))
    return;

  // Skip partial specializations — they are considered during
  // instantiation of the primary template, not during lookup.
  if(template_symbol.type.find(ID_specialization_of).is_not_nil())
  {
    expr.make_nil();
    return;
  }

#if 0
  if(template_args_non_tc.is_nil())
  {
    // no arguments, need to guess
    guess_function_template_args(expr, fargs);
    return;
  }
#endif

  // We typecheck the template arguments in the context
  // of the original scope!
  cpp_template_args_tct template_args_tc;

  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.cpp_scopes.go_to(*original_scope);

    template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, template_symbol, template_args_non_tc);
    // go back to where we used to be
  }

  // Per [temp.arg]/2: resolve template parameter references in
  // explicit template args using the enclosing template_map.
  for(auto &arg : template_args_tc.arguments())
  {
    if(
      arg.id() == ID_type &&
      arg.type().id() == ID_template_parameter_symbol_type)
    {
      cpp_typecheck.template_map.apply(arg.type());
    }
  }

  // For function templates with unassigned (partial) args, skip
  // instantiation. Store the explicit args for later deduction.
  if(template_args_tc.has_unassigned())
  {
    expr.add(ID_C_template_arguments) = template_args_tc;
    return;
  }

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration =
    to_cpp_declaration(template_symbol.type);

  // is it a class template or function template?
  if(cpp_declaration.is_class_template())
  {
    const symbolt &new_symbol = cpp_typecheck.instantiate_template(
      source_location, template_symbol, template_args_tc, template_args_tc);

    expr = type_exprt(struct_tag_typet(new_symbol.name));
    expr.add_source_location() = source_location;
  }
  else if(
    fargs.in_use && cpp_declaration.declarators().size() == 1 &&
    cpp_declaration.declarators().front().type().id() == ID_function_type &&
    !has_variadic_template_parameter(cpp_declaration.template_type()))
  {
    // [temp.inst]/2 and [over.match]: in a function-call context,
    // overload resolution uses only the signature of each candidate;
    // a specialization's definition is instantiated only when that
    // specialization is used (i.e. selected and called).  Defer
    // instantiation by storing the explicit template arguments and
    // letting guess_function_template_args form the signature; the
    // body of the *selected* overload alone is then instantiated via
    // the ID_template_function_instance path after disambiguation.
    // Eagerly instantiating every named candidate's body here turned a
    // body error in a non-selected overload (e.g. the
    // `numeric_cast_v(const mp_integer&)` overload, whose body is
    // ill-formed for Target=mp_integer) into a spurious hard error
    // during resolution of `numeric_cast_v<mp_integer>(constant_exprt)`.
    // Variadic templates are left on the eager path: their pack
    // expansion is performed by instantiate_template, not by
    // guess_function_template_args.
    expr.add(ID_C_template_arguments) = template_args_tc;
    return;
  }
  else
  {
    // function template, method template, or variable template.
    // Instantiation may fail due to SFINAE (e.g., enable_if in the
    // return type).  Suppress errors and treat failure as deduction
    // failure so that other overloads can be considered.
    // Note: we save/restore the error count instead of using a
    // null_message_handlert because the null handler changes the
    // behavior of some error-count-dependent code paths, causing
    // instantiations to fail that would otherwise succeed.
    message_handlert &old_handler = cpp_typecheck.get_message_handler();
    const std::size_t errors_before =
      old_handler.get_message_count(messaget::M_ERROR);
    const symbolt *new_sym_ptr = nullptr;
    try
    {
      const symbolt &new_symbol = cpp_typecheck.instantiate_template(
        source_location, template_symbol, template_args_tc, template_args_tc);
      new_sym_ptr = &new_symbol;
    }
    catch(...)
    {
      old_handler.set_message_count(messaget::M_ERROR, errors_before);
      expr.make_nil();
      return;
    }
    old_handler.set_message_count(messaget::M_ERROR, errors_before);
    // Per [temp.deduct]/8: if instantiation returns the template
    // symbol itself (not a code-typed specialization), treat as
    // deduction failure.
    if(
      new_sym_ptr->type.id() != ID_code &&
      new_sym_ptr->type.get_bool(ID_is_template))
    {
      expr.make_nil();
      return;
    }
    const symbolt &new_symbol = *new_sym_ptr;

    // Variable template: the type is not a function type
    if(new_symbol.type.id() != ID_code)
    {
      if(new_symbol.is_macro && new_symbol.value.is_not_nil())
        expr = new_symbol.value;
      else
        expr = symbol_exprt(new_symbol.name, new_symbol.type);
      expr.add_source_location() = source_location;
    }
    else
    {
      // check if it is a method
      const code_typet &code_type = to_code_type(new_symbol.type);

      if(
        !code_type.parameters().empty() &&
        code_type.parameters().front().get_this())
      {
        // do we have an object?
        if(fargs.has_object)
        {
          const symbolt &type_symb = cpp_typecheck.lookup(
            fargs.operands.begin()->type().get(ID_identifier));

          // [class.member.lookup]/4: name lookup uses the class
          // (or union) of the object expression.  Reject silently
          // if the resolved type symbol is neither — this can
          // happen when constexpr-eval reaches into a partially
          // instantiated body whose argument types haven't yet
          // been fully resolved.  Falling through to the
          // non-member path lets the caller surface the right
          // diagnostic at the use site.
          if(
            type_symb.type.id() != ID_struct && type_symb.type.id() != ID_union)
          {
            return;
          }

          const struct_union_typet &struct_type =
            to_struct_union_type(type_symb.type);

          // The method may be inherited from a base class template
          // (e.g., this->_Freenode() where _Freenode is in the base).
          // In that case, has_component on the derived class fails.
          // Skip the member construction and fall through to the
          // non-member (symbol) path — the call site will dispatch
          // correctly via the inherited symbol.
          if(!struct_type.has_component(new_symbol.name))
          {
            // Fall through to symbol-based dispatch
          }
          else
          {
            member_exprt member(
              *fargs.operands.begin(), new_symbol.name, code_type);
            member.add_source_location() = source_location;
            expr.swap(member);
            return;
          }
        }
      }

      expr = cpp_symbol_expr(new_symbol);
      expr.add_source_location() = source_location;
    }
  }
}

bool cpp_typecheck_resolvet::disambiguate_functions(
  const exprt &expr,
  unsigned &args_distance,
  const cpp_typecheck_fargst &fargs,
  unsigned *cv_distance)
{
  args_distance = 0;
  if(cv_distance != nullptr)
    *cv_distance = 0;

  if(!fargs.in_use)
    return true;

  // Per [over.match]/1: reject template declarations
  if(expr.type().id() != ID_code && expr.type().get_bool(ID_is_template))
    return false;

  if(expr.type().id() != ID_code)
    return true;

  const code_typet &type = to_code_type(expr.type());

  // N5008 [over.match.funcs]/1: the candidate set is built from
  // DECLARATIONS.  A symbol whose signature still contains a nil type
  // (`optionalish(? &&)`) is a half-substituted artifact left behind by a
  // failed deduction ([temp.deduct]/8 says that substitution produced NO
  // specialization); it can never be called and must not shadow or
  // ambiguate the genuine candidates re-deduced for this call.
  for(const auto &p : type.parameters())
  {
    const typet *t = &p.type();
    while((t->id() == ID_pointer || t->id() == ID_frontend_pointer) &&
          t->has_subtype())
      t = &to_type_with_subtype(*t).subtype();
    if(t->is_nil() || t->id().empty())
      return false;
  }

  // N5008 [class.copy.ctor]/2: a constructor for class X is ill-formed if its
  // first parameter is of type (optionally cv-qualified) X (passed by value)
  // and there are no other parameters or all other parameters have default
  // arguments.  Such a signature is never a usable constructor, yet it can be
  // produced by deducing a constructor template (e.g. `template<class T> X(T)`
  // with T deduced as X, giving a by-value `X(X)`).  Were it selected, copy-
  // initialising its by-value parameter would recursively construct another X
  // without bound (cf. [over.best.ics]/4 Note 2).  Exclude it from the
  // candidate set so the (non-template) copy/move constructor is used instead.
  if(type.return_type().id() == ID_constructor)
  {
    const code_typet::parameterst &ctor_params = type.parameters();
    if(
      ctor_params.size() >= 2 && ctor_params.front().get_this() &&
      ctor_params[0].type().id() == ID_pointer)
    {
      const typet &class_type =
        to_pointer_type(ctor_params[0].type()).base_type();
      const typet &p1 = ctor_params[1].type();
      if(
        p1.id() == ID_struct_tag && class_type.id() == ID_struct_tag &&
        to_struct_tag_type(p1).get_identifier() ==
          to_struct_tag_type(class_type).get_identifier())
      {
        bool rest_defaulted = true;
        for(std::size_t i = 2; i < ctor_params.size(); ++i)
        {
          if(!ctor_params[i].has_default_value())
          {
            rest_defaulted = false;
            break;
          }
        }
        if(rest_defaulted)
          return false;
      }
    }
  }

  if(expr.id() == ID_member || type.return_type().id() == ID_constructor)
  {
    // if it's a member, but does not have an object yet,
    // we add one
    if(!fargs.has_object)
    {
      const code_typet::parameterst &parameters = type.parameters();

      if(!parameters.empty() && parameters.front().get_this())
      {
        const code_typet::parametert &parameter = parameters.front();

        if(type.return_type().id() == ID_constructor)
        {
          // it's a constructor
          const typet &object_type =
            to_pointer_type(parameter.type()).base_type();
          symbol_exprt object(irep_idt(), object_type);
          object.set(ID_C_lvalue, true);

          cpp_typecheck_fargst new_fargs(fargs);
          new_fargs.add_object(object);
          return new_fargs.match(
            type, args_distance, cpp_typecheck, cv_distance);
        }
        else
        {
          if(
            expr.type().get_bool(ID_C_is_operator) &&
            fargs.operands.size() == parameters.size())
          {
            return fargs.match(type, args_distance, cpp_typecheck, cv_distance);
          }

          cpp_typecheck_fargst new_fargs(fargs);
          new_fargs.add_object(to_member_expr(expr).compound());

          return new_fargs.match(
            type, args_distance, cpp_typecheck, cv_distance);
        }
      }
      else
      {
        // Template function instance without this parameter yet;
        // match directly against the parameters.
        return fargs.match(type, args_distance, cpp_typecheck, cv_distance);
      }
    }
  }
  else if(fargs.has_object)
  {
    // If the function type already has a 'this' parameter (e.g., an
    // instantiated member function template), match directly — fargs
    // already includes the object and the type already includes 'this'.
    if(!type.parameters().empty() && type.parameters().front().get_this())
    {
      return fargs.match(type, args_distance, cpp_typecheck, cv_distance);
    }

    // For template function instances (pre-instantiation), the function
    // type doesn't include 'this' yet.  Remove the object and try to
    // match; if that fails, still accept the candidate with a high
    // distance so it can be instantiated and checked properly later.
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.remove_object();

    if(new_fargs.match(type, args_distance, cpp_typecheck, cv_distance))
      return true;

    if(expr.id() == ID_template_function_instance)
    {
      args_distance = 10000;
      return true;
    }

    return false;
  }
  else if(
    expr.id() == ID_symbol && !type.parameters().empty() &&
    type.parameters().front().get_this())
  {
    // Instantiated template member function (symbol_exprt with this
    // parameter) called without an explicit object — add a synthetic
    // this for matching purposes. This includes calls with empty
    // operand lists (e.g., variadic methods called with no args).
    const typet &object_type =
      to_pointer_type(type.parameters().front().type()).base_type();
    symbol_exprt object(irep_idt(), object_type);
    object.set(ID_C_lvalue, true);

    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.add_object(object);
    return new_fargs.match(type, args_distance, cpp_typecheck, cv_distance);
  }

  return fargs.match(type, args_distance, cpp_typecheck, cv_distance);
}

void cpp_typecheck_resolvet::filter_for_named_scopes(
  cpp_scopest::id_sett &id_set)
{
  cpp_scopest::id_sett new_set;

  // std::cout << "FILTER\n";

  // We only want scopes!
  for(const auto &id_ptr : id_set)
  {
    cpp_idt &id = *id_ptr;

    if(id.is_class() || id.is_enum() || id.is_namespace())
    {
      // std::cout << "X1\n";
      DATA_INVARIANT(id.is_scope, "should be scope");
      new_set.insert(&id);
    }
    else if(id.is_typedef())
    {
      irep_idt identifier = id.identifier;

      if(id.is_member)
      {
        // Member typedefs are stored as struct components, not as
        // standalone symbols. Look up the typedef's type through the
        // class scope and follow it to the underlying struct type.
        // The identifier for a member typedef component is the
        // class identifier + "::" + base_name, but the symbol table
        // stores it under the class tag. Look up the parent class
        // and find the component.
        const cpp_idt &parent = id.get_parent();
        const auto *class_sym =
          cpp_typecheck.symbol_table.lookup(parent.identifier);
        if(class_sym != nullptr && class_sym->type.id() == ID_struct)
        {
          // N5008 [class.member.lookup]/[basic.scope.hiding]: a member
          // declared in the class itself hides an inherited member of the
          // same name.  The flattened component list may hold both this
          // class's own member typedef (the one the looked-up id denotes,
          // whose component name equals id.identifier and which is not
          // from_base) and same-named inherited (from_base) typedefs from
          // different base classes that resolve to unrelated types.  Pick the
          // class's own member -- preferring an exact component-name match for
          // the looked-up id, then any non-from_base member -- so a qualified
          // name (e.g. a recursively-defined `typedef ... _Base`) resolves to
          // the derived class's typedef rather than a base's.
          const struct_typet::componentt *chosen = nullptr;
          for(const auto &comp : to_struct_type(class_sym->type).components())
          {
            if(!(comp.get_base_name() == id.base_name &&
                 comp.get_bool(ID_is_type)))
              continue;
            if(comp.get_name() == id.identifier)
            {
              chosen = &comp;
              break;
            }
            if(
              chosen == nullptr ||
              (chosen->get_bool(ID_from_base) && !comp.get_bool(ID_from_base)))
              chosen = &comp;
          }
          if(chosen != nullptr)
          {
            const typet &t = chosen->type();
            if(t.id() == ID_struct_tag)
            {
              const irep_idt &tag_id = to_struct_tag_type(t).get_identifier();
              auto it = cpp_typecheck.cpp_scopes.id_map.find(tag_id);
              if(it != cpp_typecheck.cpp_scopes.id_map.end())
              {
                cpp_idt &class_id = *it->second;
                if(class_id.is_scope)
                  new_set.insert(&class_id);
              }
            }
          }
        }
        continue;
      }

      while(true)
      {
        if(identifier.empty())
          break;
        const symbolt &symbol = cpp_typecheck.lookup(identifier);
        CHECK_RETURN(symbol.is_type);

        // todo? maybe do enum here, too?
        if(symbol.type.id() == ID_struct)
        {
          // this is a scope, too!
          cpp_idt &class_id = cpp_typecheck.cpp_scopes.get_id(identifier);

          DATA_INVARIANT(class_id.is_scope, "should be scope");
          new_set.insert(&class_id);
          break;
        }
        else if(symbol.type.id() == ID_struct_tag)
        {
          const irep_idt &tag_id =
            to_struct_tag_type(symbol.type).get_identifier();
          auto it = cpp_typecheck.cpp_scopes.id_map.find(tag_id);
          if(it != cpp_typecheck.cpp_scopes.id_map.end())
          {
            cpp_idt &class_id = *it->second;
            if(class_id.is_scope)
              new_set.insert(&class_id);
          }
          break;
        }
        else if(symbol.type.id() == ID_c_enum_tag)
        {
          const irep_idt &tag_id =
            to_c_enum_tag_type(symbol.type).get_identifier();
          auto it = cpp_typecheck.cpp_scopes.id_map.find(tag_id);
          if(it != cpp_typecheck.cpp_scopes.id_map.end())
          {
            cpp_idt &class_id = *it->second;
            if(class_id.is_scope)
              new_set.insert(&class_id);
          }
          break;
        }
        else
          break;
      }
    }
    else if(id.id_class == cpp_scopet::id_classt::TEMPLATE)
    {
// std::cout << "X3\n";
#if 0
      const symbolt &symbol=
        cpp_typecheck.lookup(id.identifier);

      // Template struct? Really needs arguments to be a scope!
      if(symbol.type.id() == ID_struct)
      {
        id.print(std::cout);
        assert(id.is_scope);
        new_set.insert(&id);
      }
#endif
    }
    else if(id.id_class == cpp_scopet::id_classt::TEMPLATE_PARAMETER)
    {
      // std::cout << "X4\n";
      // a template parameter may evaluate to be a scope: it could
      // be instantiated with a class/struct/union/enum
      exprt e = cpp_typecheck.template_map.lookup(id.identifier);

#if 0
      cpp_typecheck.template_map.print(std::cout);
      std::cout << "S: " << cpp_typecheck.cpp_scopes.current_scope().identifier
                << '\n';
      std::cout << "P: "
                << cpp_typecheck.cpp_scopes.current_scope().get_parent()
                << '\n';
      std::cout << "I: " << id.identifier << '\n';
      std::cout << "E: " << e.pretty() << '\n';
#endif

      if(e.id() != ID_type)
        continue; // expressions are definitively not a scope

      if(e.type().id() == ID_template_parameter_symbol_type)
      {
        auto type = to_template_parameter_symbol_type(e.type());

        while(true)
        {
          irep_idt identifier = type.get_identifier();
          if(identifier.empty())
            break;

          const symbolt &symbol = cpp_typecheck.lookup(identifier);
          CHECK_RETURN(symbol.is_type);

          if(symbol.type.id() == ID_template_parameter_symbol_type)
            type = to_template_parameter_symbol_type(symbol.type);
          else if(
            symbol.type.id() == ID_struct || symbol.type.id() == ID_union ||
            symbol.type.id() == ID_c_enum)
          {
            // this is a scope, too!
            cpp_idt &class_id = cpp_typecheck.cpp_scopes.get_id(identifier);

            DATA_INVARIANT(class_id.is_scope, "should be scope");
            new_set.insert(&class_id);
            break;
          }
          else // give up
            break;
        }
      }
    }
  }

  id_set.swap(new_set);
}

void cpp_typecheck_resolvet::filter_for_namespaces(cpp_scopest::id_sett &id_set)
{
  // we only want namespaces
  for(cpp_scopest::id_sett::iterator it = id_set.begin();
      it != id_set.end();) // no it++
  {
    if((*it)->is_namespace())
      it++;
    else
    {
      cpp_scopest::id_sett::iterator old(it);
      it++;
      id_set.erase(old);
    }
  }
}

void cpp_typecheck_resolvet::resolve_with_arguments(
  cpp_scopest::id_sett &id_set,
  const irep_idt &base_name,
  const cpp_typecheck_fargst &fargs)
{
  // Argument-dependent lookup (ADL / Koenig lookup):
  // Search in the namespaces associated with the argument types.

  // Collect the candidates contributed by ONE associated class type:
  // its own scope (friend declarations) and its enclosing namespaces.
  // N5008 [basic.lookup.argdep]/2: for a class template
  // SPECIALIZATION, the associated entities also include those of its
  // template TYPE arguments -- e.g. the unqualified `transform(it, ...)`
  // over __gnu_cxx::__normal_iterator<char *, std::basic_string<...>>
  // finds std::transform only through the basic_string argument.
  // Recurse over the recorded template arguments (visited-set bounded).
  std::set<irep_idt> visited;
  std::function<void(const typet &)> add_associated_class =
    [&](const typet &type)
  {
    typet arg_type = type;
    if(is_reference(arg_type))
      arg_type = to_reference_type(arg_type).base_type();

    if(arg_type.id() != ID_struct_tag && arg_type.id() != ID_union_tag)
      return;

    const struct_union_typet &final_type =
      arg_type.id() == ID_struct_tag
        ? static_cast<const struct_union_typet &>(
            cpp_typecheck.follow_tag(to_struct_tag_type(arg_type)))
        : static_cast<const struct_union_typet &>(
            cpp_typecheck.follow_tag(to_union_tag_type(arg_type)));

    // Search in the struct's own scope (for friend declarations)
    const irep_idt &struct_name = final_type.get(ID_name);
    if(struct_name.empty() || !visited.insert(struct_name).second)
      return;

    // [basic.lookup.argdep]/2: template type arguments of a class
    // template specialization contribute their associated entities.
    const symbolt *class_symbol =
      cpp_typecheck.symbol_table.lookup(struct_name);
    if(class_symbol != nullptr)
    {
      const irept &template_args =
        class_symbol->type.find(ID_C_template_arguments);
      if(template_args.is_not_nil())
      {
        for(const auto &targ :
            static_cast<const cpp_template_args_tct &>(template_args)
              .arguments())
        {
          if(targ.id() == ID_type)
            add_associated_class(targ.type());
        }
      }
    }

    auto scope_it = cpp_typecheck.cpp_scopes.id_map.find(struct_name);
    if(scope_it == cpp_typecheck.cpp_scopes.id_map.end())
      return;
    cpp_scopet &scope = static_cast<cpp_scopet &>(*scope_it->second);
    auto tmp_set = scope.lookup(base_name, cpp_scopet::SCOPE_ONLY);
    id_set.insert(tmp_set.begin(), tmp_set.end());

    // Search all enclosing namespaces (proper ADL, including
    // inline namespaces like std::__cxx11) AND the root namespace.
    //
    // [basic.lookup.argdep]/2 says the associated namespaces of a
    // class type include the namespace of which the class is a
    // member.  For a class declared at global scope (e.g.,
    // `struct BigInt { ... };` in `bigint.hh`), that namespace is
    // the root namespace.  An earlier termination at
    // `is_root_scope()` would skip the root namespace, so a free
    // operator declared at global scope (e.g.,
    // `bool operator<(const BigInt &, const BigInt &)`) would not
    // participate in ADL when an unqualified-but-shadowed lookup
    // (e.g., inside the body of an unrelated `operator<` member
    // function) failed to locate it via the regular scope walk.
    for(cpp_scopet *ns = &scope; ns != nullptr; ns = &ns->get_parent())
    {
      if(ns->is_namespace() || ns->is_root_scope())
      {
        tmp_set = ns->lookup(base_name, cpp_scopet::SCOPE_ONLY);
        id_set.insert(tmp_set.begin(), tmp_set.end());
      }
      if(ns->is_root_scope())
        break;
    }
  };

  for(const auto &arg : fargs.operands)
  {
    // N5008 [basic.lookup.argdep]/2: if an argument is a reference, its
    // associated types are those of the referenced type.  CBMC models a
    // reference as a pointer carrying #reference (as produced by e.g.
    // `static_cast<std::ostream &>(x)`), so strip a leading reference to reach
    // the class type; otherwise the class's associated namespace is missed and
    // an ADL-only operator@ (one hidden from ordinary lookup by an in-scope
    // member operator@ of the same name) is never found.
    add_associated_class(arg.type());
  }
}
