/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/// \file
/// C++ Language Type Checking

#include "cpp_typecheck_resolve.h"

#include <deque>
#include <unordered_map>

#ifdef DEBUG
#  include <iostream>
#endif

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/simplify_expr.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/symbol_table_base.h>

#include <ansi-c/anonymous_member.h>
#include <ansi-c/c_qualifiers.h>
#include <ansi-c/merged_type.h>

#include "cpp_constexpr_eval.h"
#include "cpp_convert_type.h"
#include "cpp_sfinae_context.h"
#include "cpp_template_parameter.h"
#include "cpp_template_qualifiers.h"
#include "cpp_type2name.h"
#include "cpp_typecheck.h"
#include "cpp_typecheck_fargs.h"
#include "cpp_util.h"

#include <algorithm>
#include <limits>
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

  // N5008 [temp.over.link]/6-7, [over.match.funcs.general]/7: function
  // templates whose template-heads differ (for instance only in the
  // enable_if condition of a defaulted constant template parameter) are
  // distinct overloads.  The second such template is kept as the
  // `#sfinae_alt' of the first (typecheck_function_template); when the
  // explicit arguments fail to substitute into the first, the alternative
  // is a candidate of its own.
  const auto sfinae_alternative =
    [this](const exprt &primary) -> std::optional<exprt>
  {
    if(primary.id() != ID_symbol)
      return {};
    const irep_idt &name = to_symbol_expr(primary).get_identifier();
    const auto alt_it = cpp_typecheck.sfinae_alternatives.find(name);
    if(alt_it == cpp_typecheck.sfinae_alternatives.end())
      return {};
    const irep_idt alt_name = id2string(name) + "#sfinae_alt";
    if(!cpp_typecheck.symbol_table.has_symbol(alt_name))
      cpp_typecheck.symbol_table.insert(alt_it->second);
    exprt alt = primary;
    alt.type() = alt_it->second.type;
    to_symbol_expr(alt).set_identifier(alt_name);
    return alt;
  };

  for(std::size_t i = 0; i < old_identifiers.size(); ++i)
  {
    const exprt old_id = old_identifiers[i];
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
      if(auto alt = sfinae_alternative(old_id))
        old_identifiers.push_back(*alt);
      continue;
    }
    catch(int)
    {
      if(auto alt = sfinae_alternative(old_id))
        old_identifiers.push_back(*alt);
      // N5008 [temp.deduct.general]/5 + [temp.deduct]/8: substituting the
      // explicit template arguments -- and the DEFAULT arguments of the
      // parameters they leave out -- into this candidate failed (a silent
      // `throw 0' from the resolver, e.g. no viable function for the call in
      // a constrained default `class = decltype(test_aux<To1>(declval<
      // From1>()))').  That removes this candidate only; the sibling
      // `template<class, class> test(...)' of libstdc++ 11's
      // __is_convertible_helper must still be tried.  Before, the failure
      // escaped the class body being instantiated (is_convertible<const
      // unsigned&, string_view> in basic_string's _If_sv constraint) and
      // `std::string{string_view}' had no viable constructor with the 11
      // headers.
      continue;
    }

    if(e.is_not_nil())
    {
      CHECK_RETURN(e.id() != ID_type || e.type().is_not_nil());

      identifiers.push_back(e);
    }
    else if(auto alt = sfinae_alternative(old_id))
      old_identifiers.push_back(*alt);
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

// Save/restore for cpp_typecheck_resolvet::current_deduction_nontype_types
struct deduction_nontype_types_guardt
{
  std::map<irep_idt, typet> &target;
  std::map<irep_idt, typet> saved;
  explicit deduction_nontype_types_guardt(std::map<irep_idt, typet> &t)
    : target(t), saved(t)
  {
  }
  ~deduction_nontype_types_guardt()
  {
    target.swap(saved);
  }
};

// The declared types of a template declaration's NON-type parameters
// ([temp.deduct.type]/17), keyed by identifier.
static std::map<irep_idt, typet>
template_nontype_parameter_types(const template_typet &template_type)
{
  std::map<irep_idt, typet> types;
  for(const auto &p : template_type.template_parameters())
  {
    if(p.id() != ID_type && !p.get(ID_identifier).empty())
      types[p.get(ID_identifier)] = p.type();
  }
  return types;
}

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

// A concept template symbol with a constraint-expression body.
static bool is_concept_with_body(const symbolt &symbol, const irep_idt &name)
{
  if(
    symbol.base_name != name || !symbol.type.get_bool(ID_is_template) ||
    symbol.type.id() != ID_cpp_declaration)
    return false;
  const cpp_declarationt &decl = to_cpp_declaration(symbol.type);
  return !decl.declarators().empty() &&
         decl.declarators().front().value().is_not_nil();
}

// Look up a concept's constraint-expression body by its base name.
exprt concept_constraint_body(
  const symbol_table_baset &symbol_table,
  const irep_idt &name)
{
  // Constraint ordering ([temp.constr.order]) normalises the concepts of
  // every constrained candidate on every overload resolution, and each
  // concept-id looked up here used to cost a scan of the whole symbol table
  // (12% of the run for a libc++ <span> program).  Remember which symbol a
  // base name resolved to; the entry is validated against the table before
  // use, so a stale entry (another translation unit in the same process)
  // just falls back to the scan.
  // A name that is NOT a concept (a raw atomic constraint keyed by its text,
  // a type trait) is remembered with the table's size at the time: as long
  // as nothing was declared since, the scan would find nothing again.
  struct cache_entryt
  {
    irep_idt symbol_name;   // empty for a miss
    std::size_t table_size; // for a miss
  };
  static std::unordered_map<irep_idt, cache_entryt> concept_symbol_by_name;

  const auto cached = concept_symbol_by_name.find(name);
  if(cached != concept_symbol_by_name.end())
  {
    if(cached->second.symbol_name.empty())
    {
      if(cached->second.table_size == symbol_table.symbols.size())
        return nil_exprt();
    }
    else
    {
      const symbolt *symbol = symbol_table.lookup(cached->second.symbol_name);
      if(symbol != nullptr && is_concept_with_body(*symbol, name))
        return to_cpp_declaration(symbol->type).declarators().front().value();
    }
  }

  for(const auto &entry : symbol_table.symbols)
  {
    if(is_concept_with_body(entry.second, name))
    {
      concept_symbol_by_name[name] = {entry.first, 0};
      return to_cpp_declaration(entry.second.type)
        .declarators()
        .front()
        .value();
    }
  }
  concept_symbol_by_name[name] = {irep_idt{}, symbol_table.symbols.size()};
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

/// The instantiation step of function template overload resolution
/// ([temp.deduct]/1, [temp.inst]/4): when a single candidate remains and it
/// is a deduced specialization (`template_function_instance'), instantiate
/// it -- explicit template arguments merged with the deduced ones, the
/// trailing return type substituted -- and replace the candidate by the
/// instance's symbol.
void cpp_typecheck_resolvet::instantiate_selected_function_template(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
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
      // N5008 [temp.inst]/1: the member template is instantiated in the
      // context of its class instance -- the class's parameters bound to
      // the instance's arguments, including a partial specialization's
      // packs (`_ArgTypes...' of function<int(int, int)>, named by the
      // constructor template's default argument `__invoke_result<_DFunc&,
      // _ArgTypes...>'; unbound, the pack expanded to one element and
      // std::function's converting constructor found no match).
      // bind_class_instance_parameters replays the deduction-time pack
      // bindings recorded on the instance, so a partial specialization's
      // packs are not paired positionally with the primary's arguments.
      if(class_sym != nullptr)
        cpp_typecheck.bind_class_instance_parameters(
          *class_sym, cpp_typecheck.template_map);
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
          cpp_typecheck.template_map.set_pack_size(pid, vals.size());
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
        cpp_typecheck.template_map.set_pack_size(pid, elems.size());
        cpp_typecheck.template_map.pack_args_map[pid] = elems;
        if(!elems.empty())
          cpp_typecheck.template_map.type_map[pid] = elems.front();
      }

      // N5008 [temp.point]/1 + [basic.scope.temp]/2: while THIS
      // specialization is instantiated, only its own parameters (plus
      // the enclosing class-template arguments bound above) may be
      // substituted.  The flat template map still holds a sibling or
      // enclosing instantiation's entries, and the short-name bridge in
      // apply() can pick either when both spell the same parameter --
      // for two instantiations of the SAME template (tuple<tuple<int>>
      // containing tuple<int>, whose `_Tf`/`_Up` keys differ only by
      // the instance prefix) no scope-distance rule can separate them.
      // Hide the foreign same-short-name entries for the duration of
      // this instantiation, exactly as build()'s shadow-removal loop
      // does for the class-parameter case.  (The saved_map above
      // restores them on the way out.)
      if(!packs.get_sub().empty())
      {
        const auto short_of = [](const irep_idt &id) -> std::string
        {
          const std::string s2 = id2string(id);
          const auto p2 = s2.rfind("::");
          return p2 != std::string::npos ? s2.substr(p2 + 2) : s2;
        };
        std::set<irep_idt> own_ids;
        std::set<std::string> own_shorts;
        for(const auto &entry : packs.get_sub())
        {
          const irep_idt pid = entry.get(ID_identifier);
          if(pid.empty())
            continue;
          own_ids.insert(pid);
          own_shorts.insert(short_of(pid));
        }
        const auto shadow = [&](auto &m)
        {
          for(auto it = m.begin(); it != m.end();)
          {
            if(
              own_ids.count(it->first) == 0 &&
              own_shorts.count(short_of(it->first)) != 0)
              it = m.erase(it);
            else
              ++it;
          }
        };
        shadow(cpp_typecheck.template_map.type_map);
        shadow(cpp_typecheck.template_map.expr_map);
        shadow(cpp_typecheck.template_map.pack_args_map);
        shadow(cpp_typecheck.template_map.pack_expr_map);
        shadow(cpp_typecheck.template_map.pack_size_map);
        // ... and make this specialization's parameters the innermost
        // active scope for the substitution of its signature (the enclosing
        // instantiation's same-named parameters stay on the stack below).
        cpp_typecheck.template_map.parameter_scopes.emplace_back(
          own_ids.begin(), own_ids.end());
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
        // parameter `R` in `template<class R, class F, class... A> R f(F,
        // A&&...)`
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

/// guess arguments of function templates
void cpp_typecheck_resolvet::guess_function_template_args(
  resolve_identifierst &identifiers,
  const cpp_typecheck_fargst &fargs)
{
  resolve_identifierst old_identifiers;
  old_identifiers.swap(identifiers);

  resolve_identifierst non_templates;

  // N5008 [over.match.best]/2.5, [temp.func.order]/8.4: constraints order
  // only VIABLE candidates (after deduction and the constraint check) with
  // equivalent function parameter lists; that is done by the
  // same-signature subsumption filter after deduction.  Dropping a
  // less-constrained candidate here, before deduction, removed
  // `template <C1 T> f(T)' when the more constrained `template <CC T>
  // f(T)' turned out not viable (f(1.0) with CC = C1 && is_same<T, int>),
  // and removed `template <C1 I> f(I)' in favour of an unrelated
  // `template <CC R> f()' (libstdc++'s ranges::copy iterator overload).

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

      // N5008 [temp.param]/4: a type-constraint on a template parameter
      // (`template<Integral T>') introduces the constraint-expression
      // `Integral<T>' into the template's associated constraints; the
      // typechecker conjoins it into the requires-clause
      // (add_type_constraint), so the requires-clause evaluation below
      // decides it.  A structural evaluator of the concept body over the
      // first argument's type used to live here (a whole symbol-table scan
      // per candidate); it understood only builtin traits and could not
      // tell `Integral<double>' false -- `template<Integral T> g' and
      // `template<Floating T> g' resolved to whichever was declared first.

      // [temp.deduct]/5 with [temp.constr.decl]/1: after deducing this
      // function-template specialization, its associated constraints (the
      // requires-clause, including the type-constraints folded into it) must
      // be satisfied by the deduced arguments; otherwise the candidate is
      // removed.  Without this, e.g. a constrained
      // templated constructor `C(T) requires integral<T>` would wrongly be
      // viable with T deduced as a class type, yielding a bogus by-value
      // `C(C)` whose argument materialisation re-invokes the same
      // construction without bound (cf. libstdc++ __max_size_type /
      // __max_diff_type).
      bool requires_ok = true;
      if(
        e.id() == ID_template_function_instance &&
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
          // N5008 [temp.param]/4 + [temp.constr.decl]/3: the type-constraints
          // of the template parameters (`template<Integral T>' introduces
          // `Integral<T>', recorded by add_type_constraint) are part of the
          // associated constraints, conjoined with the requires-clause.
          for(const auto &p : tdecl.template_type().template_parameters())
          {
            const irept &tc = p.find("#C_type_constraint");
            if(tc.is_nil())
              continue;
            if(req_clause.is_nil() || req_clause.id() == ID_nil)
              req_clause = static_cast<const exprt &>(tc);
            else
            {
              exprt conj(ID_and);
              conj.add_to_operands(
                std::move(req_clause), exprt{static_cast<const exprt &>(tc)});
              req_clause = std::move(conj);
            }
          }
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
              // N5008 [temp.constr.decl]/3 + [temp.constr.atomic]/1: the
              // associated constraints are checked with the PARAMETER
              // MAPPING of the constrained declaration: the member
              // template's own parameters bound to the deduced arguments
              // and, for a constrained member of a class template
              // specialization, the class's parameters bound to the
              // instance's arguments (libstdc++ C++20 pair<T1,T2>'s
              // converting constructor requires
              // _S_constructible<...>() over T1/T2).  Install exactly
              // that mapping in the template map (packs included, so
              // `Args...` expands to the deduced arity and
              // `sizeof...(Args)` counts it -- [temp.variadic]/5) and
              // type-check the clause as written, in the template's own
              // scope; the parameter names then resolve as in any
              // instantiated body.  This replaced a by-name textual
              // substitution that covered type parameters only.
              const cpp_template_args_tct &targs =
                to_cpp_template_args_tc(e.type().find(ID_C_template_arguments));
              cpp_saved_template_mapt clause_saved_map{
                cpp_typecheck.template_map};
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
                    // the class's bindings first: the member's parameters
                    // shadow them ([temp.local])
                    cpp_typecheck.template_map.build(
                      static_cast<const template_typet &>(
                        class_sym->type.find(ID_C_template)),
                      to_cpp_template_args_tc(
                        class_sym->type.find(ID_C_template_arguments)));
                  }
                }
              }
              cpp_typecheck.template_map.build(tdecl.template_type(), targs);
              exprt req_copy = req_clause;
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
              // N5008 [temp.constr.decl]/1, [temp.res.general]/1: the
              // requires-clause is part of the template's declaration, so
              // the names in it are looked up from the template's own scope
              // (its parent is the declaring class or namespace), not from
              // the call site.  A hidden friend such as
              // _RangeAdaptorClosure's `template<typename _Self, typename
              // _Range> requires derived_from<remove_cvref_t<_Self>,
              // _RangeAdaptorClosure> && ... operator|(_Range&&, _Self&&)`
              // names its class unqualified; looked up from main() that
              // failed and the candidate was mis-handled downstream
              // (`arr | views::take(3)` died converting the array to the
              // closure type).
              {
                const auto scope_it =
                  cpp_typecheck.cpp_scopes.id_map.find(tsym->name);
                if(
                  scope_it != cpp_typecheck.cpp_scopes.id_map.end() &&
                  scope_it->second != nullptr)
                {
                  cpp_typecheck.cpp_scopes.go_to(
                    *static_cast<cpp_scopet *>(scope_it->second));
                }
              }
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
                  if(cpp_typecheck.bind_requires_parameter_pack(pname, ptype))
                    continue;
                  try
                  {
                    cpp_typecheck.typecheck_type(ptype);
                  }
                  catch(...)
                  {
                  }
                  cpp_typecheck.bind_requires_parameter(pname, ptype);
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
                      // N5008 [temp.constr.atomic]/1: the atom is
                      // evaluated with the parameter mapping of the
                      // constrained declaration.  The by-name rewrite
                      // above only reaches parameters spelled in the
                      // CLAUSE ITSELF; a member named in the atom may
                      // have defaults referring to the enclosing
                      // class's parameters in ITS OWN declaration
                      // (gcc-16 <optional>:
                      // `template <typename, typename = remove_cv_t
                      // <_Tp>> static constexpr bool
                      // __not_constructing_bool_from_optional`, named
                      // by the converting constructor's
                      // requires-clause).  Resolving that default
                      // needs the bindings in the TEMPLATE MAP, so
                      // install them for the duration of the atom's
                      // typecheck; a throw here previously read as
                      // "constraint unsatisfied" and silently removed
                      // the candidate.
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

      if(requires_ok)
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
    // N5008 [temp.inst]/1 + [over.match.funcs]: a function template
    // specialization is ONE candidate.  The class scope lists every
    // already-materialised specialization as a plain symbol next to the
    // template itself, so once a member template has been instantiated
    // for some arguments, the same specialization enters the set twice:
    // as the deduction placeholder (template_function_instance) and as
    // the existing symbol.  Left alone the pair tied on every key and
    // made the call ambiguous ("found no match" after the fallbacks) --
    // or, ranked differently, made the winner depend on whether the
    // specialization had been instantiated earlier (candidate order):
    // libstdc++'s `shared_ptr<const _NFA>(shared_ptr<_NFA>&&)` lost its
    // body that way.  Drop the symbol when its placeholder is present.
    std::set<irep_idt> materialised;
    for(const auto &inst : identifiers)
    {
      if(inst.id() != ID_template_function_instance)
        continue;
      const irep_idt tmpl_name = inst.type().get(ID_C_template);
      if(tmpl_name.empty())
        continue;
      const symbolt *tmpl_sym = cpp_typecheck.symbol_table.lookup(tmpl_name);
      if(tmpl_sym == nullptr)
        continue;
      const irep_idt existing =
        cpp_typecheck.existing_function_template_instance(
          *tmpl_sym,
          static_cast<const cpp_template_args_tct &>(
            inst.type().find(ID_C_template_arguments)));
      if(!existing.empty())
        materialised.insert(existing);
    }
    for(auto &nt : non_templates)
    {
      if(
        nt.id() == ID_symbol &&
        materialised.count(to_symbol_expr(nt).get_identifier()) != 0)
        continue;
      identifiers.push_back(std::move(nt));
    }
  }

  // N5008 [over.match.best]/2.5 + [temp.func.order]/8.4: of two VIABLE
  // function template specializations whose templates have equivalent
  // function parameter lists, the one whose template is more
  // constrained ([temp.constr.order]/1, on the normal forms --
  // template_constraint_strictly_subsumes; `Cheap' is preferred over
  // `Cheap || Rare') is better.  Applied after deduction and the
  // constraint check: before them, `template <C1 T> f(T)' was dropped
  // for `template <CC T> f(T)' (CC = C1 && is_same<T, int>) even when
  // the latter was not viable, as for f(1.0).
  if(identifiers.size() > 1)
  {
    auto candidate_decl = [&](const exprt &id) -> const cpp_declarationt *
    {
      // after deduction: the instance records its function template
      const irep_idt sym_id = id.type().get(ID_C_template);
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
    decls.reserve(identifiers.size());
    cstr.reserve(identifiers.size());
    for(const auto &id : identifiers)
    {
      const cpp_declarationt *d = candidate_decl(id);
      // Only consider constrained templates, so an unconstrained or
      // non-template candidate is never dropped here (it is ordered by the
      // normal best-match/partial-ordering rules instead).
      const bool constrained = d != nullptr && template_is_constrained(*d);
      decls.push_back(constrained ? d : nullptr);
      cstr.push_back(constrained ? constraint_name_string(*d) : std::string{});
    }

    std::vector<bool> subsumed(identifiers.size(), false);
    for(std::size_t i = 0; i < decls.size(); ++i)
    {
      if(decls[i] == nullptr || decls[i]->declarators().empty())
        continue;
      for(std::size_t j = 0; j < decls.size(); ++j)
      {
        if(i == j || decls[j] == nullptr || decls[j]->declarators().empty())
          continue;
        // Constraint subsumption only breaks ties between viable
        // candidates that are otherwise equivalent ([over.match.best]/2.5,
        // [temp.func.order]/8.2.2, 8.4).  Restrict the
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
    auto it = identifiers.begin();
    for(std::size_t i = 0; i < identifiers.size(); ++i, ++it)
      if(!subsumed[i])
        filtered.push_back(*it);
    if(!filtered.empty() && filtered.size() < identifiers.size())
      identifiers = filtered;
  }

  disambiguate_functions(identifiers, fargs);

  // there should only be one left, or we have failed to disambiguate
  instantiate_selected_function_template(identifiers, fargs);
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

  // An ID_unassigned placeholder (from build_unassigned) marks a
  // parameter of an ACTIVE deduction with no binding yet; downstream
  // SFINAE probes rely on it surviving signature type-checking (the
  // std::pair is_constructible and libstdc++ list shapes), so it is
  // RETURNED, not treated as unbound.  But its type is the parameter's
  // UNCHECKED declared type (e.g. a raw `long`); type-check it here so a
  // scalar use in arithmetic (`_Ep - _Sp` in __make_tuple_indices under
  // libc++ __perfect_forward) does not abort with "invalid implicit
  // conversion from '<<type:long>>'" -- the expression then simply fails
  // to fold to a constant and the caller's dependent-count recovery
  // applies.
  if(
    e.id() == ID_unassigned && e.type().is_not_nil() &&
    !e.type().id().empty() && e.type().id() != ID_unassigned)
  {
    const std::size_t errors_before =
      cpp_typecheck.get_message_handler().get_message_count(messaget::M_ERROR);
    try
    {
      cpp_typecheck.typecheck_type(e.type());
    }
    catch(...)
    {
      cpp_typecheck.get_message_handler().set_message_count(
        messaget::M_ERROR, errors_before);
    }
  }

  // The pack fallbacks below also apply when the entry is an
  // ID_unassigned placeholder: build_unassigned seeds EVERY parameter,
  // pack or not, but a pack's actual binding lives in
  // pack_args_map/pack_expr_map/pack_size_map, which take precedence
  // over the placeholder ([temp.variadic]/5,7).  Non-pack placeholders
  // (no pack-map entries) still fall through to the survival return.
  if(
    e.is_nil() || (e.id() == ID_type && e.type().is_nil()) ||
    e.id() == ID_unassigned)
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
    // ... and the NON-TYPE analogue ([temp.variadic]/5 likewise): a
    // scalar reference to a multi-element VALUE pack (its elements in
    // pack_expr_map) resolves to the representative first element; the
    // per-element lockstep expansion (e.g. `__type_pack_element<_Idx,
    // _Types...>` inside libc++'s __make_tuple_types_flat member alias)
    // is applied afterwards by the expansion machinery.  Without this
    // the reference fell through to an unrelated lookup and failed with
    // "symbol '_Idx' does not uniquely resolve".
    const auto pe_it =
      cpp_typecheck.template_map.pack_expr_map.find(identifier.identifier);
    if(
      pe_it != cpp_typecheck.template_map.pack_expr_map.end() &&
      !pe_it->second.empty())
    {
      exprt pack_front = pe_it->second.front();
      pack_front.add_source_location() = source_location;
      return pack_front;
    }
  }

  if(
    e.is_nil() || (e.id() == ID_type && e.type().is_nil()) ||
    e.id() == ID_unassigned)
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
    // A non-pack ID_unassigned placeholder survives (see above); only
    // genuinely unbound (nil) entries are an error here.
    if(e.id() == ID_unassigned)
    {
      e.add_source_location() = source_location;
      return e;
    }
    // Don't print an error message — the caller may catch the exception
    // (e.g., during SFINAE or template argument deduction).
    throw 0;
  }

  // N5008 [temp.variadic]/7: a scalar reference to a pack that is
  // KNOWN-EMPTY in this instantiation must yield the zero-length-pack
  // sentinel even when the parameter also carries an ID_unassigned
  // placeholder (build_unassigned seeds every parameter; the pack's
  // emptiness is recorded separately in pack_size_map).  Returning the
  // placeholder instead sent `(unsigned long)?` into a non-type
  // template argument and the enclosing instantiation failed with
  // "expected constant expression" -- the `__tuple_indices<_Values...>`
  // member alias of __make_integer_seq's pack template, instantiated
  // for a zero-length range (__make_tuple_types<tuple, 2, 2> in libc++
  // tuple's delegating constructor).  Placeholders for parameters
  // WITHOUT a pack_size_map entry keep their survival contract (see
  // the round-41 note above).
  e.add_source_location() = source_location;

  return e;
}

exprt cpp_typecheck_resolvet::object_of_naming_class(
  const exprt &object,
  const cpp_idt &identifier,
  const source_locationt &source_location)
{
  // N5008 [class.access.base]/6: a class member access (also an implicit
  // `this->') to a non-static member requires the object expression to be
  // implicitly convertible to (a pointer to) the NAMING class -- the class
  // in whose scope the search found the member ([class.access.base]/5; the
  // nested-name-specifier's class for `E1.N::m', the object's class
  // otherwise) -- and the member is that of the naming class subobject.
  // [expr.ref]/8: it is ill-formed if the class of which the member is
  // directly a member is an ambiguous base of the naming class.  Both matter
  // only when a base class occurs more than once in the lattice
  // ([class.mi]/4-5: `d.B::i' and `d.C::i' name the i of different A
  // subobjects, `d.i' is ill-formed).
  if(object.type().id() != ID_struct_tag)
    return object;
  const irep_idt object_class =
    to_struct_tag_type(object.type()).get_identifier();
  const cpp_scopet &search_scope = cpp_typecheck.cpp_scopes.current_scope();
  const irep_idt naming_class =
    search_scope.is_class() ? search_scope.identifier : object_class;
  const symbolt *naming_symbol =
    cpp_typecheck.symbol_table.lookup(naming_class);
  const symbolt *object_symbol =
    cpp_typecheck.symbol_table.lookup(object_class);
  if(
    naming_symbol == nullptr || naming_symbol->type.id() != ID_struct ||
    object_symbol == nullptr || object_symbol->type.id() != ID_struct)
  {
    return object;
  }
  const struct_typet &naming_struct = to_struct_type(naming_symbol->type);

  if(
    identifier.class_identifier != naming_class &&
    cpp_typecheck.base_subobjects(naming_struct, identifier.class_identifier)
        .size() > 1)
  {
    cpp_typecheck.error().source_location = source_location;
    cpp_typecheck.error()
      << "member '" << identifier.base_name << "' of the ambiguous base class '"
      << cpp_typecheck.lookup(identifier.class_identifier).pretty_name
      << "' of '" << naming_symbol->pretty_name << "'" << messaget::eom;
    throw 0;
  }

  if(
    naming_class == object_class ||
    !cpp_typecheck.subtype_typecast(
      to_struct_type(object_symbol->type), naming_struct))
  {
    return object;
  }

  // the naming class subobject of the object
  exprt address = object.id() == ID_dereference
                    ? to_dereference_expr(object).pointer()
                    : exprt{address_of_exprt{object}};
  pointer_typet naming_pointer = pointer_type(struct_tag_typet{naming_class});
  if(object.type().get_bool(ID_C_constant))
    naming_pointer.base_type().set(ID_C_constant, true);
  cpp_typecheck.make_ptr_typecast(address, naming_pointer);
  dereference_exprt subobject{address, naming_pointer.base_type()};
  subobject.set(ID_C_lvalue, object.get_bool(ID_C_lvalue));
  subobject.add_source_location() = source_location;
  return std::move(subobject);
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
        object = object_of_naming_class(object, identifier, source_location);

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
          if(original_scope->this_expr.is_nil())
            e.set(ID_C_lvalue, true);
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
          // N5008 [expr.prim.id.unqual]/3: an id-expression naming a data
          // member is an lvalue.  Where `this' is not available yet (a
          // trailing-return-type, [expr.prim.this]/4) the member stands
          // for (*this).m ([expr.prim.id.general]/2) all the same, and
          // `hr(m)' with `int hr(int &)' must bind to it.  In a function
          // body the member access through the real `this' decides.
          if(original_scope->this_expr.is_nil())
            e.set(ID_C_lvalue, true);
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
      else if(symbol.type.id() == ID_array)
      {
        // Likewise a constexpr ARRAY variable: it is still an object
        // whose elements are lvalues (N5008 [dcl.constexpr],
        // [expr.sub]); substituting the brace initializer turned
        // libc++ <charconv>'s `&__digits_base_10[__value * 2]`
        // (__itoa::__append2) into address-of an array LITERAL
        // ("address_of error: ... not an lvalue").  Constant indexing
        // still folds downstream through the symbol's initializer.
        e = cpp_symbol_expr(symbol);
      }
      else
      {
        e = symbol.value;
        if(e.is_nil())
          e = cpp_symbol_expr(symbol);
        else
        {
          // N5008 [class.static.data]/4, [expr.unary.op]/3: a constexpr
          // variable is still an object; remember it, so that taking its
          // address (libc++ any's `&__unique_typeinfo<T>::__id') uses the
          // object rather than the substituted value
          e.set(ID_C_constexpr_object, symbol.name);
        }
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
/// N5008 [over.match.funcs]/5: a non-static member function's implicit
/// object parameter is a reference to `cv X`, where cv is the function's
/// cv-qualification; a const object argument therefore cannot bind to a
/// NON-const member -- that candidate is not viable ([over.match.viable]).
/// A member-template candidate is still a `template_function_instance`
/// here (its code type carries no `this` parameter), so the real
/// implicit-object check on the instantiated symbol never sees it; the
/// const/non-const pair then TIED on distance and the tie broke by
/// candidate ORDER.  Under the heap-address ordering of scope lookups
/// that was silently layout-dependent: `__source._M_access<_Functor*>()`
/// on a `const _Any_data&` (libstdc++ std::function's _M_get_pointer)
/// instantiated the non-const overload, which then failed the real
/// `this` check, leaving std::function invocation bodiless.
/// \return false when the object argument is const and the candidate is a
///   non-const member template.
bool cpp_typecheck_resolvet::member_template_object_viable(
  const exprt &cand,
  const cpp_typecheck_fargst &fargs)
{
  if(cand.id() != ID_template_function_instance)
    return true;
  if(!fargs.has_object || fargs.operands.empty())
    return true;
  const irep_idt tmpl = cand.type().get(ID_C_template);
  if(tmpl.empty())
    return true;
  const symbolt *tsym = cpp_typecheck.symbol_table.lookup(tmpl);
  if(tsym == nullptr || tsym->type.id() != ID_cpp_declaration)
    return true;
  const cpp_declarationt &decl = to_cpp_declaration(tsym->type);
  if(decl.declarators().empty())
    return true;
  // static member templates have no implicit object parameter
  if(decl.storage_spec().is_static())
    return true;
  const typet &mq = static_cast<const typet &>(
    decl.declarators().front().find(ID_method_qualifier));
  const bool member_const = cpp_typecheck.has_const(mq);
  // N5008 [over.match.funcs.general]/4: with a ref-qualifier, the implicit
  // object parameter is an lvalue (`&') or rvalue (`&&') reference, bound
  // by the usual rules (/5's licence for an rvalue object applies only
  // without one)
  const irep_idt ref_qualifier = member_template_ref_qualifier(decl);
  if(!ref_qualifier.empty())
  {
    const bool object_is_lvalue =
      cpp_typecheck.is_lvalue_expression(fargs.operands.front());
    if(ref_qualifier == "&&" && object_is_lvalue)
      return false;
    if(ref_qualifier == "&" && !object_is_lvalue && !member_const)
      return false;
  }
  if(!fargs.operands.front().type().get_bool(ID_C_constant))
    return true;
  return member_const;
}

unsigned cpp_typecheck_resolvet::member_template_const_penalty(
  const exprt &cand,
  const cpp_typecheck_fargst &fargs)
{
  if(cand.id() != ID_template_function_instance)
    return 0;

  // Determine the object argument's constness.  For an explicit object
  // (`obj.f(...)`) it is the first operand.  For an IMPLICIT member
  // call from within another member function, N5008 [over.call.func]/3:
  // the implied object argument is `(*this)` -- derive its constness
  // from the enclosing member's `this` (a const member's this points
  // to const).  Without this, the const / non-const member-template
  // overload pair tied and the call was rejected as ambiguous
  // ("does not uniquely resolve"), silently dropping the caller's
  // body -- libc++ __tree::find's `__lower_bound(...)` call, the
  // std::map::find wrong-result shape.
  bool object_const = false;
  bool have_object = false;
  if(fargs.has_object && !fargs.operands.empty())
  {
    object_const = fargs.operands.front().type().get_bool(ID_C_constant);
    have_object = true;
  }
  else
  {
    const exprt &this_expr = cpp_typecheck.cpp_scopes.current_scope().this_expr;
    if(this_expr.is_not_nil() && this_expr.type().id() == ID_pointer)
    {
      object_const =
        to_pointer_type(this_expr.type()).base_type().get_bool(ID_C_constant);
      have_object = true;
    }
  }
  if(!have_object)
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
  unsigned penalty = (member_const && !object_const) ? 1 : 0;
  // [over.ics.rank]/3.2.3: binding an rvalue object to an rvalue reference
  // (an `&&' overload) is better than to the `const &' of an `&' overload
  if(
    fargs.has_object && !fargs.operands.empty() &&
    member_template_ref_qualifier(decl) == "&" &&
    !cpp_typecheck.is_lvalue_expression(fargs.operands.front()))
  {
    ++penalty;
  }
  return penalty;
}

irep_idt cpp_typecheck_resolvet::member_template_ref_qualifier(
  const cpp_declarationt &decl)
{
  return decl.declarators()
    .front()
    .merge_type(decl.type())
    .get(ID_C_ref_qualifier);
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
  // per candidate, in the order of distance_map's entries (a multimap
  // keeps equal keys in insertion order): the reference-binding
  // tie-breaker and the number of template arguments, a last resort when
  // partial ordering leaves specializations unordered.  (Not keyed by the
  // expression: candidates differing only in comments, ID_C_template
  // among them, compare equal.)
  struct rankt
  {
    unsigned cv_distance;
    std::size_t template_argument_count;
    // cv_distance per argument (the implicit object argument of a member
    // template specialization first)
    std::vector<unsigned> cv_per_argument;
  };
  std::multimap<std::size_t, rankt> rank_map;

  for(const auto &old_id : old_identifiers)
  {
    unsigned args_distance;
    unsigned cv_distance = 0;
    std::vector<unsigned> cv_per_argument;

    if(!member_template_object_viable(old_id, fargs))
      continue;

    if(disambiguate_functions(
         old_id, args_distance, fargs, &cv_distance, &cv_per_argument))
    {
      const unsigned object_penalty =
        member_template_const_penalty(old_id, fargs);
      cv_distance += object_penalty;
      // a member template specialization's type has no `this' parameter
      // yet; its implicit object argument's share is the penalty
      if(old_id.id() == ID_template_function_instance && fargs.has_object)
        cv_per_argument.insert(cv_per_argument.begin(), object_penalty);
      std::size_t template_distance = 0;

      // N5008 [over.match.best]/2.5: a non-template function is
      // preferred over a function template specialization; between TWO
      // specializations the tie is broken by partial ordering
      // ([temp.func.order]), which runs on the equal-distance group
      // below.  The penalty is therefore BINARY -- template or not --
      // and must not compare template-argument COUNTS: the count is no
      // measure of specialization (the more specialized of libc++'s
      // ranges `end(T (&)[N])` / `end(T)` pair has MORE arguments, and
      // the count-key wrongly selected the generic one, leaving its
      // undeduced-auto return in the initializer:
      // "conversion from '<<type:auto>>'").
      std::size_t template_argument_count = 0;
      if(!old_id.type().get(ID_C_template).empty())
      {
        template_distance = 1;
        template_argument_count = old_id.type()
                                    .find(ID_C_template_arguments)
                                    .find(ID_arguments)
                                    .get_sub()
                                    .size();
      }
      // An ALREADY-INSTANTIATED function template specialization enters
      // the candidate set as a plain symbol without ID_C_template; it
      // carries #fn_template_type instead.  It is still a specialization
      // ([over.match.best]/2.5 distinguishes by whether the candidate IS
      // one, not by whether it was instantiated earlier).  Ranked as a
      // non-template it beat the not-yet-instantiated sibling overload
      // whose conversion sequence is BETTER: libstdc++'s
      // `shared_ptr(shared_ptr<_Yp>&& __r) : __shared_ptr<_Tp>(
      // std::move(__r))` bound the xvalue to the const& converting
      // constructor whenever that one had been instantiated first (a
      // candidate-order accident), copying instead of moving.
      else if(old_id.id() == ID_symbol)
      {
        // The marker lives on the symbol's type in the symbol table; the
        // candidate expression carries a copy of the component type only.
        const symbolt *cand_sym = cpp_typecheck.symbol_table.lookup(
          to_symbol_expr(old_id).get_identifier());
        if(
          cand_sym != nullptr &&
          cand_sym->type.find(irep_idt{"#fn_template_type"}).is_not_nil())
        {
          template_distance = 1;
          template_argument_count = std::max<std::size_t>(
            1,
            cand_sym->type.find(irep_idt{"#fn_template_args"})
              .find(ID_arguments)
              .get_sub()
              .size());
        }
      }

      // N5008 [dcl.spec.auto.general]/13: a candidate whose return type
      // is an `auto` placeholder that can NEVER be deduced -- a
      // declared-but-never-defined `auto f(T);` overload -- cannot be
      // used where its type is needed; ranking it above a definable
      // candidate leaves the placeholder in the caller ("conversion
      // from '<<type:auto>>'", libc++'s ranges end(T (&)[N]) / end(T)
      // pair, where the count-based template key otherwise prefers the
      // bodiless generic).  At ranking time every not-yet-instantiated
      // candidate still shows `auto`, so the discriminator is the
      // TEMPLATE's definition: penalise only when the declarator has no
      // body (nothing to deduce from, ever).  The candidate stays
      // viable when it is the only match.
      std::size_t undeduced_auto_penalty = 0;
      if(
        old_id.type().id() == ID_code &&
        to_code_type(old_id.type()).return_type().id() == ID_auto)
      {
        const irep_idt tmpl_id = old_id.type().get(ID_C_template);
        if(!tmpl_id.empty())
        {
          const symbolt *tmpl_sym = cpp_typecheck.symbol_table.lookup(tmpl_id);
          if(
            tmpl_sym != nullptr && tmpl_sym->type.id() == ID_cpp_declaration &&
            !to_cpp_declaration(tmpl_sym->type).declarators().empty() &&
            to_cpp_declaration(tmpl_sym->type)
              .declarators()[0]
              .value()
              .is_nil())
            undeduced_auto_penalty = 1;
        }
      }

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
        1000000000ULL * args_distance + 100000000ULL * undeduced_auto_penalty +
        1000 * template_distance;

      distance_map.insert({total_distance, old_id});
      rank_map.insert(
        {total_distance,
         {cv_distance, template_argument_count, std::move(cv_per_argument)}});
    }
  }

  old_identifiers.clear();

  // put in the top ones
  std::vector<rankt> ranks;
  if(!distance_map.empty())
  {
    auto range = distance_map.equal_range(distance_map.begin()->first);
    for(auto it = range.first; it != range.second; ++it)
      old_identifiers.push_back(it->second);
    auto rank_range = rank_map.equal_range(distance_map.begin()->first);
    for(auto it = rank_range.first; it != rank_range.second; ++it)
      ranks.push_back(it->second);
  }

  // N5008 [over.ics.rank]/3.2.3, /3.2.6: of two REFERENCE bindings, one
  // binding an rvalue reference to an rvalue (rather than an lvalue
  // reference), or one to a less cv-qualified type, is better; the rules
  // compare reference bindings only.  `cv_distance' sums them per
  // candidate, so it decides between two candidates only when their
  // parameters are references at the same positions -- a by-value
  // `wrap(From, To)' and a `wrap(const I &, I)' are indistinguishable
  // here, and partial ordering below selects the latter (libstdc++'s
  // __niter_wrap).
  if(old_identifiers.size() > 1)
  {
    const auto reference_shape = [](const exprt &candidate)
    {
      std::vector<bool> shape;
      if(candidate.type().id() == ID_code)
      {
        for(const auto &p : to_code_type(candidate.type()).parameters())
          shape.push_back(
            is_reference(p.type()) || is_rvalue_reference(p.type()));
      }
      return shape;
    };
    std::vector<bool> dominated(old_identifiers.size(), false);
    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      for(std::size_t j = 0; j < old_identifiers.size(); ++j)
      {
        if(
          i == j || ranks[j].cv_distance >= ranks[i].cv_distance ||
          reference_shape(old_identifiers[i]) !=
            reference_shape(old_identifiers[j]))
        {
          continue;
        }
        // [over.match.best.general]/2.1: j is better only if it is not
        // worse for any argument (S().f(x) with f(int &) const & and
        // f(const int &) && is ambiguous)
        const auto &cv_i = ranks[i].cv_per_argument;
        const auto &cv_j = ranks[j].cv_per_argument;
        bool not_worse = true;
        if(cv_i.size() == cv_j.size())
        {
          for(std::size_t k = 0; k < cv_i.size(); ++k)
          {
            if(cv_j[k] > cv_i[k])
              not_worse = false;
          }
        }
        if(not_worse)
        {
          dominated[i] = true;
          break;
        }
      }
    }
    resolve_identifierst kept;
    std::vector<rankt> kept_ranks;
    for(std::size_t i = 0; i < old_identifiers.size(); ++i)
    {
      if(!dominated[i])
      {
        kept.push_back(old_identifiers[i]);
        kept_ranks.push_back(ranks[i]);
      }
    }
    old_identifiers.swap(kept);
    ranks.swap(kept_ranks);
  }
  // the template argument counts of the group, for the last-resort
  // ordering below (looked up by expression AND template)
  std::vector<std::pair<exprt, std::size_t>> template_argument_counts;
  for(std::size_t i = 0; i < old_identifiers.size() && i < ranks.size(); ++i)
  {
    template_argument_counts.emplace_back(
      old_identifiers[i], ranks[i].template_argument_count);
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

    // [over.match.best]/2.5 orders function template specializations by
    // partial ordering ([temp.func.order]) only; two that remain unordered
    // make the call ambiguous.  function_template_at_least_as_specialised
    // does not implement all of [temp.deduct.partial] (packs, non-type
    // patterns), so as a last resort prefer the specialization with fewer
    // template arguments -- the former ranking heuristic, now applied only
    // after partial ordering, which it used to pre-empt (`f(const S &)'
    // was preferred to the more specialized `f(const basic_string<C, T, A>
    // &)').
    if(identifiers.size() > 1)
    {
      const auto count_of = [&](const exprt &id) -> std::optional<std::size_t>
      {
        for(const auto &entry : template_argument_counts)
        {
          if(
            entry.first == id && entry.first.type().get(ID_C_template) ==
                                   id.type().get(ID_C_template))
          {
            return entry.second;
          }
        }
        return {};
      };
      std::size_t fewest = std::numeric_limits<std::size_t>::max();
      for(const auto &id : identifiers)
      {
        if(const auto count = count_of(id))
          fewest = std::min(fewest, *count);
      }
      resolve_identifierst fewer;
      for(const auto &id : identifiers)
      {
        const auto count = count_of(id);
        if(!count.has_value() || *count == fewest)
          fewer.push_back(id);
      }
      if(!fewer.empty())
        identifiers.swap(fewer);
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
    else if(
      identifier.type().id() == ID_struct_tag ||
      identifier.type().id() == ID_union_tag)
    {
      // N5008 [class.union.general]/1-2: a union is a class; it has
      // constructors like any other class, and a non-POD union
      // ([class.default.ctor]/1: with an implicitly-declared default
      // constructor when none is user-declared) is constructed by calling
      // one -- `__rep()' in libc++ 23's basic_string, whose variant member
      // `__long' has a defaulted default constructor.  Only struct types
      // contributed their constructors here, so the functional cast of a
      // non-POD union found no candidate at all.
      const struct_union_typet &struct_type = cpp_typecheck.follow_tag(
        to_struct_or_union_tag_type(identifier.type()));

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
cpp_scopet &cpp_typecheck_resolvet::resolve_pattern_scope(
  const cpp_namet &cpp_name,
  irep_idt &base_name,
  cpp_template_args_non_tct &template_args)
{
  // Matching the partial specialization `at<al<T>>' while `at<al<int>>::
  // rb<vt>' is being resolved reached resolve_scope for the pattern's names
  // and left original_scope at the specialization's template scope; `vt'
  // was then looked up there ("symbol 'vt' is unknown", libstdc++'s
  // `allocator_traits<_Alloc>::template rebind_alloc<value_type>' in
  // path::generic_string).
  struct point_of_use_guardt
  {
    cpp_typecheck_resolvet &resolver;
    cpp_scopet *const scope;
    const source_locationt location;
    explicit point_of_use_guardt(cpp_typecheck_resolvet &r)
      : resolver(r), scope(r.original_scope), location(r.source_location)
    {
    }
    ~point_of_use_guardt()
    {
      resolver.original_scope = scope;
      resolver.source_location = location;
    }
  } point_of_use_guard{*this};
  return resolve_scope(cpp_name, base_name, template_args);
}

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
            // instead.  libstdc++ has the same shape: `typedef
            // __cv_selector<...> __match; typedef typename __match::__type
            // __type;` in __match_cv_qualifiers (behind __copy_cv and every
            // common_reference), which failed whenever the class was first
            // completed under suppress_elaborate.
            if(sym == nullptr && id_ptr->is_member)
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
          const irept *tpl_node = &tpl_arg;
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
              // The binding names the bound template SYMBOL; its scope
              // entry is in id_map under the same identifier.  A by-name
              // lookup from the root scope (the previous code) cannot find
              // a template nested in a namespace: `Pred<T>::value' with
              // `Pred' bound to `ns::is_ptr' (or std::is_integral) resolved
              // nothing, and every use of a qualified template-name as a
              // template template argument was lost.
              auto it = cpp_typecheck.cpp_scopes.id_map.find(tmpl_id);
              if(
                it != cpp_typecheck.cpp_scopes.id_map.end() &&
                it->second->id_class == cpp_idt::id_classt::TEMPLATE)
              {
                id_set.insert(it->second);
              }
              else if(cpp_typecheck.symbol_table.has_symbol(tmpl_id))
              {
                const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
                // the id_map entry under the template's identifier is its
                // parameter SCOPE; the template-name is declared in the
                // enclosing scope (a namespace, a class) -- look there,
                // and only from the root as a last resort
                if(
                  it != cpp_typecheck.cpp_scopes.id_map.end() &&
                  it->second->id_class == cpp_idt::id_classt::TEMPLATE_SCOPE &&
                  it->second->is_scope &&
                  !static_cast<cpp_scopet &>(*it->second).is_root_scope())
                {
                  auto found = static_cast<cpp_scopet &>(*it->second)
                                 .get_parent()
                                 .lookup(
                                   tmpl_sym.base_name,
                                   cpp_scopet::SCOPE_ONLY,
                                   cpp_idt::id_classt::TEMPLATE);
                  for(const auto &f : found)
                    id_set.insert(f);
                }
                if(id_set.empty())
                {
                  auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
                    tmpl_sym.base_name,
                    cpp_scopet::RECURSIVE,
                    cpp_idt::id_classt::TEMPLATE);
                  for(const auto &f : found)
                    id_set.insert(f);
                }
              }
            }
            else if(
              e.id() == ID_type &&
              (e.type().id() == ID_struct_tag || e.type().id() == ID_union_tag))
            {
              // N5008 [temp.deduct.type]/8: same as the resolve-with-
              // arguments site -- deduction binds the TT-parameter to
              // the argument INSTANCE; a SCOPE use with template
              // arguments (`_Alloc<_Tp, _Args...>::template
              // rebind<_Up>`, libc++ __allocator_traits_rebind's
              // partial-specialization body walking into the member
              // template) names the TEMPLATE the instance came from.
              // Derive it here too; otherwise the qualified-name walk
              // failed and std::set's __node_allocator typedef chain
              // (__tree line 925) was dropped.
              const irep_idt inst_id =
                e.type().id() == ID_struct_tag
                  ? to_struct_tag_type(e.type()).get_identifier()
                  : to_union_tag_type(e.type()).get_identifier();
              const symbolt *inst_sym =
                cpp_typecheck.symbol_table.lookup(inst_id);
              if(inst_sym != nullptr)
              {
                auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
                  inst_sym->base_name,
                  cpp_scopet::RECURSIVE,
                  cpp_idt::id_classt::TEMPLATE);
                for(const auto &f : found)
                {
                  const symbolt *cand =
                    cpp_typecheck.symbol_table.lookup(f->identifier);
                  if(
                    cand != nullptr && cand->type.get_bool(ID_is_template) &&
                    to_cpp_declaration(cand->type)
                      .type()
                      .get(ID_specialization_of)
                      .empty())
                    id_set.insert(f);
                }
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

        // N5008 [basic.lookup.qual.general]/1: the lookup of a name followed
        // by `::' considers only namespaces, types and templates whose
        // specializations are types.  An ordinary RECURSIVE lookup stops at
        // the first scope declaring the name; when everything found there is
        // a variable or function (`int f(int N) { return N::b; }', libc++'s
        // `__validate_second(__flags __flags)' using `__flags::__second'),
        // those declarations are not considered and the search continues in
        // the enclosing scopes.
        if(recursive)
        {
          const auto is_object_or_function = [](const cpp_idt *id)
          {
            return id->id_class == cpp_idt::id_classt::SYMBOL ||
                   id->id_class == cpp_idt::id_classt::UNKNOWN;
          };
          while(
            !id_set.empty() &&
            std::all_of(id_set.begin(), id_set.end(), is_object_or_function))
          {
            // continue above the scope that declares the names found
            cpp_scopet &declaring =
              static_cast<cpp_scopet &>((*id_set.begin())->get_parent());
            if(declaring.is_root_scope())
            {
              id_set.clear();
              break;
            }
            id_set = declaring.get_parent().lookup(
              final_base_name, cpp_scopet::RECURSIVE);
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
        // N5008 [basic.lookup.unqual]/5: a name in the conversion-type-id
        // is looked up in the same fashion as the conversion-function-id --
        // for `B::operator I', a search in the class B -- and, if that finds
        // nothing, by unqualified lookup from where it appears: `using
        // B::operator I;' in A finds the member typedef A::I (libstdc++'s
        // atomic<int>, `using __base_type::operator __integral_type;').
        const irept *first_name = op_name.id() == ID_cpp_name &&
                                      !op_name.get_sub().empty() &&
                                      op_name.get_sub().front().id() == ID_name
                                    ? &op_name.get_sub().front()
                                    : nullptr;
        if(
          first_name != nullptr && original_scope != nullptr &&
          original_scope != &cpp_typecheck.cpp_scopes.current_scope() &&
          cpp_typecheck.cpp_scopes.current_scope()
            .lookup(first_name->get(ID_identifier), cpp_scopet::QUALIFIED)
            .empty())
        {
          cpp_save_scopet saved_scope(cpp_typecheck.cpp_scopes);
          cpp_typecheck.cpp_scopes.go_to(*original_scope);
          cpp_typecheck.typecheck_type(op_name);
        }
        else
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
} // NOLINT(readability/fn_size)

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

  // N5008 [temp.deduct.type]/8: a deduced template-template-parameter
  // is bound to the argument INSTANCE; template_map.apply can
  // substitute that binding textually into a qualified name, so the
  // scope walk arrives here with the INSTANCE'S TAG as the "template
  // name" (`tag-allocator<signed_int>` with new template arguments --
  // libc++ __allocator_traits_rebind's `_Alloc<_Tp>::template
  // rebind<_Up>`).  Derive the TEMPLATE the instance was created from
  // (the same convention as the resolve/resolve_scope TT fallbacks).
  if(effective_id_set.empty())
  {
    const symbolt *inst_sym = cpp_typecheck.symbol_table.lookup(base_name);
    if(inst_sym == nullptr)
    {
      // instance tags of non-global templates carry a scope prefix;
      // try the current prefix chain via the scope-aware lookup
      const auto inst_ids = cpp_typecheck.cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::RECURSIVE);
      if(!inst_ids.empty())
        inst_sym =
          cpp_typecheck.symbol_table.lookup((*inst_ids.begin())->identifier);
    }
    if(
      inst_sym != nullptr &&
      (inst_sym->type.id() == ID_struct || inst_sym->type.id() == ID_union) &&
      inst_sym->type.find(ID_full_template_args).is_not_nil())
    {
      auto tmpl_ids = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
        inst_sym->base_name,
        cpp_scopet::RECURSIVE,
        cpp_idt::id_classt::TEMPLATE);
      if(tmpl_ids.empty())
      {
        // A namespace-scope template's id is not reachable by the
        // root-scope RECURSIVE walk (it does not descend into
        // namespaces).  Per N5008 [namespace.qual]/[basic.lookup.qual]
        // the template lives in the same scope as its instances: the
        // instance's scope-tree entry sits INSIDE the template's
        // parameter scope, so the template's own id is found by an
        // unqualified lookup in that scope's PARENT (the namespace,
        // e.g. `std::__1` for `std::__1::allocator<signed_int>` --
        // the libc++ `_Alloc<_Tp>::template rebind<_Up>` shape of
        // __allocator_traits_rebind).
        const auto im_it = cpp_typecheck.cpp_scopes.id_map.find(inst_sym->name);
        if(im_it != cpp_typecheck.cpp_scopes.id_map.end())
        {
          tmpl_ids =
            static_cast<cpp_scopet &>(im_it->second->get_parent().get_parent())
              .lookup(
                inst_sym->base_name,
                cpp_scopet::SCOPE_ONLY,
                cpp_idt::id_classt::TEMPLATE);
        }
      }
      for(auto *tid : tmpl_ids)
      {
        const symbolt *cand =
          cpp_typecheck.symbol_table.lookup(tid->identifier);
        if(
          cand != nullptr && cand->type.get_bool(ID_is_template) &&
          to_cpp_declaration(cand->type)
            .type()
            .get(ID_specialization_of)
            .empty())
          effective_id_set.insert(tid);
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
  // N5008 [temp.spec.partial.match]/1: the primary template is used
  // only when NO partial specialisation matches; it never competes on
  // the specialisation-argument count below.  `cost` is that count, so a
  // primary with fewer template parameters than a matching
  // specialisation (`un<T>` vs `un<pack<A, B>>`, two parameters) used to
  // win outright.
  matches.back().cost = std::numeric_limits<std::size_t>::max();

  for(const auto &id_ptr : id_set)
  {
    const irep_idt id = id_ptr->identifier;
    // A scope entry may name an entity whose SYMBOL does not exist yet:
    // members of a class-template instance are registered in the scope
    // as the instance is elaborated, and a member typedef of a not-yet-
    // elaborated instance (e.g. `vector<T,A>::reverse_iterator` reached
    // through std::equal over reverse iterators) has an entry but no
    // symbol.  namespacet::lookup asserts in that case, aborting the
    // whole run; such an entry is simply not a usable candidate here.
    if(!cpp_typecheck.symbol_table.has_symbol(id))
      continue;
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
    deduction_nontype_types_guardt deduction_nontype_types_guard{
      current_deduction_nontype_types};
    current_deduction_nontype_types =
      template_nontype_parameter_types(cpp_declaration.template_type());
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

    // N5008 [temp.deduct.type]/8: matching a partial specialization's
    // argument PATTERN uses the strict P/A form rules -- a reference
    // pattern (`T&`) requires a reference argument and cv-qualifiers
    // are part of the pattern.  The other spec-matching sites
    // (instantiate_template / elaborate_class_template) already opt
    // in; this one deduced `decay_<T&>` from `decay_<int*>` (stripping
    // the `&`), selecting the reference specialization, so
    // `decay_t_<int*>` resolved to `int` (libc++
    // __to_address/__decay_t return-type shape).
    const bool saved_strict_cv = strict_cv_deduction;
    strict_cv_deduction = true;

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
          // N5008 [temp.deduct.type]/9-10: the trailing pack binds the
          // remaining arguments -- TYPES for a type parameter pack, VALUES
          // for a non-type one (`template<int H, int... T> struct
          // sum_t<H, T...>`).  A value pack is recorded in pack_expr_map
          // (see the template-id deduction in guess_template_args); it used
          // to be recorded as an EMPTY type pack, so `sum_t<1, 2, 3>`
          // matched the specialization with T = {} and had no `v`.
          std::vector<typet> pack_elems;
          exprt::operandst pack_exprs;
          for(std::size_t j = i; j < n_full; j++)
          {
            const exprt &a = full_template_args_tc.arguments()[j];
            if(a.id() == ID_type)
            {
              if(a.type().id() != ID_empty)
                pack_elems.push_back(a.type());
            }
            else
              pack_exprs.push_back(a);
          }
          cpp_typecheck.template_map.set_pack_size(
            pack_id, pack_elems.size() + pack_exprs.size());
          if(pack_exprs.empty())
          {
            cpp_typecheck.template_map.pack_args_map[pack_id] = pack_elems;
            if(!pack_elems.empty())
              cpp_typecheck.template_map.type_map[pack_id] = pack_elems.front();
          }
          else
          {
            cpp_typecheck.template_map.pack_expr_map[pack_id] = pack_exprs;
            cpp_typecheck.template_map.expr_map[pack_id] = pack_exprs.front();
          }
        }
        else
        {
          deduce_trailing_type_pack_pattern(
            parg_t, cpp_declaration.template_type(), full_template_args_tc, i);
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

    strict_cv_deduction = saved_strict_cv;

    // see if that has worked out

    cpp_template_args_tct guessed_template_args =
      cpp_typecheck.template_map.build_template_args(
        cpp_declaration.template_type());

    if(
      !guessed_template_args.has_unassigned() &&
      !guessed_template_args.has_conflict())
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
            // [temp.variadic]/5 likewise for a NON-TYPE pack: its deduced
            // element VALUES live in pack_expr_map, not pack_args_map
            // (mirroring the same splice in instantiate_template's
            // specialization matching).  Without it only the scalar
            // convenience element survived: `pf<Op, index_sequence<Idx...>,
            // Bound...>` (libc++ __perfect_forward) stored `Idx = {0}`
            // instead of `{0, 1}`, mis-instantiating the members and
            // dropping every caller of `decltype(_Op()(_Idx...))`.
            auto pe_it = cpp_typecheck.template_map.pack_expr_map.find(pid);
            if(pe_it != cpp_typecheck.template_map.pack_expr_map.end())
            {
              for(const auto &pe : pe_it->second)
                expanded.push_back(pe);
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
          // Scope the two-phase-lookup filter (see resolve()) to the
          // pattern typecheck below ([temp.res.general]/1).
          ++cpp_typecheck.two_phase_pattern_depth;
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
          --cpp_typecheck.two_phase_pattern_depth;
        }
        catch(...)
        {
          cpp_typecheck.disable_template_arg_pack_expansion = false;
          --cpp_typecheck.two_phase_pattern_depth;
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

      // N5008 [temp.type]/1, [dcl.fct]/5: a function type argument may be
      // in parsed form (a written `void(int)': parameters as
      // cpp_declaration) or converted (`decltype(cb)', a deduced F:
      // parameters as `parameter'); both denote the same type.  Compare
      // them in converted form.
      const auto canonical_function_types = [&](cpp_template_args_tct args)
      {
        for(auto &arg : args.arguments())
        {
          if(arg.id() == ID_type && arg.type().id() == ID_code)
            arg.type() = canonical_function_type(arg.type());
        }
        return args;
      };
      const bool function_type_argument = std::any_of(
        full_template_args_tc.arguments().begin(),
        full_template_args_tc.arguments().end(),
        [](const exprt &a)
        { return a.id() == ID_type && a.type().id() == ID_code; });

      if(
        partial_specialization_args_tc == full_template_args_tc ||
        (function_type_argument &&
         canonical_function_types(partial_specialization_args_tc) ==
           canonical_function_types(full_template_args_tc)))
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
          // N5008 [temp.deduct.partial]/7-9: of two patterns differing in
          // cv-qualification, the more qualified one is more specialized
          // (`const volatile T' over `const T').  Deduction-based ordering
          // below decides that for plain patterns; for patterns written
          // through an alias template (`ident<const volatile T, int>',
          // libc++'s __enable_if_tuple_size_imp) it leaves the candidates
          // unordered, and these sort keys decide -- so count each
          // qualifier.
          std::function<std::size_t(const irept &)> count_qualifiers =
            [&count_qualifiers](const irept &n) -> std::size_t
          {
            std::size_t count =
              (n.id() == ID_const || n.id() == ID_volatile) ? 1 : 0;
            for(const auto &sub : n.get_sub())
              count += count_qualifiers(sub);
            for(const auto &named_sub : n.get_named_sub())
            {
              if(named_sub.first != ID_C_source_location)
                count += count_qualifiers(named_sub.second);
            }
            return count;
          };
          for(const auto &arg : partial_specialization_args.arguments())
            constrained += count_qualifiers(arg);
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
                // [temp.constr.op]: short-circuiting evaluation
                const auto r = cpp_typecheck.evaluate_constraint(req_copy);
                if(r.has_value())
                {
                  evaluated = true;
                  satisfied = *r;
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

  // N5008 [temp.spec.partial.order]/1: when more than one partial
  // specialisation matches, the one selected is the one that is MORE
  // SPECIALISED than the others -- each viewed as a function template
  // over its argument pattern and ordered by deduction
  // ([temp.func.order]).  The keys sorted on above (argument count,
  // constrained-argument count, repeated parameters) are heuristics that
  // get real library shapes wrong in both directions: `traits<_Tp*>` and
  // `traits<const _Tp*>` (libstdc++ iterator_traits) tie for
  // `const char*` and std::sort -- unstable -- left the winner to
  // candidate ORDER (`_Tp = const char` made regex's _Executor operate on
  // basic_regex<const char, ...> and match no constructor); and chrono's
  // `common_type<duration<R1,P1>, duration<R2,P2>>` (four parameters)
  // sorted BEHIND the generic `common_type<_Tp1, _Tp2>`.  Decide by
  // deduction first; the sorted keys, then the symbol identifier, break
  // only genuinely unordered pairs -- deterministically.  The primary
  // (baseline, infinite cost) is used only when nothing else matched
  // ([temp.spec.partial.match]/1).
  if(matches.size() > 1)
  {
    const auto decl_of = [&](const matcht &m) -> const cpp_declarationt &
    { return to_cpp_declaration(cpp_typecheck.lookup(m.id).type); };
    const auto is_primary = [&](const matcht &m)
    { return m.id == primary_template_symbol.name; };
    std::size_t best = 0;
    for(std::size_t i = 1; i < matches.size(); ++i)
    {
      if(is_primary(matches[i]))
        continue;
      if(is_primary(matches[best]))
      {
        best = i;
        continue;
      }
      const bool i_at_least =
        cpp_typecheck.partial_specialization_at_least_as_specialised(
          decl_of(matches[i]), decl_of(matches[best]), matches[best].id);
      const bool best_at_least =
        cpp_typecheck.partial_specialization_at_least_as_specialised(
          decl_of(matches[best]), decl_of(matches[i]), matches[i].id);
      if(i_at_least && !best_at_least)
        best = i;
      else if(i_at_least == best_at_least)
      {
        // unordered by deduction: sorted keys, then identifier
        if(matches[i] < matches[best])
          best = i;
        else if(
          !(matches[best] < matches[i]) &&
          id2string(matches[i].id) < id2string(matches[best].id))
          best = i;
      }
    }
    if(best != 0)
      std::swap(matches[0], matches[best]);
  }

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
} // NOLINT(readability/fn_size)

/// Whether naming the alias template \p alias leaves the completeness of its
/// arguments to the aliased type ([temp.inst]/2): the alias denotes a pointer
/// or reference to one of its parameters (`template <class U> using rebind =
/// U *;', pointer_traits<T *>::rebind), or forwards to a member template-id
/// of another class (`typename pointer_traits<From>::template rebind<To>',
/// libc++'s __rebind_pointer_t), whose own alias then decides.
bool cpp_typecheck_resolvet::alias_leaves_arguments_incomplete(
  const cpp_declarationt &alias)
{
  // `using A = X;' is parsed as `typedef X A;': the declaration type is
  // merged_type(..., X, typedef) and the declarator carries no type
  if(
    alias.declarators().size() != 1 ||
    alias.declarators().front().type().is_not_nil() ||
    alias.type().id() != ID_merged_type)
  {
    return false;
  }
  const typet *aliased = nullptr;
  for(const auto &sub : to_merged_type(alias.type()).subtypes())
  {
    if(sub.id() == ID_typedef || sub.id() == ID_typename)
      continue;
    if(aliased != nullptr)
      return false;
    aliased = &sub;
  }
  if(aliased == nullptr)
    return false;

  if(aliased->id() == ID_frontend_pointer)
  {
    // a pointer (or reference) to a bare name that is one of the parameters
    if(aliased->get_sub().size() != 1)
      return false;
    const irept &base = aliased->get_sub().front();
    if(
      base.id() != ID_cpp_name || base.get_sub().size() != 1 ||
      base.get_sub().front().id() != ID_name)
    {
      return false;
    }
    const irep_idt &name = base.get_sub().front().get(ID_identifier);
    for(const auto &parameter : alias.template_type().template_parameters())
    {
      const irep_idt &identifier = parameter.id() == ID_type
                                     ? parameter.type().get(ID_identifier)
                                     : parameter.get(ID_identifier);
      const std::string id = id2string(identifier);
      const auto separator = id.rfind("::");
      if(
        (separator == std::string::npos ? id : id.substr(separator + 2)) ==
        id2string(name))
      {
        return true;
      }
    }
    return false;
  }

  // a qualified name ending in a template-id: `X::template rebind<To>'
  if(aliased->id() != ID_cpp_name)
    return false;
  const auto &subs = aliased->get_sub();
  if(subs.empty() || subs.back().id() != ID_template_args)
    return false;
  for(const auto &sub : subs)
  {
    if(sub.id() == "::")
      return true;
  }
  return false;
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
  static thread_local std::map<std::pair<irep_idt, irept>, unsigned> active;
  irept args_irep = static_cast<const irept &>(full_template_args);
  // A RECURSIVE member alias (libc++'s _OrImpl:
  // `_Result = _OrImpl<sizeof...(_Rest)>::template _Result<_First>`)
  // re-enters with the TEXTUALLY IDENTICAL argument spelling
  // (`<_First>`) at every level while the active template bindings
  // differ (each level peels one pack element, [temp.alias]/2).  Keying
  // on the spelling alone misidentified the well-founded recursion as a
  // cycle and returned the empty placeholder, silently dropping e.g. a
  // base-specifier using the alias.  Append a fingerprint of the
  // CURRENT bindings of every name referenced in the arguments, so only
  // a re-entry with the SAME bindings -- a genuine cycle -- is broken.
  {
    irept fingerprint("template_map_fingerprint");
    std::function<void(const irept &)> collect = [&](const irept &n)
    {
      const irep_idt id = n.get(ID_identifier);
      if(!id.empty())
      {
        auto suffix_matches = [&](const irep_idt &key_id)
        {
          const std::string k = id2string(key_id);
          const auto pos = k.rfind("::");
          return (pos != std::string::npos ? k.substr(pos + 2) : k) ==
                 id2string(id);
        };
        for(const auto &te : cpp_typecheck.template_map.type_map)
          if(suffix_matches(te.first))
            fingerprint.get_sub().push_back(te.second);
        for(const auto &ee : cpp_typecheck.template_map.expr_map)
          if(suffix_matches(ee.first))
            fingerprint.get_sub().push_back(ee.second);
        for(const auto &ps : cpp_typecheck.template_map.pack_size_map)
          if(suffix_matches(ps.first))
          {
            irept sz("pack_size");
            sz.set(ID_value, std::to_string(ps.second));
            fingerprint.get_sub().push_back(sz);
          }
      }
      for(const auto &c : n.get_named_sub())
        collect(c.second);
      for(const auto &c : n.get_sub())
        collect(c);
    };
    collect(args_irep);
    // The re-entry levels of a recursive member alias can also differ
    // ONLY by the enclosing instance the member is looked up in
    // (One<1>::_Result vs One<0>::_Result share the base_name); add
    // the candidate identifiers to the key.
    for(const auto *idp : id_set)
    {
      irept scope_id("scope");
      scope_id.set(ID_identifier, idp->identifier);
      fingerprint.get_sub().push_back(scope_id);
    }
    if(!fingerprint.get_sub().empty())
      args_irep.add("map_fingerprint") = fingerprint;
  }
  // Distinguish legitimate NESTED resolutions of the same alias
  // spelling from genuine cycles: the return type of a function
  // template candidate is substituted after the candidate's deduction
  // map is reverted, so a nested resolution (e.g. the inner
  // `__decay_t<decltype(std::__to_address(...))>` while computing the
  // OUTER __to_address's identically-spelled return type,
  // pointer_traits.h) reaches here with the SAME spelling and the
  // SAME visible bindings.  Such nesting differs in the INSTANTIATION
  // CONTEXT ([temp.point]): add the innermost instantiation frame to
  // the key.  A genuine mutual-recursion cycle repeats the same frame
  // and still trips the per-key cap; as a backstop, an absolute
  // same-spelling depth cap below bounds alternating-frame cycles.
  {
    irept ctx("ctx");
    if(!cpp_typecheck.instantiation_stack.empty())
    {
      ctx.set(
        ID_identifier, cpp_typecheck.instantiation_stack.back().identifier);
      ctx.set_size_t(
        irep_idt{"depth"}, cpp_typecheck.instantiation_stack.size());
    }
    args_irep.add("instantiation_ctx") = ctx;
  }
  static thread_local std::map<irep_idt, unsigned> spelling_depth;
  unsigned &sdepth = spelling_depth[base_name];
  if(sdepth >= 20)
    return empty_typet{};
  struct sdepth_guardt
  {
    unsigned &d;
    explicit sdepth_guardt(unsigned &_d) : d(_d)
    {
      ++d;
    }
    ~sdepth_guardt()
    {
      --d;
    }
  } sdepth_guard{sdepth};
  // (map_fingerprint and instantiation_ctx are regular named sub-trees:
  // irept::compare ignores comments, `#'-prefixed names, which then left
  // every level of a recursion like libstdc++'s __parse_int::_Number_help
  // with `__ull_constant<_Pow * __digit::value + __next::type::value>' with
  // the same key, and the third nested level was cut off.)
  std::pair<irep_idt, irept> key{base_name, args_irep};
  // Re-entry with an identical key is NOT necessarily a cycle: the
  // legitimate resolution of a member alias delegates to
  // instantiate_template, whose conversion of the alias declaration
  // re-resolves the SAME spelled type once more before the outer call
  // completes (libc++'s recursive _OrImpl::_Result).  Allow a small
  // bounded number of same-key re-entries -- a genuine mutual-recursion
  // cycle (the MSVC add_rvalue_reference_t shape this guard exists
  // for) hits the cap and is still broken conservatively.
  unsigned &depth = active[key];
  if(depth >= 2)
    return empty_typet{};
  ++depth;
  struct guardt
  {
    std::map<std::pair<irep_idt, irept>, unsigned> &s;
    std::pair<irep_idt, irept> k;
    ~guardt()
    {
      auto it = s.find(k);
      if(it != s.end() && --it->second == 0)
        s.erase(it);
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
  // _Values pack; libstdc++'s std::variant member alias `__to_type<_Np,
  // enable_if_t<(_Np < sizeof...(_Types))>>` evaluates its default argument
  // against the instance's _Types pack).  instantiate_template builds only
  // the alias's own parameter map, so pre-bind the enclosing instance's
  // parameters -- exactly as add_method_body does for member function
  // bodies.
  //
  // The EXPLICIT arguments are expressions of the referencing context
  // ([basic.lookup.unqual]/1) and must be type-checked BEFORE that pre-bind:
  // the map resolves a bare parameter by SHORT name (conformance violation
  // V1, template_mapt::apply), so with the enclosing `_Tp` of
  // allocator_traits<__new_allocator<_Tp>> pre-bound, the argument `_Tp` of
  // `allocator_traits<_Alloc>::template rebind_alloc<_Tp>` in
  // __alloc_traits::rebind<_Tp> (a DIFFERENT `_Tp`, the live one) resolved to
  // the pre-bound pair type and libstdc++ _Rb_tree's _Node_allocator became
  // the pair allocator.  The DEFAULT arguments, by contrast, belong to the
  // alias and need the enclosing bindings; they are appended in the second
  // pass below, after the pre-bind.
  cpp_template_args_non_tct explicit_args_tc;
  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
    cpp_typecheck.cpp_scopes.go_to(*original_scope);
    // N5008 [temp.inst]/2, [temp.alias]/2: naming a specialization in an
    // alias template's argument list does not by itself require it to be
    // complete -- `rebind<node<void>>' is `node<void> *', and node<void> may
    // be the class whose instantiation is in progress (libc++'s list node
    // rebinding to itself through pointer_traits).  Instantiating it here
    // saw an incomplete base.  Only for the alias shapes that certainly
    // leave the completeness to the aliased type; the contexts that need a
    // complete type elaborate on their own.
    const bool skip_argument_elaboration =
      alias_leaves_arguments_incomplete(to_cpp_declaration(template_sym->type));
    const bool old_skip = cpp_typecheck.skip_typechecking_elaborate;
    if(skip_argument_elaboration)
      cpp_typecheck.skip_typechecking_elaborate = true;
    cpp_template_args_tct explicit_tc;
    try
    {
      explicit_tc = cpp_typecheck.typecheck_template_args(
        source_location,
        *template_sym,
        full_template_args,
        /*explicit_only=*/true);
    }
    catch(...)
    {
      cpp_typecheck.skip_typechecking_elaborate = old_skip;
      throw;
    }
    cpp_typecheck.skip_typechecking_elaborate = old_skip;
    static_cast<irept &>(explicit_args_tc) = static_cast<irept &>(explicit_tc);
    // keep the type-checked types from being re-resolved in the second pass
    // (a template template argument is already the resolved template's
    // parameter-symbol type, which the second pass recognises as such)
    for(auto &arg : explicit_args_tc.arguments())
    {
      if(
        arg.id() == ID_type &&
        arg.type().id() != ID_template_parameter_symbol_type)
      {
        already_typechecked_typet::make_already_typechecked(arg.type());
      }
    }
  }

  cpp_saved_template_mapt saved_enclosing_map(cpp_typecheck.template_map);
  if(template_id_entry != nullptr)
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
            map.set_pack_size(pid, elems.size());
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
            map.set_pack_size(pid, vals.size());
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
        // N5008 [temp.variadic]/7: a trailing pack that matched ZERO
        // arguments is still deduced -- to the empty sequence -- so the
        // loop must reach the pack parameter even when the instance's
        // argument list ends before it (`__integer_sequence<size_t>`
        // with _Values = {}: one argument, two parameters).  Otherwise
        // the pack stays unbound and the member alias body's
        // `(_Values + _Sp)...` expansion, finding no pack state, resolves
        // the bare pack name and fails -- silently dropping the enclosing
        // conversion (the std::tuple constructor's mem-init shape).
        for(std::size_t k = 0; k < enc_params.size(); ++k)
        {
          const auto &param = enc_params[k];
          if(k >= enc_arg_list.size() && !param.get_bool(ID_ellipsis))
            break;
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
            cpp_typecheck.template_map.set_pack_size(
              pack_id, k < enc_arg_list.size() ? enc_arg_list.size() - k : 0);
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

  // second pass: the pre-typechecked explicit arguments plus the alias's
  // default arguments, evaluated with the enclosing instance's bindings
  cpp_template_args_tct template_args_tc;
  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
    cpp_typecheck.cpp_scopes.go_to(*original_scope);
    template_args_tc = cpp_typecheck.typecheck_template_args(
      source_location, *template_sym, explicit_args_tc);
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
        const irept *t = &arg.type();
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

  // Clang's builtin alias template `__make_integer_seq<Tpl, T, N>`
  // names `Tpl<T, 0, ..., N-1>` (the compiler-accelerated backing of
  // [intseq.make]; libc++'s make_integer_sequence and the tuple
  // indices are built on it).  The resolve_scope interception only
  // covers QUALIFIED uses (`__make_integer_seq<...>::member`); a bare
  // use as a type -- e.g. the alias body of
  //   template <class T, T N>
  //   using make_integer_sequence = __make_integer_seq<integer_sequence, T, N>;
  // resolved via resolve_template_alias -- lands here.  Rewrite to the
  // expanded template-id and continue with ordinary resolution.
  if(
    base_name == "__make_integer_seq" && template_args.is_not_nil() &&
    template_args.arguments().size() == 3)
  {
    const auto &ma = template_args.arguments();
    typet elem_type =
      ma[1].id() == ID_type || ma[1].id() == ID_ambiguous
        ? ma[1].type()
        : static_cast<const typet &>(static_cast<const irept &>(ma[1]));
    exprt count = ma[2];
    if(count.id() == ID_type || count.id() == ID_ambiguous)
      count =
        static_cast<const exprt &>(static_cast<const irept &>(count.type()));
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
    const irept *tpl_node = &ma[0];
    if(tpl_node->id() == ID_ambiguous || tpl_node->id() == ID_type)
    {
      const irept &t = ma[0].type();
      if(t.id() == ID_cpp_name)
        tpl_node = &t;
    }
    if(tpl_node->id() == ID_cpp_name)
      tpl_name = to_cpp_name(*tpl_node).get_base_name();

    // N5008 [temp.param]/1 + [intseq.make]: libc++ wraps the builtin
    // in an impl alias whose first argument is a TEMPLATE-TEMPLATE
    // parameter (`__make_integer_seq<_BaseType, _Tp, _SequenceSize>`);
    // at the alias's instantiation the parameter's BINDING names the
    // real sequence template.  Resolve the name through the template
    // map (a template_parameter_symbol_type binding carries the bound
    // template's canonical identifier -- take its base name for the
    // ordinary resolution below).
    // N5008 [temp.param]/1 + [intseq.make]: libc++ wraps the builtin
    // in an impl alias whose first argument is a TEMPLATE-TEMPLATE
    // parameter (`__make_integer_seq<_BaseType, _Tp, _SequenceSize>`);
    // by this point the parameter has been substituted with its
    // BINDING -- an `ambiguous`/`type` node whose type is a
    // template_parameter_symbol_type naming the bound sequence
    // template canonically (`template.integer_sequence<Type0,
    // Non_Type1>`).  Take the template's base name from it.
    if(
      tpl_name.empty() &&
      (ma[0].id() == ID_ambiguous || ma[0].id() == ID_type) &&
      ma[0].type().id() == ID_template_parameter_symbol_type)
    {
      const std::string bound = id2string(
        to_template_parameter_symbol_type(ma[0].type()).get_identifier());
      auto q = bound.rfind("::");
      std::string base = q != std::string::npos ? bound.substr(q + 2) : bound;
      if(base.compare(0, 9, "template.") == 0)
        base = base.substr(9);
      auto angle = base.find('<');
      if(angle != std::string::npos)
        base = base.substr(0, angle);
      if(!base.empty())
        tpl_name = base;
    }
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
      base_name = tpl_name;
      template_args = std::move(expanded_args);
    }
    else
    {
      // dependent or malformed: substitution failure
      throw 0;
    }
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

  // N5008 [basic.lookup.qual]/1: for a qualified name `S::m`, the
  // lookup of `m` is restricted to the scope denoted by the
  // nested-name-specifier (S's scope, its bases and inline/using
  // namespaces -- the QUALIFIED walk); it must NOT continue into
  // ENCLOSING scopes.  The unconditional RECURSIVE walk here made a
  // nonexistent member fall back to a same-named namespace-scope
  // function, wrongly validating detection-idiom specialization
  // patterns like libc++ __to_address_helper's
  // `decltype((void)pointer_traits<_P>::to_address(...))` -- the
  // member is absent, the pattern must fail softly, but the fallback
  // found std::to_address and the void-returning specialization was
  // selected (the cpp20 vector-family __to_address chain).
  // The same holds for a member-qualified name ([basic.lookup.qual.general]/2,
  // the name after `.' or `->'): while its class is still being defined, a
  // member declared later must not be replaced by a same-named entity of an
  // enclosing namespace (libstdc++'s ref_view::begin() named from a
  // constraint evaluated during the class's instantiation found the
  // customization point object ranges::begin).
  cpp_scopet::lookup_kindt lookup_kind = qualified || fargs.member_access
                                           ? cpp_scopet::QUALIFIED
                                           : cpp_scopet::RECURSIVE;

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
          // The binding names the bound template SYMBOL directly; its
          // scope entry is in id_map under the same identifier.  Use
          // that -- a by-name search from the root scope cannot find
          // templates nested in namespaces (RECURSIVE walks towards
          // enclosing scopes, it does not descend): libc++'s
          // `std::__1::__split_buffer_pointer_layout` was missed and
          // the TT-param base `_Layout<__split_buffer, _Tp, _Alloc>`
          // then resolved to the raw parameter, dropping the base
          // class ([temp.param]/1, [temp.names]/2: the parameter's
          // binding is the template to use at the use site).
          auto it = cpp_typecheck.cpp_scopes.id_map.find(tmpl_id);
          if(
            it != cpp_typecheck.cpp_scopes.id_map.end() &&
            it->second->id_class == cpp_idt::id_classt::TEMPLATE)
          {
            id_set.insert(it->second);
          }
          else if(
            it != cpp_typecheck.cpp_scopes.id_map.end() &&
            it->second->id_class == cpp_idt::id_classt::TEMPLATE_SCOPE)
          {
            // id_map holds the template's SCOPE entry; the TEMPLATE
            // id lives in the scope that declared the template.  Look
            // the short name up there (SCOPE_ONLY: exactly that
            // scope).
            const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
            auto found = static_cast<cpp_scopet &>(it->second->get_parent())
                           .lookup(
                             tmpl_sym.base_name,
                             cpp_scopet::SCOPE_ONLY,
                             cpp_idt::id_classt::TEMPLATE);
            for(const auto &f : found)
              id_set.insert(f);
          }
          else
          {
            const symbolt &tmpl_sym = cpp_typecheck.lookup(tmpl_id);
            irep_idt tmpl_base = tmpl_sym.base_name;
            // Fallback: search from root scope to find the template
            auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
              tmpl_base, cpp_scopet::RECURSIVE, cpp_idt::id_classt::TEMPLATE);
            for(const auto &f : found)
              id_set.insert(f);
          }
        }
      }
      else if(
        e.id() == ID_type &&
        (e.type().id() == ID_struct_tag || e.type().id() == ID_union_tag))
      {
        // N5008 [temp.deduct.type]/8 (P = TT<T>): deduction records the
        // template-template parameter's binding as the deduced argument
        // INSTANCE (that unification is load-bearing elsewhere), but a
        // USE of the parameter with its own template-argument list --
        // `_Alloc<_Up>` in the body -- names the TEMPLATE the instance
        // was created from, applied to the NEW arguments.  Derive the
        // template from the instance here at the use site; without
        // this, `_Alloc<_Up>` resolved to the bound instance itself
        // regardless of `_Up` (allocator_traits' rebind chain:
        // R<allocator<int>, char>::type came out allocator<int>).
        const irep_idt inst_id =
          e.type().id() == ID_struct_tag
            ? to_struct_tag_type(e.type()).get_identifier()
            : to_union_tag_type(e.type()).get_identifier();
        const symbolt *inst_sym = cpp_typecheck.symbol_table.lookup(inst_id);
        if(inst_sym != nullptr)
        {
          auto found = cpp_typecheck.cpp_scopes.get_root_scope().lookup(
            inst_sym->base_name,
            cpp_scopet::RECURSIVE,
            cpp_idt::id_classt::TEMPLATE);
          for(const auto &f : found)
          {
            const symbolt *cand =
              cpp_typecheck.symbol_table.lookup(f->identifier);
            if(
              cand != nullptr && cand->type.get_bool(ID_is_template) &&
              to_cpp_declaration(cand->type)
                .type()
                .get(ID_specialization_of)
                .empty())
              id_set.insert(f);
          }
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
  // classes are NOT considered (ADL is suppressed).  Without this an
  // unqualified
  // member call such as `find(x)` inside a member function -- which ordinary
  // lookup resolves to `this->find` -- would also pull in a same-named member
  // of
  // the argument's class (e.g. `std::basic_string::find` when `x` is a
  // `std::string`), making the call ambiguous.  Operators are excluded: they
  // use
  // the separate [over.match.oper] candidate-gathering, which always includes
  // ADL-found non-member operators regardless of any member operator.
  // A member function TEMPLATE's scope entry carries no class_identifier;
  // it is a class member all the same (its parent scope is the class), so
  // `zip<b>(x)` inside ranget<It>::zip(containert &) must not also collect
  // ranget<J>::zip from the argument's class -- that made the call to the
  // sibling overload ambiguous with the same-named member of the argument's
  // class instance.
  bool ordinary_lookup_found_member = false;
  for(const auto *id : id_set)
  {
    if(
      !id->class_identifier.empty() ||
      (id->has_parent() && id->get_parent().is_class()))
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
  // N5008 [temp.res.general]/1 + [temp.dep.candidate]/1 (two-phase name
  // lookup): when a DEPENDENT unqualified call is re-looked-up during
  // instantiation, the ordinary-lookup component comprises only
  // declarations visible at the TEMPLATE DEFINITION point; only ADL is
  // performed at the point of instantiation.  CBMC resolves at
  // instantiation time against the full symbol table, so a function
  // declared AFTER the template wrongly becomes a candidate -- selecting
  // a partial specialization whose `decltype(f(...))` pattern names a
  // later-declared `f` (libc++ pointer_traits' _HasToAddress /
  // to_address ordering; KNOWNBUG cpp20_spec_match_two_phase).
  //
  // Approximate the definition-point rule by declaration ORDER within
  // the same file: a candidate declared later in the SAME file as the
  // use cannot have been visible at the use's lexical point (valid
  // programs require prior declaration for non-ADL unqualified calls).
  // Cross-file candidates are kept (header order is not modelled).
  // Restricted to SFINAE contexts (deduction / specialization
  // matching), where mis-added candidates flip selections silently;
  // ADL below re-adds instantiation-point candidates as [temp.point]
  // allows.
  if(
    !qualified && fargs.in_use && !fargs.has_object &&
    cpp_typecheck.two_phase_pattern_depth > 0 &&
    !source_location.get_file().empty())
  {
    const irep_idt use_file = source_location.get_file();
    const auto use_line_str = id2string(source_location.get_line());
    if(!use_line_str.empty())
    {
      const unsigned long use_line = std::stoul(use_line_str);
      for(auto it = id_set.begin(); it != id_set.end();)
      {
        const symbolt *cand_sym =
          cpp_typecheck.symbol_table.lookup((*it)->identifier);
        bool drop = false;
        if(
          cand_sym != nullptr && !cand_sym->location.get_file().empty() &&
          cand_sym->location.get_file() == use_file &&
          (cand_sym->type.id() == ID_code ||
           cand_sym->type.get_bool(ID_is_template)))
        {
          const auto cand_line_str = id2string(cand_sym->location.get_line());
          if(!cand_line_str.empty() && std::stoul(cand_line_str) > use_line)
            drop = true;
        }
        if(drop)
          it = id_set.erase(it);
        else
          ++it;
      }
    }
  }

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
      // Retry lookup after elaboration.  N5008 [class.member.lookup]: the
      // member may be INHERITED -- `is_convertible<...>::value`, declared
      // by the integral_constant base that the elaboration has just
      // attached -- so the retry must search the bases too (QUALIFIED),
      // not the class's own entries only.
      id_set = cpp_typecheck.cpp_scopes.current_scope().lookup(
        base_name, cpp_scopet::QUALIFIED);
    }

    // N5008 [basic.lookup.qual] + [class.static.data]: the member may
    // exist as a SYMBOL even when the instance's scope-tree entry is
    // missing it -- a static data member whose symbol was created by
    // the lazy-member machinery without a matching scope registration
    // (the `_Pred::value` of libc++'s __and_helper signature, where
    // `_Pred` arrives as a textually-spliced instance tag:
    // `tag-_IsFancyPointer<RI>::value` resolved fine as a symbol but
    // not through the scope tree, so _And<...> collapsed to
    // false_type and std::__to_address(reverse_iterator) lost its
    // overloads).  Fall back to the symbol table directly: member
    // symbols are named after the instance WITHOUT the `tag-` marker.
    if(id_set.empty())
    {
      std::string scope_str = id2string(cur.identifier);
      // strip the OUTERMOST `tag-` (angle-bracket depth 0); inner
      // occurrences belong to template-argument instance tags and are
      // part of the member symbol's name
      {
        int depth = 0;
        for(std::size_t i = 0; i + 4 <= scope_str.size(); ++i)
        {
          if(scope_str[i] == '<')
            ++depth;
          else if(scope_str[i] == '>')
            --depth;
          else if(depth == 0 && scope_str.compare(i, 4, "tag-") == 0)
          {
            scope_str.erase(i, 4);
            break;
          }
        }
      }
      const irep_idt member_id = scope_str + "::" + id2string(base_name);
      const symbolt *member_sym = cpp_typecheck.symbol_table.lookup(member_id);
      if(
        member_sym != nullptr && !member_sym->is_type &&
        member_sym->is_static_lifetime)
      {
        // N5008 [temp.inst]/3 + [expr.const]: using the member in a
        // constant context instantiates its initializer.  The lazy
        // machinery may have left the raw dependent expression (the
        // `_HasArrow<...>::value || _HasToAddress<...>::value` of
        // _IsFancyPointer); evaluate it now, under a SFINAE guard in
        // the member's class scope, so consumers see the constant.
        // Return the member directly: registering a scope entry here
        // would mutate the scope's id container while outer resolve
        // frames may hold live iterators into it.
        //
        // The member's initializer may be only PARTIALLY evaluated at
        // this point (the class is mid-elaboration; the use that got
        // us here is the [temp.inst]/9 trigger).  For the disjunction /
        // conjunction initializers of the detection-trait idiom
        // (`_HasArrow<...>::value || _HasToAddress<...>::value`,
        // libc++ _IsFancyPointer), the short-circuit rules
        // ([expr.log.or]/1, [expr.log.and]/1) let a determinate
        // constant operand decide the value without evaluating the
        // remaining (still-unresolved) operand -- exactly what a
        // conforming implementation's constant evaluator does.  Fold
        // structurally; no typechecking (re-entering the typechecker
        // mid-elaboration corrupts the in-flight class).
        const symbolt *resolved = cpp_typecheck.symbol_table.lookup(member_id);
        if(resolved != nullptr)
        {
          exprt folded = resolved->value;
          std::function<void(exprt &)> fold_sc = [&](exprt &e)
          {
            if(e.id() != ID_or && e.id() != ID_and)
              return;
            for(auto &op : e.operands())
              fold_sc(op);
            const bool is_or = e.id() == ID_or;
            for(const auto &op : e.operands())
            {
              if(!op.is_constant())
                continue;
              const bool v = !to_constant_expr(op).is_zero();
              if(is_or == v)
              {
                const irep_idt tid = e.type().id();
                if(
                  tid == ID_c_bool || tid == ID_signedbv ||
                  tid == ID_unsignedbv)
                {
                  e = from_integer(v ? 1 : 0, e.type());
                }
                else
                {
                  e = v ? static_cast<exprt>(true_exprt{})
                        : static_cast<exprt>(false_exprt{});
                }
                return;
              }
            }
          };
          if(folded.is_not_nil() && !folded.is_constant())
          {
            fold_sc(folded);
            simplify(folded, cpp_typecheck);
          }
          if(folded.is_constant())
          {
            exprt result = folded;
            result.add_source_location() = source_location;
            return result;
          }
          exprt result = cpp_symbol_expr(*resolved);
          result.add_source_location() = source_location;
          return result;
        }
      }
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
      // See the note above: a scope entry may exist without its symbol
      // (member of a class-template instance still being elaborated).
      // It cannot be a template candidate here; drop it rather than
      // asserting in namespacet::lookup.
      if(!cpp_typecheck.symbol_table.has_symbol(id))
      {
        it = id_set.erase(it);
        continue;
      }
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
          !cpp_typecheck.skip_typechecking_elaborate &&
          cpp_typecheck.elaborate_on_naming)
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

      if(
        !cpp_typecheck.skip_typechecking_elaborate &&
        cpp_typecheck.elaborate_on_naming)
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
            // N5008 [basic.lookup.unqual]/1: the arguments are expressions
            // at the point of use, not in the template's scope -- type-check
            // them in the original scope, as for class and function
            // templates (`std::in_place_index<__accepted_index<_Tp>>` in
            // std::variant's converting constructor names a member of the
            // class, invisible from namespace std).
            cpp_template_args_tct tc_args;
            try
            {
              cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);
              cpp_typecheck.cpp_scopes.go_to(*original_scope);
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
            // N5008 [temp.pre]/1, [basic.pre]/7: an instance of a
            // variable template of class or array type names an object --
            // `__v<_ArrayExtent>' (libstdc++ 16's span constructor) is an
            // lvalue of type integral_constant<...> whose conversion
            // function is called on it.  Keep the symbol, as
            // convert_identifier does for such constexpr variables;
            // substituting the initializer value left no object to call
            // the member function on and the constructor was dropped.
            const typet &inst_type = inst_sym.type;
            if(
              inst_sym.value.is_not_nil() &&
              (inst_type.id() == ID_struct_tag ||
               inst_type.id() == ID_union_tag || inst_type.id() == ID_array))
            {
              exprt object = cpp_symbol_expr(inst_sym);
              object.add_source_location() = source_location;
              identifiers.push_back(object);
              handled_variable_template = true;
            }
            // The instantiated symbol is a constexpr variable.
            // Return its value, evaluating any remaining constexpr
            // function calls.
            else if(inst_sym.value.is_not_nil())
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

  // N5008 [temp.over]/1: a function template contributes the
  // specialization that template argument deduction synthesizes for THIS
  // call, or nothing if deduction fails.  A specialization instantiated
  // for an earlier call (a member template's specialization is recorded
  // among the class's components, marked #fn_template_type) is not a
  // candidate of its own: offered here, it made `S(tup<int>)' viable for
  // a `tup<char, char>' argument through tup's converting constructor
  // template, although deduction of `S(tup<A>)' fails.  When it is
  // viable, deduction from its template synthesizes it again.  Removed
  // before the exact-match phase too: checking it there tried conversions
  // of the arguments to its parameter types, which instantiated (and
  // dropped) unrelated constructor templates (libc++'s tuple<X &&> from
  // tuple<>).  Only when a template is among the candidates.
  bool has_template_candidate = false;
  for(const auto &id : identifiers)
  {
    if(id.type().get_bool(ID_is_template))
      has_template_candidate = true;
  }
  const auto remove_earlier_specializations =
    [this, has_template_candidate](resolve_identifierst &candidates)
  {
    if(!has_template_candidate)
      return;
    candidates.erase(
      std::remove_if(
        candidates.begin(),
        candidates.end(),
        [this](const exprt &e)
        {
          if(e.id() != ID_symbol)
            return false;
          const symbolt *sym = cpp_typecheck.symbol_table.lookup(
            to_symbol_expr(e).get_identifier());
          return sym != nullptr &&
                 sym->type.find(irep_idt{"#fn_template_type"}).is_not_nil();
        }),
      candidates.end());
  };

  // We disambiguate functions
  resolve_identifierst new_identifiers = identifiers;

  remove_templates(new_identifiers);
  remove_earlier_specializations(new_identifiers);

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
    remove_earlier_specializations(new_identifiers);

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
        remove_earlier_specializations(new_identifiers);
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
      remove_earlier_specializations(new_identifiers);
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
} // NOLINT(readability/fn_size)

/// N5008 [temp.type]/1, [dcl.fct]/5: the function type \p code with its
/// parameters in converted form: a written `void(int)' keeps them as
/// cpp_declaration, `decltype(cb)' and deduced types have `parameter's.
/// (Parameter names and default arguments are #-attributes, which
/// comparison ignores.)
typet cpp_typecheck_resolvet::canonical_function_type(const typet &code)
{
  typet result = code;
  cpp_typecheck.convert_parsed_parameters(to_code_type(result));
  return result;
}

/// N5008 [temp.deduct.type]/9: a trailing pack expansion P_i of a partial
/// specialization's argument list whose pattern is not a bare pack (`const Z
/// &...') is compared with each remaining argument of A; each comparison
/// deduces the next element of every template parameter pack that occurs in
/// the pattern (`S<T1, const Z &...>' against `S<int, const int &, const int
/// &>' deduces Z = {int, int}).  Records the packs in the template map; a
/// failed comparison leaves the pack unassigned.
void cpp_typecheck_resolvet::deduce_trailing_type_pack_pattern(
  const typet &pattern_with_ellipsis,
  const template_typet &template_type,
  const cpp_template_args_tct &arguments,
  std::size_t first)
{
  typet pattern = pattern_with_ellipsis;
  pattern.remove(ID_ellipsis);
  // the type parameter packs of the specialization that occur in the pattern
  std::vector<irep_idt> packs;
  for(const auto &parameter : template_type.template_parameters())
  {
    if(!parameter.get_bool(ID_ellipsis) || parameter.id() != ID_type)
      continue;
    const irep_idt &id = parameter.type().get(ID_identifier);
    std::string short_name = id2string(id);
    const auto sep = short_name.rfind("::");
    if(sep != std::string::npos)
      short_name = short_name.substr(sep + 2);
    bool occurs = false;
    std::function<void(const irept &)> walk = [&](const irept &n)
    {
      if(n.id() == ID_name && n.get(ID_identifier) == short_name)
        occurs = true;
      for(const auto &sub : n.get_sub())
        walk(sub);
      for(const auto &named : n.get_named_sub())
        walk(named.second);
    };
    walk(pattern);
    if(occurs)
      packs.push_back(id);
  }
  if(packs.empty())
    return;
  auto &map = cpp_typecheck.template_map;
  std::map<irep_idt, std::vector<typet>> elements;
  for(std::size_t j = first; j < arguments.arguments().size(); ++j)
  {
    const exprt &argument = arguments.arguments()[j];
    if(argument.id() != ID_type)
      return; // a value cannot match a type pattern
    for(const auto &pack : packs)
      map.type_map[pack] = typet{ID_unassigned};
    guess_template_args(pattern, argument.type());
    for(const auto &pack : packs)
    {
      const typet &deduced = map.type_map[pack];
      if(deduced.id() == ID_unassigned || deduced.is_nil())
        return;
      elements[pack].push_back(deduced);
    }
  }
  for(const auto &pack : packs)
  {
    std::vector<typet> &elems = elements[pack];
    // as for a bare pack: the front element is the scalar convenience
    // binding build_template_args reads
    map.set_pack_size(pack, elems.size());
    if(!elems.empty())
      map.type_map[pack] = elems.front();
    map.pack_args_map[pack] = std::move(elems);
  }
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
      resolve_pattern_scope(cpp_name, base_name, template_args);

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

    // N5008 [temp.deduct.type]/5.1: the nested-name-specifier of a type
    // that was specified using a qualified-id is a non-deduced context --
    // `typename enable_if<is_conv<X&&, ...>>::type` (the expansion of
    // libstdc++'s _Require<> in __common_ref_impl's rvalue partial
    // specialization) deduces nothing about X.  Resolving it here, with the
    // specialization's parameters still unassigned, evaluated the
    // constraint on unbound names as a hard error, aborting the matching
    // of every sibling specialization.
    const bool template_args_on_qualifier = [&]() -> bool
    {
      bool seen_args = false;
      for(const auto &sub : cpp_name.get_sub())
      {
        if(sub.id() == ID_template_args)
          seen_args = true;
        else if(sub.id() == ID_scope_resolution && seen_args)
          return true;
      }
      return false;
    }();
    if(template_args_on_qualifier)
      return;

    if(cpp_name.has_template_args())
    {
      if(!guess_template_args_via_alias(cpp_name, desired_type))
        guess_template_args_template_id(cpp_name, desired_type);
    }
    else
      guess_template_args_simple_name(cpp_name, desired_type);
  }
  else
    guess_template_args_compound(template_type, desired_type);
}

/// The alias-template step of guess_template_args for a template-id
/// pattern: N5008 [temp.alias]/2 -- when the name is an alias template,
/// expand it and deduce against its underlying type.
/// \return true when the pattern was an alias template and deduction went
///   through its expansion; false when the name is not an alias
bool cpp_typecheck_resolvet::guess_template_args_via_alias(
  const cpp_namet &cpp_name,
  const typet &desired_type)
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
        resolve_pattern_scope(cpp_name, qual_base_name, qual_template_args);
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
        const cpp_declarationt &alias_decl = to_cpp_declaration(sym->type);
        const cpp_declaratort &alias_declarator =
          alias_decl.declarators().front();
        typet alias_type = alias_declarator.merge_type(alias_decl.type());
        cpp_convert_plain_type(alias_type, cpp_typecheck.get_message_handler());

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
        for(std::size_t i = 0; i < alias_params.size() && i < targs.size(); ++i)
        {
          // The targ is a cpp_name referencing the function
          // template's parameter. We need to substitute the
          // alias param name in alias_type with this cpp_name.
          const irept &targ = targs[i];
          irept targ_type =
            targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
          if(targ_type.id() == ID_type)
            targ_type = targ_type.find(ID_type);
          // Substitutable argument shapes: a plain name and a
          // cv-qualified name (`const _Tp`, libc++'s
          // __enable_if_tuple_size_imp pattern).  N5008
          // [temp.alias]/2: the alias-id is equivalent to the
          // substituted defining-type-id -- including the
          // argument's cv-qualifiers; dropping them here left
          // the alias body's parameter name in place, which then
          // collided with the SPECIALIZATION's identically-named
          // parameter and deduced it without const, see
          // strict_cv_deduction.
          // A TYPE parameter's argument must itself be a type
          // spelling (a plain or cv-qualified name).  A NON-TYPE
          // parameter's argument is an EXPRESSION of arbitrary
          // shape -- e.g. the `!__has_construct<...>::value`
          // constraint argument of libc++ allocator_traits'
          // fallback `construct` overload; N5008 [temp.alias]/2
          // makes the alias-id equivalent to the substituted
          // defining-type-id for ANY argument shape.  Skipping
          // the substitution left the alias's own parameter name
          // (`_Bp`) in the body, whose typecheck then failed and
          // discarded BOTH construct overloads (the call became
          // unresolvable and the enclosing body was dropped:
          // the vector push_back
          // __uninitialized_allocator_move_if_noexcept shape).
          const bool param_is_type = alias_params[i].id() == ID_type;
          if(
            param_is_type && targ_type.id() != ID_cpp_name &&
            targ_type.id() != ID_merged_type)
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
            std::string id = id2string(alias_params[i].get(ID_identifier));
            if(id.empty())
              id = id2string(alias_params[i].type().get(ID_identifier));
            const auto pos = id.rfind("::");
            alias_param_base =
              irep_idt{pos != std::string::npos ? id.substr(pos + 2) : id};
          }
          if(alias_param_base.empty())
            continue;

          // Find the alias param name in alias_type and replace
          std::function<void(irept &)> subst;
          subst = [&](irept &t)
          {
            if(t.id() == ID_cpp_name)
            {
              const cpp_namet &n = to_cpp_name(static_cast<const typet &>(t));
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
        return true;
      }
    }
  }
  return false;
}

/// N5008 [temp.deduct.type]/9: each argument Pi of P is compared with the
/// corresponding argument Ai of A.  When the class template's last
/// parameter is a pack and P contains no pack expansion, P's arguments
/// correspond to A's one to one: `tup<A>' does not match `tup<char, char>'
/// or `tup<>' (the deduced A would not be identical to A,
/// [temp.deduct.call]/4).  Without this check the remaining arguments were
/// ignored and the candidate was made viable by a converting constructor.
/// \param instance_type: the type of A's class symbol
/// \param targs: P's template arguments
/// \param inst_arguments: A's template arguments
/// \return whether deduction fails for that reason
static bool pack_argument_count_differs(
  const typet &instance_type,
  const irept::subt &targs,
  const exprt::operandst &inst_arguments)
{
  const irept &class_template = instance_type.find(ID_C_template);
  const irept::subt &class_parameters =
    class_template.find(ID_template_parameters).get_sub();
  for(const auto &targ : targs)
  {
    const irept &t = targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
    if(targ.get_bool(ID_ellipsis) || t.get_bool(ID_ellipsis))
      return false;
  }
  if(
    class_parameters.empty() ||
    !class_parameters.back().get_bool(ID_ellipsis) ||
    targs.size() + 1 < class_parameters.size())
  {
    return false;
  }
  // the zero-length-pack sentinel (an empty type) is not an argument
  std::size_t a_count = 0;
  for(const auto &a : inst_arguments)
  {
    if(!(a.id() == ID_type && a.type().id() == ID_empty))
      ++a_count;
  }
  return a_count != targs.size();
}

/// The template arguments of the class template specialization of type
/// \p instance_type that P's arguments \p targs are deduced from: the
/// primary-relative ID_full_template_args recorded when the instance was
/// created, else ID_C_template_arguments.
/// \return nullptr if there are none, or if deduction fails by
///   pack_argument_count_differs
static const exprt::operandst *deducible_instance_arguments(
  const typet &instance_type,
  const irept::subt &targs)
{
  const irept &full_inst_args = instance_type.find(ID_full_template_args);
  const irept &inst_args = full_inst_args.is_not_nil()
                             ? full_inst_args
                             : instance_type.find(ID_C_template_arguments);
  if(inst_args.is_nil())
    return nullptr;
  const exprt::operandst &arguments =
    static_cast<const cpp_template_args_tct &>(inst_args).arguments();
  if(pack_argument_count_differs(instance_type, targs, arguments))
    return nullptr;
  return &arguments;
}

/// guess_template_args for a template-id pattern `C<args...>' against a
/// class template specialization ([temp.deduct.type]/8-9, with the
/// derived-to-base step of [temp.deduct.call]/4.3): each argument of the
/// pattern is matched against the corresponding argument of the
/// specialization (or of a base class that is one).
void cpp_typecheck_resolvet::guess_template_args_template_id(
  const cpp_namet &cpp_name,
  const typet &desired_type)
{
  // the pattern as a type, for the recursive deductions below
  const typet &pattern =
    static_cast<const typet &>(static_cast<const irept &>(cpp_name));
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
      const irept &t = targ.id() == ID_ambiguous ? targ.find(ID_type) : targ;
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
        // N5008 [temp.deduct]/5, [temp.arg.explicit]/7: only the parameters
        // of the template being deduced are poisoned; a parameter of the
        // enclosing class (C of `sv<C>' in a member template of fstr<C>) is
        // bound already and does not participate -- the argument is then
        // converted to the parameter type
        if(
          !current_deduction_parameters.empty() &&
          current_deduction_parameters.count(id_ptr->identifier) == 0)
        {
          continue;
        }
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

  // N5008 [temp.deduct.call]/4.3 with [temp.inst]/2: deducing from A's
  // BASE CLASSES needs A complete; the argument's class template
  // specialization is instantiated here if it has only been named so far
  // (`Derived<int> &__d' as a parameter, then `get_head(__d)').
  cpp_typecheck.elaborate_class_template(desired_type);
  const symbolt *desired_sym = cpp_typecheck.symbol_table.lookup(desired_id);
  if(desired_sym == nullptr)
  {
    mark_targs_conflicting();
    return;
  }

  // Check if it was instantiated from a template.  N5008
  // [temp.deduct.type]: deduction against a class-template
  // specialization needs only the instance's template ARGUMENTS,
  // not a completed definition -- an instance of a template that
  // is only forward-declared (`template <class, class> struct
  // __tree_node;`, libc++'s <__tree> node types) records
  // full_template_args but never ID_C_template, and rejecting it
  // here left the pattern `__tree_node<_Tp, _VoidPtr>` undeduced
  // (its parameters nil), failing the enclosing declaration
  // ("symbol '__pair1_' is unknown", the std::set shape).
  if(
    desired_sym->type.find(ID_C_template).is_nil() &&
    desired_sym->type.find(ID_full_template_args).is_nil() &&
    desired_sym->type.find(ID_C_template_arguments).is_nil())
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
          if(base_type.id() != ID_struct_tag && base_type.id() != ID_union_tag)
            continue;
          const irep_idt base_id =
            base_type.id() == ID_struct_tag
              ? to_struct_tag_type(base_type).get_identifier()
              : to_union_tag_type(base_type).get_identifier();
          const symbolt *base_sym = cpp_typecheck.symbol_table.lookup(base_id);
          if(base_sym == nullptr || base_sym->base_name != dtb_tmpl_name)
            continue;
          const bool saved_dab = deducing_against_base;
          deducing_against_base = true;
          guess_template_args(pattern, base_type);
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
          if(base_type.id() != ID_struct_tag && base_type.id() != ID_union_tag)
            continue;
          const irep_idt base_id =
            base_type.id() == ID_struct_tag
              ? to_struct_tag_type(base_type).get_identifier()
              : to_union_tag_type(base_type).get_identifier();
          if(!bases_seen.insert(base_id).second)
            continue;
          const symbolt *base_sym = cpp_typecheck.symbol_table.lookup(base_id);
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
          guess_template_args(pattern, base_type);
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
  const exprt::operandst *const inst_arguments_ptr =
    deducible_instance_arguments(desired_sym->type, targs);
  if(inst_arguments_ptr == nullptr)
  {
    mark_targs_conflicting();
    return;
  }
  const auto &inst_arguments = *inst_arguments_ptr;

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
    for(std::size_t i = 0; i < targs.size() && i < inst_arguments.size(); ++i)
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
        const typet &base_type = static_cast<const typet &>(base.find(ID_type));
        if(base_type.id() != ID_struct_tag && base_type.id() != ID_union_tag)
          continue;
        const irep_idt base_id =
          base_type.id() == ID_struct_tag
            ? to_struct_tag_type(base_type).get_identifier()
            : to_union_tag_type(base_type).get_identifier();
        const symbolt *base_sym = cpp_typecheck.symbol_table.lookup(base_id);
        if(base_sym == nullptr || base_sym->base_name != tmpl_bn)
          continue;
        const bool saved_dab = deducing_against_base;
        deducing_against_base = true;
        guess_template_args(pattern, base_type);
        deducing_against_base = saved_dab;
        return; // dispatched to the base subobject
      }
      // No base is a specialization of the same template: A is genuinely
      // not (derived from) a specialization of P.
      mark_targs_conflicting();
      return;
    }
  }

  // N5008 [temp.deduct.type]/1, [temp.deduct.call]/4-5: a TYPE argument of P
  // that does not involve the template parameters being deduced (`wchar_t'
  // in `os<wchar_t, T>') is not deduced but must be identical to A's
  // corresponding argument; otherwise A is not a specialization matching P
  // (only a base of A may be, [temp.deduct.call]/4.3), and deduction fails.
  // Deducing T from the other arguments regardless made the substituted
  // parameter type os<wchar_t, tr<char>> & and instantiated that class
  // (libc++'s deleted `operator<<(basic_ostream<wchar_t, _Traits> &,
  // char16_t)' considered for an ostringstream).
  {
    const auto mentions_template_parameter = [&](const irept &arg)
    {
      std::function<bool(const irept &)> walk = [&](const irept &n) -> bool
      {
        if(n.id() == ID_name && !n.get(ID_identifier).empty())
        {
          for(const auto *p : cpp_typecheck.cpp_scopes.current_scope().lookup(
                n.get(ID_identifier), cpp_scopet::RECURSIVE))
          {
            if(p->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER)
              return true;
          }
        }
        if(n.id() == ID_template_parameter_symbol_type)
          return true;
        for(const auto &sub : n.get_sub())
          if(walk(sub))
            return true;
        for(const auto &ns : n.get_named_sub())
          if(ns.first != ID_C_source_location && walk(ns.second))
            return true;
        return false;
      };
      return walk(arg);
    };
    bool fixed_type_mismatch = false;
    for(std::size_t i = 0; i < targs.size() && i < inst_arguments.size(); ++i)
    {
      const irept &tn = targs[i];
      if(tn.get_bool(ID_ellipsis) || tn.find(ID_type).get_bool(ID_ellipsis))
        break;
      if(tn.id() != ID_type || inst_arguments[i].id() != ID_type)
        continue;
      if(mentions_template_parameter(tn.find(ID_type)))
        continue;
      // the pattern is in parsed form (`wchar_t'); convert it
      typet pattern_arg = static_cast<const typet &>(tn.find(ID_type));
      try
      {
        cpp_convert_plain_type(
          pattern_arg, cpp_typecheck.get_message_handler());
      }
      catch(...)
      {
        continue;
      }
      // only plain built-in types: their identity is unambiguous here
      const irep_idt &pid = pattern_arg.id();
      if(
        pid != ID_signedbv && pid != ID_unsignedbv && pid != ID_bool &&
        pid != ID_c_bool && pid != ID_floatbv && pid != ID_empty)
      {
        continue;
      }
      const typet &a = inst_arguments[i].type();
      if(
        a.id() != pid || a.get(ID_width) != pattern_arg.get(ID_width) ||
        a.get(ID_C_c_type) != pattern_arg.get(ID_C_c_type) ||
        a.get_bool(ID_C_constant) != pattern_arg.get_bool(ID_C_constant) ||
        a.get_bool(ID_C_volatile) != pattern_arg.get_bool(ID_C_volatile))
      {
        fixed_type_mismatch = true;
        break;
      }
    }
    if(fixed_type_mismatch)
    {
      const irep_idt tmpl_bn = cpp_name.get_base_name();
      for(const auto &base : desired_sym->type.find(ID_bases).get_sub())
      {
        const typet &base_type = static_cast<const typet &>(base.find(ID_type));
        if(base_type.id() != ID_struct_tag)
          continue;
        const symbolt *base_sym = cpp_typecheck.symbol_table.lookup(
          to_struct_tag_type(base_type).get_identifier());
        if(base_sym == nullptr || base_sym->base_name != tmpl_bn)
          continue;
        const bool saved_dab = deducing_against_base;
        deducing_against_base = true;
        guess_template_args(pattern, base_type);
        deducing_against_base = saved_dab;
        return;
      }
      mark_targs_conflicting();
      return;
    }
  }

  // N5008 [temp.deduct.type]/17: if P has a form that contains `<i>`
  // where `i` names a non-type template parameter of the template being
  // deduced, and the type of `i` differs from the type of the
  // corresponding template parameter of the template named by P,
  // deduction fails -- `template <long... U> impl(indices<U...>)`
  // called with `indices<unsigned long...>` has no viable
  // constructor (g++/clang: "deduced non-type template argument does
  // not have the same type as the corresponding template parameter").
  // Both sides are DECLARED parameter types, so the deduced values'
  // representation plays no part.  Dependent or unresolvable types are
  // not compared.
  const irept &named_template_irep = desired_sym->type.find(ID_C_template);
  const template_typet *named_template_type =
    named_template_irep.is_nil()
      ? nullptr
      : static_cast<const template_typet *>(&named_template_irep);
  auto nontype_kind_mismatch =
    [&](const irept &pattern_arg, std::size_t named_index) -> bool
  {
    if(named_template_type == nullptr)
      return false;
    const irept &pa = pattern_arg.id() == ID_ambiguous
                        ? pattern_arg.find(ID_type)
                        : pattern_arg;
    if(pa.id() != ID_cpp_name)
      return false;
    const cpp_namet &pn = to_cpp_name(static_cast<const typet &>(pa));
    if(pn.is_qualified() || pn.has_template_args())
      return false;
    irep_idt pattern_param;
    for(const auto *id_ptr : cpp_typecheck.cpp_scopes.current_scope().lookup(
          pn.get_base_name(), cpp_scopet::RECURSIVE))
    {
      if(
        id_ptr->id_class == cpp_idt::id_classt::TEMPLATE_PARAMETER &&
        current_deduction_nontype_types.count(id_ptr->identifier) != 0)
      {
        pattern_param = id_ptr->identifier;
      }
    }
    if(pattern_param.empty())
      return false;
    // [temp.deduct.type]/20 Example 13: `f<1>(a)` is OK -- an explicitly
    // specified argument is not deduced, so its parameter's type does not
    // take part.  It is already bound (not `unassigned`) here.
    {
      const auto eit = cpp_typecheck.template_map.expr_map.find(pattern_param);
      if(
        eit != cpp_typecheck.template_map.expr_map.end() &&
        eit->second.id() != ID_unassigned)
      {
        return false;
      }
      if(
        eit == cpp_typecheck.template_map.expr_map.end() &&
        cpp_typecheck.template_map.pack_expr_map.count(pattern_param) != 0)
      {
        return false;
      }
    }
    const auto &named_params = named_template_type->template_parameters();
    // the pattern parameter may be a pack matching the trailing run of
    // the named template's parameters; compare against the parameter at
    // named_index, or the named template's own trailing pack
    const template_parametert *named_param = nullptr;
    if(named_index < named_params.size())
      named_param = &named_params[named_index];
    else if(!named_params.empty() && named_params.back().get_bool(ID_ellipsis))
      named_param = &named_params.back();
    if(named_param == nullptr || named_param->id() == ID_type)
      return false;
    typet t_pattern = current_deduction_nontype_types.at(pattern_param);
    typet t_named = named_param->type();
    // A type spelled with a template parameter is dependent: not compared
    std::function<bool(const irept &)> names_cpp_name =
      [&](const irept &n) -> bool
    {
      if(n.id() == ID_cpp_name)
        return true;
      for(const auto &sub : n.get_sub())
        if(names_cpp_name(sub))
          return true;
      return false;
    };
    if(names_cpp_name(t_pattern) || names_cpp_name(t_named))
      return false;
    try
    {
      cpp_typecheck.typecheck_type(t_pattern);
      cpp_typecheck.typecheck_type(t_named);
    }
    catch(...)
    {
      return false;
    }
    const auto strip = [](typet t) -> typet
    {
      c_qualifierst{}.write(t);
      return t;
    };
    t_pattern = strip(t_pattern);
    t_named = strip(t_named);
    const auto is_arith = [](const typet &t)
    {
      return t.id() == ID_signedbv || t.id() == ID_unsignedbv ||
             t.id() == ID_bool || t.id() == ID_c_bool ||
             t.id() == ID_c_enum_tag;
    };
    return is_arith(t_pattern) && is_arith(t_named) && t_pattern != t_named;
  };

  // Match each template arg from the cpp_name against the
  // corresponding instantiation arg
  for(std::size_t i = 0; i < targs.size(); i++)
  {
    if(nontype_kind_mismatch(targs[i], i))
    {
      mark_targs_conflicting();
      return;
    }
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
        const cpp_namet &pn = to_cpp_name(static_cast<const typet &>(targ_t));
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
            pack_exprs.push_back(static_cast<const exprt &>(inst_arguments[j]));
        }

        cpp_typecheck.template_map.set_pack_size(
          pack_id, pack_elems.size() + pack_exprs.size());
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
          : static_cast<const typet &>(static_cast<const irept &>(targs[i]));
      guess_template_args(targ_type, inst_arguments[i].type());
    }
    else
    {
      guess_template_args(
        static_cast<const exprt &>(targs[i]), inst_arguments[i]);
    }
  }
}

/// guess_template_args for a plain name pattern: a template parameter is
/// bound to the desired type ([temp.deduct.type]/1); any other name deduces
/// nothing.
void cpp_typecheck_resolvet::guess_template_args_simple_name(
  const cpp_namet &cpp_name,
  const typet &desired_type)
{
  // template parameters aren't qualified
  if(!cpp_name.is_qualified())
  {
    irep_idt base_name;
    cpp_template_args_non_tct template_args;
    resolve_pattern_scope(cpp_name, base_name, template_args);

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
          // [expr.rel]/2: `T' deduced from `a == b' is bool
          t = cpp_bool_type(desired_type);
        }
        else
        {
          // Already assigned: N5008 [temp.deduct.type]/2 requires every
          // deduction of a parameter to yield the same type, cv-qualifiers
          // included (`T' from `T *' with `const char *' is `const char',
          // from `T' with `char' is `char').  The qualifiers are comments
          // of the irep, which operator== ignores, so compare them too.
          const typet &existing = t;
          const typet &incoming = desired_type;
          const bool same_cv = existing.get_bool(ID_C_constant) ==
                                 incoming.get_bool(ID_C_constant) &&
                               existing.get_bool(ID_C_volatile) ==
                                 incoming.get_bool(ID_C_volatile);
          // [temp.type]/1: a function type in parsed and in converted form
          // (`same<decltype(cb), void(int)>' against `same<A, A>')
          if(
            !same_cv ||
            (existing != incoming &&
             (existing.id() != ID_code || incoming.id() != ID_code ||
              canonical_function_type(existing) !=
                canonical_function_type(incoming))))
          {
            t.id(ID_unassigned); // mark as conflicting
          }
        }
      }
    }
  }
}

/// guess_template_args for the compound patterns ([temp.deduct.type]/8):
/// cv-qualified (merged) types, references, pointers (including pointers to
/// members), arrays and function types -- deduce from the corresponding
/// component of the desired type.
void cpp_typecheck_resolvet::guess_template_args_compound(
  const typet &template_type,
  const typet &desired_type)
{
  if(template_type.id() == ID_merged_type)
  {
    // Strip cv-qualifiers from the desired type when the merged_type
    // contains them, so that e.g. const T matched against const char
    // deduces T=char rather than T=const char.
    typet desired = desired_type;
    // `const volatile T' parses as merged_type(merged_type(volatile, const),
    // T): flatten nested merged types so each qualifier is checked
    // ([temp.deduct.type]/8) -- otherwise `const volatile T' deduced from
    // any argument, and partial ordering could not rank it above `const T'
    std::vector<typet> subtypes;
    std::function<void(const typet &)> flatten = [&](const typet &t)
    {
      if(t.id() == ID_merged_type)
      {
        for(const auto &sub : to_merged_type(t).subtypes())
          flatten(sub);
      }
      else
        subtypes.push_back(t);
    };
    flatten(template_type);
    // N5008 [basic.type.qualifier]/3: an array type whose elements are
    // cv-qualified has the cv-qualification of its elements, and "cv T"
    // with T an array type is the array of cv-qualified elements.  So
    // `const T' matched by `const char[3]' deduces T = char[3]: the
    // qualifier is checked on, and removed from, the innermost element
    // type (and the array nodes, which may carry a copy of it).
    const auto innermost_element = [](typet &t) -> typet &
    {
      typet *e = &t;
      while(e->id() == ID_array)
        e = &to_array_type(*e).element_type();
      return *e;
    };
    const auto has_qualifier = [&](const irep_idt &q)
    { return desired.get_bool(q) || innermost_element(desired).get_bool(q); };
    const auto remove_qualifier = [&](const irep_idt &q)
    {
      for(typet *e = &desired;; e = &to_array_type(*e).element_type())
      {
        e->remove(q);
        if(e->id() != ID_array)
          break;
      }
    };
    for(const auto &t : subtypes)
    {
      if(t.id() == ID_const)
      {
        // N5008 [temp.deduct.type]/8: in strict (partial-specialization
        // matching) mode, a cv-qualified pattern requires a
        // correspondingly qualified argument; `const T` does not match
        // a non-const type, so deduction fails (T stays unassigned and
        // the candidate is discarded by the has_unassigned() check).
        if(strict_cv_deduction && !has_qualifier(ID_C_constant))
          return;
        remove_qualifier(ID_C_constant);
      }
      else if(t.id() == ID_volatile)
      {
        if(strict_cv_deduction && !has_qualifier(ID_C_volatile))
          return;
        remove_qualifier(ID_C_volatile);
      }
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
    // [temp.deduct.type]/8 (P/A form list): in partial-specialization
    // matching (strict_cv_deduction contexts) a reference pattern `T&`
    // or `T&&` is matched only by a REFERENCE argument -- `decay_<T&>`
    // must not match `decay_<int*>` (stripping the `&` and deducing
    // T=int* wrongly selects the reference specialization, so
    // `decay_t_<int*>` resolved to `int`; the libc++
    // __to_address/__decay_t return-type shape).  Reference stripping
    // remains correct for function-call deduction ([temp.deduct.call]/3),
    // which does not set strict_cv_deduction.
    if(
      strict_cv_deduction && !is_reference(desired) &&
      !is_rvalue_reference(desired))
    {
      return; // reference pattern vs non-reference argument
    }
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
  else if(
    (template_type.id() == ID_pointer ||
     template_type.id() == ID_frontend_pointer) &&
    template_type.find(ID_to_member).is_not_nil())
  {
    // N5008 [temp.deduct.type]/8: the form `T C::*` -- a pointer to
    // member of a class named by a template parameter, deducing both the
    // member type and the class (`__result_of_memfun<_Res _Class::*,
    // _Arg, _Args...>`, the libstdc++ trait every std::bind / std::invoke
    // over a member function pointer resolves through).  A pointer
    // pattern without `to_member` never matched a pointer-to-member
    // argument's shape, so the primary (`__failure_type`) was chosen and
    // `std::bind(&S::f, &s, _1)` had no result type.
    if(
      desired_type.id() != ID_pointer ||
      desired_type.find(ID_to_member).is_nil())
      return; // a pointer-to-member pattern needs a pointer-to-member
    // the class: the pattern's nested-name-specifier keeps the parser's
    // trailing `::` component (typecheck_type pops it the same way)
    typet pattern_class =
      static_cast<const typet &>(template_type.find(ID_to_member));
    if(
      pattern_class.id() == ID_cpp_name && !pattern_class.get_sub().empty() &&
      pattern_class.get_sub().back().id() == ID_scope_resolution)
      pattern_class.get_sub().pop_back();
    guess_template_args(
      pattern_class,
      static_cast<const typet &>(desired_type.find(ID_to_member)));
    // the member type: for a member function the argument's code type
    // carries the implicit object parameter; deducing the whole code
    // type keeps the re-formed `_Res _Class::*` identical to the
    // argument (typecheck_type adds `this` only when absent)
    guess_template_args(
      to_type_with_subtype(template_type).subtype(),
      to_pointer_type(desired_type).base_type());
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
      // N5008 [temp.deduct.call]/3: if P is a forwarding reference
      // (an rvalue reference to a cv-unqualified template parameter,
      // here a bare cpp_name subtype) and the argument is an lvalue
      // (A arrives as `lvalue reference to A`), the whole reference
      // type is used for deduction: T&& vs int(&)[3] deduces
      // T = int(&)[3].  Only in call-style deduction; in
      // partial-specialization matching (strict_cv_deduction) the
      // reference kinds must match exactly, per the check below.
      if(
        !strict_cv_deduction && template_type.get_bool(ID_C_rvalue_reference) &&
        to_type_with_subtype(template_type).subtype().id() == ID_cpp_name &&
        desired_is_ref && !desired_type.get_bool(ID_C_rvalue_reference))
      {
        guess_template_args(
          to_type_with_subtype(template_type).subtype(), desired_type);
        return;
      }
      if(
        pattern_is_ref && desired_is_ref &&
        template_type.get_bool(ID_C_rvalue_reference) !=
          desired_type.get_bool(ID_C_rvalue_reference))
        return; // reference kinds differ -> deduction failure
      // [temp.deduct.type]/8: see the reference branch above -- in
      // partial-specialization matching a reference pattern requires a
      // reference argument.
      if(strict_cv_deduction && pattern_is_ref && !desired_is_ref)
        return;
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

        // N5008 [temp.deduct.type]/10: a function parameter pack `A...'
        // (the last parameter, [temp.param]/11) is deduced from each of
        // the remaining parameter types, as in the code-type branch below.
        // Only its first element was deduced and the pack never recorded,
        // so `R (&)(A...)' matched `int (&)(int, int)' as `int (&)(int)'
        // and lost to `T &' ([temp.spec.partial.match]).
        if(
          tp.id() == ID_cpp_declaration &&
          !to_cpp_declaration(tp).declarators().empty() &&
          to_cpp_declaration(tp).declarators().front().get_has_ellipsis())
        {
          deduce_function_parameter_pack(
            to_cpp_declaration(tp),
            desired_type,
            static_cast<std::size_t>(d_it - desired_params.begin()));
          break;
        }

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

  cpp_typecheck.template_map.set_pack_size(pack_id, pack_elems.size());
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
  // N5008 [expr.new]/1 + [temp.variadic]/5: a new-initializer's
  // expression-list is a pack-expansion context like a call's argument
  // list -- `decltype(::new(declval<void *>()) _Tp(declval<_Args>()...))',
  // the constraint of libc++'s std::construct_at.  An EMPTY _Args (the
  // `std::construct_at(p)' of basic_string::__begin_lifetime) must be
  // expanded to no initializer before the operand is type-checked; missed
  // here, the bare pack reference was rejected and the call found no
  // viable candidate.
  if(
    n.id() == ID_side_effect && n.get(ID_statement) == ID_cpp_new &&
    n.find(ID_initializer).is_not_nil())
  {
    for(const auto &a : n.find(ID_initializer).get_sub())
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

/// N5008 [temp.deduct]/5 + [temp.param]/11-14: after deduction, the
/// template parameters of \p cpp_declaration that remain unassigned in
/// \p template_args take their default template arguments, substituted with
/// the arguments deduced so far (a parameter pack that deduced empty is
/// recorded in \p pack_param_name / \p variadic_pack_empty).
/// \return false when a default argument's substitution fails (a deduction
///   failure, [temp.deduct]/8) -- the candidate is not viable
bool cpp_typecheck_resolvet::apply_default_template_arguments(
  const cpp_declarationt &cpp_declaration,
  const symbolt &template_symbol,
  const irept::subt &parameters,
  const irep_idt &member_class_tag,
  bool has_non_empty_pack,
  const std::vector<typet> &pack_deduced_types,
  std::size_t pack_expansion_size,
  cpp_template_args_tct &template_args,
  irep_idt &pack_param_name,
  bool &variadic_pack_empty)
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
  // A pack deduced from inside a parameter type (`const tup<U...> &') has
  // its elements in pack_args_map, and build_template_args may already
  // have spread them over the argument slots: count those, too
  // ([temp.deduct.type]/9).
  std::size_t deduced_pack_size = pack_expansion_size;
  if(!has_non_empty_pack && pack_param_index < params.size())
  {
    const auto deduced = cpp_typecheck.template_map.pack_args_map.find(
      params[pack_param_index].type().get(ID_identifier));
    if(
      deduced != cpp_typecheck.template_map.pack_args_map.end() &&
      args.size() == params.size() - 1 + deduced->second.size())
    {
      deduced_pack_size = deduced->second.size();
    }
  }
  const std::size_t pack_extra =
    (deduced_pack_size > 0 && pack_param_index < params.size())
      ? deduced_pack_size - 1
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
    const irep_idt pack_id = params[pack_param_index].type().get(ID_identifier);
    if(!pack_id.empty())
    {
      // N5008 [temp.deduct.type]/9, [temp.variadic]/8: a pack deduced from
      // inside a parameter type (`const tup<U...> &') is not a function
      // parameter pack -- pack_expansion_size counts only the latter --
      // and its elements are recorded in pack_args_map; sizeof...(U) in a
      // default template argument is their count
      // (`enable_if<sizeof...(U) == sizeof...(T), int> = 0', libc++'s
      // tuple(const tuple<_Up...> &)).
      std::size_t size = pack_expansion_size;
      if(!has_non_empty_pack)
      {
        const auto deduced =
          cpp_typecheck.template_map.pack_args_map.find(pack_id);
        if(deduced != cpp_typecheck.template_map.pack_args_map.end())
          size = deduced->second.size();
      }
      cpp_typecheck.template_map.set_pack_size(pack_id, size);
      // N5008 [temp.variadic]/5 + [temp.param]/14: a defaulted parameter
      // following the pack may also EXPAND it -- libstdc++'s
      // `_Bind::operator()<class... _Args, class _Result =
      // _Res_type<tuple<_Args...>>>`.  The single-pack flow records the
      // deduced elements in pack_args_map only after this loop (see the
      // multi-pack record below), so the default's `tuple<_Args...>`
      // found the size but no elements and fell back to the scalar
      // binding: `tuple<int>` for a two-argument call, and
      // `_Safe_tuple_element_t<1, tuple<int>>` (the second placeholder)
      // failed -- every std::bind with two or more placeholders had no
      // call operator.  Record the elements now, for this instance's
      // own pack only ([basic.scope.temp]/2) and only when there are
      // two or more (a single element keeps the established scalar
      // path; see the multi-pack note on evaluation order).
      // Only when a following parameter's DEFAULT ARGUMENT names the
      // pack: recording the elements unconditionally adds a second
      // same-spelled pack to the flat map while a constraint in a
      // following parameter's TYPE (`enable_if_t<ic<_UElements...>()>`,
      // the std::tuple converting constructor) is being evaluated, and
      // the callee's own same-named pack is then shadowed
      // (cpp17_tuple_get_two_pack_ctor_3elem).
      const std::string pack_short = [&]()
      {
        const std::string f = id2string(pack_id);
        const auto pos = f.rfind("::");
        return pos != std::string::npos ? f.substr(pos + 2) : f;
      }();
      std::function<bool(const irept &)> names_pack = [&](const irept &n)
      {
        if(n.id() == ID_name && id2string(n.get(ID_identifier)) == pack_short)
          return true;
        for(const auto &c : n.get_sub())
          if(names_pack(c))
            return true;
        for(const auto &c : n.get_named_sub())
          if(names_pack(c.second))
            return true;
        return false;
      };
      bool default_names_pack = false;
      for(std::size_t j = pack_param_index + 1; j < params.size(); ++j)
        if(
          params[j].has_default_argument() &&
          names_pack(params[j].default_argument()))
          default_names_pack = true;
      // a pack expansion of the pack in a template-argument list of a
      // following parameter's type or default (`enable_if<C<U...>::value,
      // int> = 0')
      std::function<bool(const irept &)> expands_in_targs = [&](const irept &n)
      {
        if(n.id() == ID_template_args)
        {
          for(const auto &a : n.find(ID_arguments).get_sub())
          {
            const irept &t = a.id() == ID_ambiguous ? a.find(ID_type) : a;
            if(
              (a.get_bool(ID_ellipsis) || t.get_bool(ID_ellipsis)) &&
              names_pack(t))
              return true;
          }
        }
        for(const auto &c : n.get_sub())
          if(expands_in_targs(c))
            return true;
        for(const auto &c : n.get_named_sub())
          if(expands_in_targs(c.second))
            return true;
        return false;
      };
      bool default_expands_pack_in_template_args = false;
      for(std::size_t j = pack_param_index + 1; j < params.size(); ++j)
      {
        if(
          params[j].has_default_argument() &&
          (expands_in_targs(params[j].type()) ||
           expands_in_targs(params[j].default_argument())))
        {
          default_names_pack = true;
          default_expands_pack_in_template_args = true;
        }
      }
      // A single element is recorded too when a default names the pack in a
      // template-argument list (`enable_u<U...>::value'): the scalar binding
      // does not expand `U...', which then named no argument at all.
      if(
        default_names_pack &&
        pack_deduced_types.size() == pack_expansion_size &&
        (pack_expansion_size >= 2 ||
         (pack_expansion_size == 1 && default_expands_pack_in_template_args)) &&
        cpp_typecheck.template_map.pack_args_map.find(pack_id) ==
          cpp_typecheck.template_map.pack_args_map.end())
      {
        cpp_typecheck.template_map.pack_args_map[pack_id] = pack_deduced_types;
      }
    }
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
          return false;
        }

        const std::string full_id = id2string(param.type().get(ID_identifier));
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
          // Keep the pack's slot as an explicit EMPTY type argument
          // (the convention instantiate_template drops for an empty
          // pack) rather than erasing it: erased, the trailing
          // parameters' arguments slid into the pack's position, and
          // the instance was built with e.g. `_Result`'s value as the
          // sole element of `_Args` -- `_Bind::operator()<int>(int&&)`
          // for a zero-argument call (libstdc++ std::bind).
          args[i] = exprt(ID_type, empty_typet());
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
          // N5008 [temp.inst]/1, [temp.dep.type]: a member template's
          // default template argument is evaluated in the context of the
          // class instance -- its parameters bound, including a partial
          // specialization's packs (`_ArgTypes...' in std::function's
          // `_Callable<_Functor>' constraint).  The bindings made when
          // this deduction started may have been swapped out by an
          // intervening alias or argument type-check; re-establish them
          // (non-overriding for the member's own deduced parameters).
          if(!member_class_tag.empty())
          {
            const symbolt *enclosing_sym =
              cpp_typecheck.symbol_table.lookup(member_class_tag);
            if(enclosing_sym != nullptr)
            {
              template_mapt with_class;
              cpp_typecheck.bind_class_instance_parameters(
                *enclosing_sym, with_class);
              for(const auto &tm : with_class.type_map)
                cpp_typecheck.template_map.type_map.emplace(
                  tm.first, tm.second);
              for(const auto &em : with_class.expr_map)
                cpp_typecheck.template_map.expr_map.emplace(
                  em.first, em.second);
              for(const auto &ps : with_class.pack_size_map)
                if(
                  cpp_typecheck.template_map.pack_size_map.find(ps.first) ==
                  cpp_typecheck.template_map.pack_size_map.end())
                  cpp_typecheck.template_map.set_pack_size(ps.first, ps.second);
              for(const auto &pa : with_class.pack_args_map)
                cpp_typecheck.template_map.pack_args_map.emplace(
                  pa.first, pa.second);
              for(const auto &pe : with_class.pack_expr_map)
                cpp_typecheck.template_map.pack_expr_map.emplace(
                  pe.first, pe.second);
            }
          }
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
            return false;
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
          // N5008 [expr.prim.fold]/2, [temp.deduct.general]/5: a fold over this
          // template's own pack in the default (`enable_if_t<(is_same_v<int,
          // U> && ...)>') expands over the deduced elements before the
          // default is checked; otherwise the C type checker's placeholder
          // made it `true'
          const auto expand_own_pack_folds = [&](irept &node)
          {
            if(pack_param_index >= params.size())
              return;
            const irep_idt pack_id =
              params[pack_param_index].type().get(ID_identifier);
            const auto deduced =
              cpp_typecheck.template_map.pack_args_map.find(pack_id);
            const auto size =
              cpp_typecheck.template_map.pack_size_map.find(pack_id);
            std::vector<exprt> elements;
            if(deduced != cpp_typecheck.template_map.pack_args_map.end())
            {
              for(const auto &t : deduced->second)
                elements.push_back(exprt{ID_type, t});
            }
            else if(!pack_deduced_types.empty())
            {
              for(const auto &t : pack_deduced_types)
                elements.push_back(exprt{ID_type, t});
            }
            if(
              !elements.empty() ||
              (size != cpp_typecheck.template_map.pack_size_map.end() &&
               size->second == 0))
            {
              const std::string pack_str = id2string(pack_id);
              const auto pos = pack_str.rfind("::");
              cpp_typecheckt::expand_folds_over_pack(
                node,
                pos != std::string::npos ? pack_str.substr(pos + 2) : pack_str,
                elements);
            }
          };
          auto eval_default = [&]() -> exprt
          {
            typet param_type = param.type();
            expand_own_pack_folds(param_type);
            cpp_typecheck.template_map.apply(param_type);
            cpp_typecheck.typecheck_type(param_type);
            // Use the default value
            exprt default_val = param.default_argument();
            expand_own_pack_folds(default_val);
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
              cpp_typecheck.template_map.pack_args_map[pack_id] = deduced_types;
            else
              cpp_typecheck.template_map.pack_expr_map[pack_id] = deduced_exprs;
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
          return false;
        }
      }
    }
  }
  return true;
}

/// The substitution step of function template argument deduction
/// ([temp.deduct.general]/5-6): with the deduced arguments bound in the
/// template map, substitute them into the function type \p function_type
/// and type-check it.
/// \param function_declarator: the template's declarator (its parameter list
///   names the function parameter pack, needed when the substitution
///   removed an empty pack)
/// \param fargs: the call's arguments (arity of a variadic call)
/// \param function_type: the function type, substituted in place
/// \return false on a substitution failure (SFINAE, [temp.deduct]/8) -- the
///   candidate is not viable; its diagnostics are discarded
bool cpp_typecheck_resolvet::substitute_function_type(
  const cpp_declaratort &function_declarator,
  const cpp_typecheck_fargst &fargs,
  typet &function_type)
{
  // Type-check the function type in a SFINAE context: suppress error
  // count so that substitution failures (e.g., enable_if with false
  // condition in the return type) are silently discarded.
  message_handlert &old_handler = cpp_typecheck.get_message_handler();
  const std::size_t sfinae_errors =
    old_handler.get_message_count(messaget::M_ERROR);
  // function parameter packs bound for the trailing return type
  std::vector<irep_idt> bound_parameter_packs;
  try
  {
    // N5008 [temp.variadic]/5: a function parameter pack (`A &&...a')
    // declares one parameter per element of A, the k-th of type A_k &&, and
    // a pack expansion naming it in a decltype operand of the trailing
    // return type (`decltype(f(static_cast<A &&>(a)...))') is expanded
    // element-wise, A_k and the k-th parameter in lockstep -- before the
    // element-wise substitution below replaces A by its first element.
    // The parameters are bound as for a requires-expression's parameter
    // pack (bind_requires_parameter_pack).
    if(function_type.has_subtype())
    {
      // The deduction replicated the pack's declaration once per element,
      // with the element types substituted and the same name `a' -- a name
      // a parameter-declaration-clause cannot otherwise declare twice
      // ([dcl.fct]/13); bind one symbol per such declaration.
      std::map<irep_idt, std::vector<typet>> replicated;
      std::vector<irep_idt> order;
      for(const auto &p : function_type.find(ID_parameters).get_sub())
      {
        if(p.id() != ID_cpp_declaration)
          continue;
        const auto &pdecl = static_cast<const cpp_declarationt &>(p);
        if(pdecl.declarators().empty())
          continue;
        const auto &pdtor = pdecl.declarators().front();
        const auto &pn = pdtor.name().get_sub();
        if(pn.empty() || pn.front().id() != ID_name)
          continue;
        const irep_idt &pname = pn.front().get(ID_identifier);
        if(replicated.find(pname) == replicated.end())
          order.push_back(pname);
        typet element_type = pdtor.merge_type(pdecl.type());
        element_type.remove(ID_ellipsis);
        replicated[pname].push_back(element_type);
      }
      for(const auto &pname : order)
      {
        const auto &types = replicated[pname];
        if(types.size() < 2)
          continue;
        std::vector<exprt> elements;
        for(const auto &t : types)
        {
          typet element_type = t;
          cpp_typecheck.typecheck_type(element_type);
          elements.push_back(
            cpp_typecheck.requires_parameter_pack_element(pname, element_type));
        }
        cpp_typecheck.requires_parameter_packs[pname] = std::move(elements);
        bound_parameter_packs.push_back(pname);
      }
      if(!bound_parameter_packs.empty())
      {
        cpp_typecheck.expand_requires_parameter_packs_in_type(
          to_type_with_subtype(function_type).subtype());
      }
    }
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

      // N5008 [temp.variadic]/7: a function parameter pack whose template
      // pack deduced EMPTY expands to zero parameters, and any expansion
      // referencing it in the trailing return type yields zero arguments.
      // Remove the parameter and strip its call-argument references from
      // the return type -- otherwise the decltype below sees the dead
      // name (`symbol 'args' is unknown`) and the candidate is dropped:
      // libc++ __perfect_forward's
      // `operator()(_Args&&... __args) -> decltype(_Op()(..., __args...))`
      // called with no arguments (the ranges views::take closure under
      // std::invoke).
      {
        auto short_of = [](const irep_idt &id) -> std::string
        {
          const std::string f = id2string(id);
          const auto pos = f.rfind("::");
          return pos != std::string::npos ? f.substr(pos + 2) : f;
        };
        // N5008 [basic.scope.temp]/2, [basic.scope.scope] (hiding): a
        // short name denotes the innermost declaration -- the most recently
        // bound pack of that name (template_mapt::generation_of).  An older
        // empty pack of another template with the same name (`_Args' of a
        // __perfect_forward_impl constructor template) does not make this
        // function's own one-element `_Args' empty (libc++'s __bind_back,
        // `-> decltype(... forward_as_tuple(__args...))').
        std::set<std::string> empty_pack_short_names;
        {
          std::map<std::string, std::pair<std::size_t, bool>> newest;
          const auto &map = cpp_typecheck.template_map;
          for(const auto &ps : map.pack_size_map)
          {
            const std::string sn = short_of(ps.first);
            const std::size_t g = map.generation_of(ps.first);
            auto it = newest.find(sn);
            if(it == newest.end() || g >= it->second.first)
              newest[sn] = {g, ps.second == 0};
          }
          for(const auto &n : newest)
            if(n.second.second)
              empty_pack_short_names.insert(n.first);
        }
        if(!empty_pack_short_names.empty())
        {
          std::vector<irep_idt> removed_param_names;
          // The pack parameter may ALREADY have been removed from
          // `function_type`'s parameter list by the earlier substitution
          // (its empty expansion), while its call-argument references in
          // the trailing return type remain.  Recover the parameter NAME
          // from the original declarator (mirroring instantiate_template's
          // recovery for the body strip).
          {
            const irept &ofparams =
              function_declarator.type().find(ID_parameters);
            for(const auto &opi : ofparams.get_sub())
            {
              if(opi.id() != ID_cpp_declaration)
                continue;
              const auto &opd = static_cast<const cpp_declarationt &>(opi);
              if(
                opd.declarators().empty() ||
                (!opd.declarators().front().get_bool(ID_ellipsis) &&
                 !opd.declarators().front().type().get_bool(ID_ellipsis) &&
                 !opd.type().get_bool(ID_ellipsis)))
                continue;
              const irept *t = &opd.type();
              while(t->id() != ID_cpp_name && !t->get_sub().empty())
                t = &t->get_sub().front();
              std::string own;
              if(t->id() == ID_cpp_name && !t->get_sub().empty())
                own = id2string(t->get_sub().front().get(ID_identifier));
              if(own.empty() || empty_pack_short_names.count(own) == 0)
                continue;
              for(const auto &nsub : opd.declarators().front().name().get_sub())
                if(nsub.id() == ID_name)
                  removed_param_names.push_back(nsub.get(ID_identifier));
            }
          }
          params.erase(
            std::remove_if(
              params.begin(),
              params.end(),
              [&](const irept &pi)
              {
                if(pi.id() != ID_cpp_declaration)
                  return false;
                const auto &pd = static_cast<const cpp_declarationt &>(pi);
                if(
                  pd.declarators().empty() ||
                  (!pd.declarators().front().get_bool(ID_ellipsis) &&
                   !pd.declarators().front().type().get_bool(ID_ellipsis) &&
                   !pd.type().get_bool(ID_ellipsis)))
                  return false;
                // the pack parameter's type names its template pack
                const irept *t = &pd.type();
                while(t->id() != ID_cpp_name && !t->get_sub().empty())
                  t = &t->get_sub().front();
                std::string own;
                if(t->id() == ID_cpp_name && !t->get_sub().empty())
                  own = id2string(t->get_sub().front().get(ID_identifier));
                if(own.empty() || empty_pack_short_names.count(own) == 0)
                  return false;
                for(const auto &nsub :
                    pd.declarators().front().name().get_sub())
                  if(nsub.id() == ID_name)
                    removed_param_names.push_back(nsub.get(ID_identifier));
                return true;
              }),
            params.end());
          if(!removed_param_names.empty() && function_type.has_subtype())
          {
            std::function<bool(const irept &)> refs_removed =
              [&](const irept &n) -> bool
            {
              if(n.id() == ID_cpp_name)
                for(const auto &sn : n.get_sub())
                  if(
                    sn.id() == ID_name &&
                    std::find(
                      removed_param_names.begin(),
                      removed_param_names.end(),
                      sn.get(ID_identifier)) != removed_param_names.end())
                    return true;
              for(const auto &sn : n.get_sub())
                if(refs_removed(sn))
                  return true;
              for(const auto &ns : n.get_named_sub())
                if(refs_removed(ns.second))
                  return true;
              return false;
            };
            std::function<void(irept &)> strip_refs = [&](irept &node)
            {
              if(
                node.id() == ID_side_effect &&
                node.get(ID_statement) == ID_function_call)
              {
                for(auto &sub : node.get_sub())
                  if(sub.id() == ID_arguments)
                  {
                    auto &asub = sub.get_sub();
                    asub.erase(
                      std::remove_if(
                        asub.begin(),
                        asub.end(),
                        [&](const irept &a)
                        {
                          return (a.id() == ID_cpp_name ||
                                  a.get_bool(ID_ellipsis)) &&
                                 refs_removed(a);
                        }),
                      asub.end());
                  }
              }
              for(auto &sub : node.get_sub())
                strip_refs(sub);
              for(auto &ns : node.get_named_sub())
                strip_refs(ns.second);
            };
            strip_refs(to_type_with_subtype(function_type).subtype());
          }
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
          // (an element of a bound function parameter pack: above)
          {
            const auto &pn = pdecl.declarators().front().name().get_sub();
            if(
              !pn.empty() && pn.front().id() == ID_name &&
              std::find(
                bound_parameter_packs.begin(),
                bound_parameter_packs.end(),
                pn.front().get(ID_identifier)) != bound_parameter_packs.end())
            {
              continue;
            }
          }
          // N5008 [dcl.meaning.general]/1: the parameter's type is the
          // decl-specifier type modified by its declarator (`X *p' is a
          // pointer); the decl-specifier type alone made `p' an `X'
          typet ptype = pdecl.declarators().front().merge_type(pdecl.type());
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
          // The synthetic symbol is keyed by template scope + parameter
          // name, shared by every specialization of the template: its type
          // must be the CURRENT deduction's, or the second instantiation
          // (`make_range(map)' after `make_range(vector)') evaluates
          // `decltype(c.begin())' against the first one's parameter type
          // and returns the wrong ranget (an unrelated class: "found no
          // match for symbol 'ranget'", the whole body dropped).
          if(cpp_typecheck.symbol_table.has_symbol(sym_name))
          {
            cpp_typecheck.symbol_table.get_writeable_ref(sym_name).type = ptype;
          }
          else
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
    const auto unbind = [&]()
    {
      for(const auto &name : bound_parameter_packs)
        cpp_typecheck.requires_parameter_packs.erase(name);
    };
    try
    {
      cpp_typecheck.typecheck_type(function_type);
    }
    catch(...)
    {
      unbind();
      throw;
    }
    unbind();
    old_handler.set_message_count(messaget::M_ERROR, sfinae_errors);
  }
  catch(...)
  {
    old_handler.set_message_count(messaget::M_ERROR, sfinae_errors);
    return false;
  }

  // N5008 [temp.deduct.general]/8: type deduction fails if substituting
  // the deduced arguments forms an invalid type -- among the listed
  // examples "attempting to create a reference to void" and "attempting
  // to create a function type in which a parameter has a type of void".
  // `T &&' deduced from a void expression (libstdc++'s poison pill
  // `void begin(auto &) = delete', called in the requires-expression of
  // the `__adl_begin' concept) is such a case; the instance
  // `operator()<void>' would otherwise be created with no parameter for
  // `__t' and its body fail to convert.
  if(function_type.id() == ID_code)
  {
    for(const auto &parameter : to_code_type(function_type).parameters())
    {
      const typet &parameter_type = parameter.type();
      if(parameter_type.id() == ID_empty)
        return false;
      if(
        is_reference(parameter_type) &&
        to_reference_type(parameter_type).base_type().id() == ID_empty)
      {
        return false;
      }
    }
  }
  return true;
}

/// Function template argument deduction without call arguments
/// ([temp.deduct.funcaddr], [temp.arg.explicit]/4): the template is named
/// without a call and without explicit arguments.  Every template parameter
/// has a default argument, or the target of a function-pointer conversion
/// supplies the arguments.
/// \return the deduced specialization, or nil to give up; no value when
///   deduction is to proceed as for a call (defaults exist)
std::optional<exprt> cpp_typecheck_resolvet::deduce_without_call_arguments(
  const exprt &expr,
  const cpp_declarationt &cpp_declaration,
  const cpp_typecheck_fargst &fargs)
{
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
      {
        return nil_exprt(); // give up
      }
    }
  }
  return {};
}

/// N5008 [temp.variadic]/5-7: shape the function type \p function_type for
/// the deduced function parameter pack -- an EMPTY pack removes its
/// parameter (and the pack's call-argument references in a trailing return
/// type), a pack of N elements is expanded into N parameters.
void cpp_typecheck_resolvet::expand_function_parameter_pack(
  const cpp_declaratort &function_declarator,
  const irept::subt &parameters,
  bool variadic_pack_empty,
  const irep_idt &pack_param_name,
  bool has_non_empty_pack,
  std::size_t pack_expansion_size,
  const std::vector<typet> &pack_deduced_types,
  typet &function_type)
{
  if(variadic_pack_empty && function_type.id() == ID_function_type)
  {
    irept::subt &params = function_type.add(ID_parameters).get_sub();
    // Remove parameters whose declarator has ellipsis AND whose type names
    // THE empty pack (own-pack rule).  N5008 [dcl.fct]/6: a bare `...`
    // parameter is C VARARGS -- not a pack reference -- and must survive
    // (it vanished from `decltype(F()()) invoke_(F, ...)` whenever the
    // trailing template pack deduced empty, and the instantiated overload
    // no longer accepted extra arguments).  `B...` with B a non-pack is
    // likewise varargs; only the empty pack's own parameter expands to
    // nothing ([temp.variadic]/7).
    params.erase(
      std::remove_if(
        params.begin(),
        params.end(),
        [&pack_param_name](const irept &p)
        {
          if(p.id() == ID_cpp_declaration)
          {
            const auto &decl = to_cpp_declaration(p);
            if(!decl.declarators().empty())
            {
              const auto &d = decl.declarators().front();
              if(!d.get_bool(ID_ellipsis) && !d.type().get_bool(ID_ellipsis))
                return false;
              const irept *t = &decl.type();
              while(t->id() != ID_cpp_name && !t->get_sub().empty())
                t = &t->get_sub().front();
              std::string own;
              if(t->id() == ID_cpp_name && !t->get_sub().empty())
                own = id2string(t->get_sub().front().get(ID_identifier));
              return own == id2string(pack_param_name);
            }
          }
          return false;
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
}

/// N5008 [temp.deduct.call]: deduce the template arguments from the call
/// arguments \p fargs (from \p it on), one function parameter of
/// \p parameters at a time -- P/A pairs, forwarding references, a trailing
/// function parameter pack (its element types are collected in
/// \p pack_deduced_types, its size in \p pack_expansion_size).
void cpp_typecheck_resolvet::deduce_from_call_arguments(
  const irept::subt &parameters,
  const cpp_typecheck_fargst &fargs,
  exprt::operandst::const_iterator it,
  std::size_t &pack_expansion_size,
  bool &has_non_empty_pack,
  std::vector<typet> &pack_deduced_types)
{
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
        // N5008 [temp.deduct.call]/3: a forwarding reference is an
        // rvalue reference to a cv-unqualified BARE template parameter
        // of this template.  A template-id like `uptr<U>` is also a
        // cpp_name here, but `uptr<U>&&` is an ORDINARY rvalue-reference
        // parameter: treating it as forwarding made an
        // (CBMC-)lvalue-marked prvalue argument deduce against
        // `uptr<derived>&` and fail, rejecting unique_ptr's converting
        // constructor for `unique_ptr<const derived>(new derived())`.
        // Require a single unadorned name (no template arguments, no
        // scope qualification).
        const auto &base = arg_declaration.type();
        if(
          base.id() == ID_template_parameter_symbol_type ||
          (base.id() == ID_cpp_name && base.get_sub().size() == 1 &&
           base.get_sub().front().id() == ID_name))
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
            const bool elem_is_lvalue = cpp_typecheck.is_lvalue_expression(*it);
            // [expr.type]/1: an xvalue typed `T &&' has type T
            typet element_type = it->type();
            if(!elem_is_lvalue && is_rvalue_reference(element_type))
              element_type = to_reference_type(element_type).base_type();
            typet deduced_type =
              elem_is_lvalue ? ::reference_type(it->type()) : element_type;
            pack_deduced_types.push_back(deduced_type);
            guess_template_args(arg_declaration.type(), deduced_type);
            continue;
          }

          typet arg_actual_type = it->type();
          if(arg_type.id() == ID_cpp_name)
          {
            // N5008 [expr.type]/1 + [temp.deduct.call]/2: an expression
            // never has reference type -- the operand's recorded
            // reference wrapper (e.g. a forwarding-reference parameter
            // `_View&&` passed on to a BY-VALUE pack, libc++'s
            // `invoke(__closure, __view)` in operator|) is adjusted
            // away before the by-value deduction, so the array-to-
            // pointer decay below sees the array (`int(&)[1]` must
            // deduce `int*`, not reference-to-array).
            if(is_reference(arg_actual_type))
              arg_actual_type = to_reference_type(arg_actual_type).base_type();
            // a reference-to-array is represented as the ARRAY type
            // carrying the reference bit (`ref_array`), not as a
            // pointer -- clear it, the [expr.type]/1 adjustment again
            arg_actual_type.remove(ID_C_reference);
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
      // lvalue, deduce T as "lvalue reference to A".  A materialised
      // temporary or a dereference of an unnamed rvalue reference (the
      // result of std::move) is not an lvalue (is_lvalue_expression);
      // named rvalue reference variables are.
      // N5008 [temp.deduct.call]/2-3: the function-to-pointer conversion
      // of the argument applies only when P is not a reference type; for
      // a reference P (`T &', `T &&') a function lvalue's type A is the
      // function type itself (T = void(int) for `cb'; a forwarding
      // reference deduces T = void (&)(int)).
      if(
        is_reference(arg_type) && it->id() == ID_address_of &&
        it->get_bool(ID_C_implicit) &&
        to_address_of_expr(*it).object().type().id() == ID_code)
      {
        const typet &function_type = to_address_of_expr(*it).object().type();
        if(is_forwarding_ref)
        {
          guess_template_args(
            arg_declaration.type(), ::reference_type(function_type));
        }
        else
          guess_template_args(arg_type, function_type);
        ++it;
        continue;
      }

      const bool is_lvalue = cpp_typecheck.is_lvalue_expression(*it);
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
        (to_pointer_type(arg_type).base_type().id() ==
           ID_template_parameter_symbol_type ||
         (to_pointer_type(arg_type).base_type().id() == ID_cpp_name &&
          to_pointer_type(arg_type).base_type().get_sub().size() == 1 &&
          to_pointer_type(arg_type).base_type().get_sub().front().id() ==
            ID_name)))
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
          // see the pack branch above: [expr.type]/1 adjustment first,
          // so a reference-wrapped array argument still decays
          // ([temp.deduct.call]/2)
          if(is_reference(arg_actual_type))
            arg_actual_type = to_reference_type(arg_actual_type).base_type();
          arg_actual_type.remove(ID_C_reference);
          arg_actual_type.remove(ID_C_constant);
          arg_actual_type.remove(ID_C_volatile);
          if(arg_actual_type.id() == ID_array)
            arg_actual_type =
              pointer_type(to_array_type(arg_actual_type).element_type());
        }
        else if(!is_reference(arg_type) && !is_rvalue_reference(arg_type))
        {
          // N5008 [temp.deduct.call]/2.1: for any non-reference P (`X *',
          // `const X *', `box<X> *'), an array argument A is replaced by
          // the pointer from the array-to-pointer conversion; `f(arr)'
          // with `template <class X> int f(X *)' deduces X = int
          typet adjusted = arg_actual_type;
          if(is_reference(adjusted))
            adjusted = to_reference_type(adjusted).base_type();
          adjusted.remove(ID_C_reference);
          if(adjusted.id() == ID_array)
          {
            arg_actual_type =
              pointer_type(to_array_type(adjusted).element_type());
          }
        }
        if(is_forwarding_ref && is_rvalue_reference(arg_type))
        {
          // N5008 [expr.type]/1: an expression of type `reference to T'
          // (an xvalue such as `static_cast<char &&>(c)', which the front
          // end types as char &&) has type T; [temp.deduct.call]/3: a
          // non-lvalue argument deduces T as A
          if(is_rvalue_reference(arg_actual_type))
            arg_actual_type = to_reference_type(arg_actual_type).base_type();
          guess_template_args(
            to_pointer_type(arg_type).base_type(), arg_actual_type);
        }
        else
          guess_template_args(arg_type, arg_actual_type);
      }
    }

    ++it;
  }
}

/// N5008 [over.match.viable]/4: after deduction, is every call argument of
/// \p fargs implicitly convertible to the corresponding parameter of the
/// substituted \p function_type?  Deduction can succeed with mismatching
/// types (T deduced from another parameter); the candidate is then not
/// viable.  Conversion attempts run with their diagnostics discarded.
bool cpp_typecheck_resolvet::arguments_convertible_to_parameters(
  const typet &function_type,
  const irept::subt &parameters,
  const cpp_typecheck_fargst &fargs)
{
  message_handlert &old_handler = cpp_typecheck.get_message_handler();
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
    // an EXPLICIT object parameter ([dcl.fct]/6, `this Self &&self') is an
    // ordinary parameter paired with the object argument: keep both
    const bool explicit_object =
      !has_this && function_type.get_bool("explicit_this");
    if(fargs.has_object && !explicit_object && arg_it != fargs.operands.end())
      ++arg_it;
    for(std::size_t i = start;
        i < params.size() && arg_it != fargs.operands.end();
        ++i, ++arg_it)
    {
      // N5008 [over.ics.list]: a braced-init-list argument has no type;
      // its conversion (list-initialization of the parameter) is checked
      // with the viability of the whole candidate
      // (disambiguate_functions), not by this quick filter
      if(arg_it->id() == ID_initializer_list)
        continue;
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
          {
            return false;
          }
        }
      }
    }
  }
  return true;
}

/// N5008 [temp.deduct.call]/1 + [temp.variadic]/5: record the function
/// parameter pack deduced from the call in the template map as a PACK
/// (element types and size) -- non-empty with \p pack_deduced_types, or
/// empty (size 0) -- so that a pack expansion in the substituted signature
/// expands to its elements.
void cpp_typecheck_resolvet::record_deduced_function_parameter_pack(
  const cpp_declarationt &cpp_declaration,
  bool has_non_empty_pack,
  std::size_t pack_expansion_size,
  const std::vector<typet> &pack_deduced_types)
{
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
    // N5008 [temp.deduct.call]/1: the pack deduced from the trailing
    // FUNCTION parameter pack (`_Up... __u`) corresponds to the LAST
    // type pack of the template's parameter list, and a pack already
    // deduced from a template-id argument must not be clobbered --
    // mirroring the pack_args recorder above.  Taking the FIRST type
    // pack overwrote `_Tf` (deduced {box} from the __tuple_types<_Tf...>
    // argument) with the trailing pack's {int} in libc++ __tuple_impl's
    // three-pack constructor, so the substituted signature read
    // `__tuple_types<int>` and the (correctly deduced) candidate was
    // rejected -- the converting-element constructor-drop shape.
    const auto &t_params2 =
      cpp_declaration.template_type().template_parameters();
    for(auto it_p = t_params2.rbegin(); it_p != t_params2.rend(); ++it_p)
    {
      if(!it_p->get_bool(ID_ellipsis) || it_p->id() != ID_type)
        continue;
      const irep_idt pack_id = it_p->type().get(ID_identifier);
      if(!pack_id.empty())
      {
        auto &slot = cpp_typecheck.template_map.pack_args_map[pack_id];
        if(slot.empty())
        {
          slot = pack_deduced_types;
          cpp_typecheck.template_map.set_pack_size(
            pack_id, pack_expansion_size);
        }
      }
      break;
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
          cpp_typecheck.template_map.set_pack_size(pack_id, 0);
        break;
      }
    }
  }
}

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
  {
    return nil_exprt(); // not a template
  }

  PRECONDITION(expr.id() == ID_symbol);

  // a template is always a declaration
  const cpp_declarationt &cpp_declaration = to_cpp_declaration(tmp);

  // Class templates require explicit template arguments,
  // no guessing!
  if(cpp_declaration.is_class_template())
  {
    return nil_exprt();
  }

  // we need function arguments for guessing
  if(fargs.operands.empty() && expr.find(ID_C_template_arguments).is_nil())
  {
    const std::optional<exprt> result =
      deduce_without_call_arguments(expr, cpp_declaration, fargs);
    if(result.has_value())
      return *result;
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
  deduction_nontype_types_guardt deduction_nontype_types_guard{
    current_deduction_nontype_types};
  current_deduction_nontype_types =
    template_nontype_parameter_types(cpp_declaration.template_type());
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
    // N5008 [namespace.udecl]/1, [class.inhctor.init]/1: a constructor
    // template inherited by `using B::B' is a member of B; its signature and
    // default template arguments depend on B's template parameters, not on
    // those of the derived class named by ID_C_class.  The template's
    // identifier names its own class; prefer that one when it differs.
    const irep_idt id_class_tag = class_tag;
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
          // A template argument can be a FUNCTION TYPE spelled with
          // parentheses (partial specializations like
          // `function<_Rp(_ArgTypes...)>` instantiate to
          // `std::function<(cpp_declaration(...))->(...)>::template.X`);
          // the `::` inside those parens is NOT a scope separator of
          // the class name.  Track both bracket kinds at depth.
          if(c == '<' || c == '(')
            ++depth;
          else if(c == '>' || c == ')')
            --depth;
          else if(depth == 0 && c == ':' && class_name[i + 1] == ':')
            insert_pos = i + 2;
        }
        const irep_idt owner_tag = class_name.substr(0, insert_pos) + "tag-" +
                                   class_name.substr(insert_pos);
        if(
          id_class_tag.empty() ||
          (owner_tag != id_class_tag &&
           cpp_typecheck.symbol_table.has_symbol(owner_tag)))
        {
          class_tag = owner_tag;
        }
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
  // N5008 [dcl.fct]/6, [over.match.funcs]/3, [temp.deduct.call]/1: an
  // EXPLICIT object parameter (`this Self &&self', C++23) is an ordinary
  // function parameter deduced from the object argument -- Self is the type
  // of the object expression (a forwarding reference: `A &' for an lvalue
  // A).  It was skipped together with the object argument, so Self was never
  // deduced and `a.get()' had no viable candidate ("found no match for
  // symbol 'get'"; libstdc++ 16's std::_Bind::operator()).
  const bool explicit_object_parameter =
    !parameters.empty() && parameters.front().get_bool("explicit_this");
  if(
    fargs.has_object && it != fargs.operands.end() &&
    !explicit_object_parameter)
    ++it;

  // Track pack expansion size for non-empty packs
  std::size_t pack_expansion_size = 0;
  bool has_non_empty_pack = false;
  std::vector<typet> pack_deduced_types;

  deduce_from_call_arguments(
    parameters,
    fargs,
    it,
    pack_expansion_size,
    has_non_empty_pack,
    pack_deduced_types);

  // N5008 [temp.arg.explicit]/2 + [temp.deduct.general]/2: explicitly
  // specified template arguments are substituted BEFORE deduction and
  // are not themselves subject to it; deduction only fills the
  // remaining parameters.  The pre-population of the map above is
  // overwritten when a call argument's type deduces a DIFFERENT
  // binding for an explicitly-given parameter (e.g. `get<W>(1, 2)`
  // deducing T=int from the int argument although T=W was given, the
  // argument being convertible to W).  Re-assert the explicit
  // bindings after the deduction pass so they always win.
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
        exprt resolved_arg = explicit_args.arguments()[i];
        if(resolved_arg.id() == ID_type)
          cpp_typecheck.template_map.apply(resolved_arg.type());
        cpp_typecheck.template_map.set(params[i], resolved_arg);
      }
    }
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
      // Outside every function body (a namespace-scope alias or
      // variable's `decltype(f(tup<int, char>()))') there is no such call
      // to fold, and the instance must have the deduced arity as well.
      if(
        derived_to_base_deduced_packs.find(pack_id) ==
          derived_to_base_deduced_packs.end() &&
        !cpp_typecheck.instantiating_deferred_body &&
        !cpp_typecheck.functions_being_typechecked.empty())
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

  // N5008 [temp.deduct.call]/1 + [temp.variadic]/4: the elements deduced
  // for a trailing FUNCTION parameter pack must be recorded as the pack's
  // template-argument list (pack_args_map), not merely in the scalar
  // type_map (whose per-element guesses overwrite one another).  With
  // several template packs (`template<unsigned long... Uf, class... Tf,
  // class... Up> impl(indices<Uf...>, types<Tf...>, Up...)`, the libc++
  // __tuple_impl constructor), an empty pre-seeded pack_args_map entry
  // for Up otherwise survives deduction, the #deduced_packs record
  // stores arity 0, and instantiate_template expands the trailing pack
  // to ZERO parameters -- the rebuilt instance is then rejected by the
  // second disambiguation ("found no match for symbol '__tuple_impl'").
  if(has_non_empty_pack && !pack_deduced_types.empty())
  {
    const auto &t_params =
      cpp_declaration.template_type().template_parameters();
    std::size_t n_type_packs = 0;
    for(const auto &tp : t_params)
      if(tp.get_bool(ID_ellipsis) && tp.id() == ID_type)
        ++n_type_packs;
    // Only the MULTI-pack shape needs this record (the single-pack flow
    // sizes the pack from the argument count alone and pre-dates this);
    // overwriting the single-pack state changes the evaluation order of
    // parallel-pack SFINAE constraints (cpp17_tuple_get_two_pack_ctor).
    for(auto it_p = t_params.rbegin();
        n_type_packs >= 2 && it_p != t_params.rend();
        ++it_p)
    {
      if(!it_p->get_bool(ID_ellipsis) || it_p->id() != ID_type)
        continue;
      const irep_idt pid = it_p->type().get(ID_identifier);
      auto &slot = cpp_typecheck.template_map.pack_args_map[pid];
      if(slot.empty())
      {
        slot = pack_deduced_types;
        cpp_typecheck.template_map.set_pack_size(
          pid, pack_deduced_types.size());
      }
      break; // the trailing function pack corresponds to the LAST type pack
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

  // N5008 [temp.variadic]/5,8: with MULTIPLE template parameter packs
  // (libc++ __tuple_impl's five-pack constructor `<size_t... _Uf,
  // class... _Tf, size_t... _Ul, class... _Tl, class... _Up>`), the
  // flat positional argument list cannot encode how arguments split
  // between the packs, and the single-pack surgery below (placeholder
  // dropping/expansion keyed to the FIRST pack) mis-pairs parameters
  // with arguments.  The per-pack element bindings recorded by the
  // deduction above (pack_args_map/pack_expr_map/pack_size_map) are
  // authoritative ([temp.deduct]); rebuild the flat list by walking
  // the parameters and splicing each pack's elements (an empty pack
  // contributes nothing, [temp.variadic]/7).  Gated to n_packs >= 2:
  // single-pack shapes keep the existing (battle-tested) path.
  {
    const auto &mp_params =
      cpp_declaration.template_type().template_parameters();
    std::size_t mp_n_packs = 0;
    for(const auto &tp : mp_params)
      if(tp.get_bool(ID_ellipsis))
        ++mp_n_packs;
    bool mp_all_sized = mp_n_packs >= 2;
    // The FUNCTION parameter pack's deduced element types live only in
    // the local pack_deduced_types (they are entered into the map after
    // this block in the single-pack path); allow exactly ONE unmapped
    // pack and serve it from there.
    irep_idt mp_fn_pack;
    if(mp_all_sized)
    {
      for(const auto &tp : mp_params)
      {
        if(!tp.get_bool(ID_ellipsis))
          continue;
        const irep_idt pid = tp.id() == ID_type ? tp.type().get(ID_identifier)
                                                : tp.get(ID_identifier);
        if(pid.empty())
        {
          mp_all_sized = false;
          break;
        }
        if(
          cpp_typecheck.template_map.pack_size_map.find(pid) ==
          cpp_typecheck.template_map.pack_size_map.end())
        {
          if(mp_fn_pack.empty() && tp.id() == ID_type)
            mp_fn_pack = pid;
          else
          {
            mp_all_sized = false;
            break;
          }
        }
      }
    }
    if(mp_all_sized)
    {
      cpp_template_args_tct::argumentst spliced;
      bool ok = true;
      for(const auto &tp : mp_params)
      {
        const irep_idt pid = tp.id() == ID_type ? tp.type().get(ID_identifier)
                                                : tp.get(ID_identifier);
        if(tp.get_bool(ID_ellipsis))
        {
          const auto pa_it = cpp_typecheck.template_map.pack_args_map.find(pid);
          const auto pe_it = cpp_typecheck.template_map.pack_expr_map.find(pid);
          if(pid == mp_fn_pack)
          {
            // the function parameter pack: deduced per-argument above
            for(const auto &t : pack_deduced_types)
              spliced.push_back(exprt(ID_type, t));
            // record the binding so template_mapt::build's multi-pack
            // gate (and sizeof... evaluation) sees this pack as bound
            cpp_typecheck.template_map.set_pack_size(
              pid, pack_deduced_types.size());
            cpp_typecheck.template_map.pack_args_map[pid] = pack_deduced_types;
            // NO scalar type_map convenience entry: build() deliberately
            // avoids scalar-binding packs of two or more elements -- the
            // scalar CONCRETIZES the pack reference in the parameter
            // pattern (`Up&&...` becomes `int&&`), and the in-class
            // replication (cpp_typecheck_compound_type.cpp) can then no
            // longer identify the pack by name to expand it per
            // [temp.variadic]/5.
            if(pack_deduced_types.size() == 1)
              cpp_typecheck.template_map.type_map[pid] =
                pack_deduced_types.front();
          }
          else if(pa_it != cpp_typecheck.template_map.pack_args_map.end())
          {
            for(const auto &t : pa_it->second)
              spliced.push_back(exprt(ID_type, t));
          }
          else if(pe_it != cpp_typecheck.template_map.pack_expr_map.end())
          {
            for(const auto &v : pe_it->second)
              spliced.push_back(v);
          }
          // empty pack: contributes no arguments
        }
        else if(tp.id() == ID_type)
        {
          const typet t = cpp_typecheck.template_map.lookup_type(pid);
          if(t.is_nil())
          {
            ok = false;
            break;
          }
          spliced.push_back(exprt(ID_type, t));
        }
        else
        {
          const exprt e = cpp_typecheck.template_map.lookup_expr(pid);
          if(e.is_nil())
          {
            ok = false;
            break;
          }
          spliced.push_back(e);
        }
      }
      if(ok)
        template_args.arguments().swap(spliced);
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
  if(
    template_args.has_unassigned() && !apply_default_template_arguments(
                                        cpp_declaration,
                                        template_symbol,
                                        parameters,
                                        member_class_tag,
                                        has_non_empty_pack,
                                        pack_deduced_types,
                                        pack_expansion_size,
                                        template_args,
                                        pack_param_name,
                                        variadic_pack_empty))
  {
    return nil_exprt();
  }

  if(template_args.has_unassigned())
  {
    return nil_exprt(); // give up
  }

  // Build the type of the function.

  typet function_type = function_declarator.merge_type(cpp_declaration.type());

  // When a variadic pack is empty, remove pack-expanded parameters from
  // the function type before typechecking, since the pack type name
  // (e.g. Base) has no mapping in the template map.
  expand_function_parameter_pack(
    function_declarator,
    parameters,
    variadic_pack_empty,
    pack_param_name,
    has_non_empty_pack,
    pack_expansion_size,
    pack_deduced_types,
    function_type);

  record_deduced_function_parameter_pack(
    cpp_declaration,
    has_non_empty_pack,
    pack_expansion_size,
    pack_deduced_types);

  if(!substitute_function_type(function_declarator, fargs, function_type))
    return nil_exprt();

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

  if(!arguments_convertible_to_parameters(function_type, parameters, fargs))
    return nil_exprt();

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

/// N5008 [temp.arg.explicit]/9: template argument deduction can extend the
/// sequence of template arguments of a pack beyond the explicitly specified
/// ones (`count<int>(1, 2, 3)' deduces Ts = {int, int, int}).  True when the
/// last explicit argument falls into a type template parameter pack that is
/// the pattern of a function parameter pack, and the call has more
/// arguments than the explicit ones account for -- the explicit arguments
/// are then only a prefix, and deduction must see the call.
static bool explicit_pack_extended_by_deduction(
  const cpp_declarationt &declaration,
  const cpp_template_args_non_tct &explicit_args,
  const cpp_typecheck_fargst &fargs)
{
  const auto &params = declaration.template_type().template_parameters();
  const std::size_t n_explicit = explicit_args.arguments().size();
  if(n_explicit == 0)
    return false;
  // the parameter that receives the last explicit argument
  std::size_t pack_index = params.size();
  for(std::size_t i = 0; i < params.size() && i < n_explicit; ++i)
  {
    if(params[i].get_bool(ID_ellipsis))
    {
      pack_index = i;
      break;
    }
  }
  if(pack_index == params.size() || params[pack_index].id() != ID_type)
    return false;
  // the function's parameters: a pack expansion among them
  const typet &ftype = declaration.declarators().front().type();
  std::size_t n_fixed = 0;
  bool has_pack = false;
  for(const auto &p : ftype.find(ID_parameters).get_sub())
  {
    if(p.id() != ID_cpp_declaration)
      continue;
    const auto &pd = static_cast<const cpp_declarationt &>(p);
    const bool is_pack =
      !pd.declarators().empty() &&
      (pd.declarators().front().get_bool(ID_ellipsis) ||
       pd.declarators().front().type().get_bool(ID_ellipsis) ||
       pd.type().get_bool(ID_ellipsis));
    if(is_pack)
      has_pack = true;
    else
      ++n_fixed;
  }
  if(!has_pack)
    return false;
  std::size_t n_call = fargs.operands.size();
  if(fargs.has_object && n_call > 0)
    --n_call;
  const std::size_t n_in_pack = n_explicit - pack_index;
  return n_call > n_fixed + n_in_pack;
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
  //
  // N5008 [basic.lookup.unqual]/1 + [expr.ref]/1: the template arguments
  // of a member template-id (`r.is_derived<I>()`, `p->template f<I>()`)
  // are expressions of the enclosing postfix-expression, not of the
  // object's class.  typecheck_expr_member enters the object's class
  // scope before resolving the member name, so `original_scope` is that
  // class scope there; an argument naming the CALLER's template
  // parameter (`I` of the enclosing member template, CBMC's own
  // small_shared_n_way_ptrt::is_derived) found nothing and the call had
  // no candidates ("found no match for symbol 'is_derived'", the
  // goto-symex dog-food block).  Use the recorded point of use.
  cpp_template_args_tct template_args_tc;

  {
    cpp_save_scopet save_scope(cpp_typecheck.cpp_scopes);

    cpp_typecheck.cpp_scopes.go_to(
      fargs.naming_scope != nullptr ? *fargs.naming_scope : *original_scope);

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
    (!has_variadic_template_parameter(cpp_declaration.template_type()) ||
     explicit_pack_extended_by_deduction(
       cpp_declaration, template_args_non_tc, fargs)))
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
  unsigned *cv_distance,
  std::vector<unsigned> *cv_per_argument)
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
            type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
        }
        else
        {
          if(
            expr.type().get_bool(ID_C_is_operator) &&
            fargs.operands.size() == parameters.size())
          {
            return fargs.match(
              type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
          }

          cpp_typecheck_fargst new_fargs(fargs);
          new_fargs.add_object(to_member_expr(expr).compound());

          return new_fargs.match(
            type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
        }
      }
      else
      {
        // Template function instance without this parameter yet;
        // match directly against the parameters.
        return fargs.match(
          type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
      }
    }
  }
  else if(fargs.has_object)
  {
    // If the function type already has a 'this' parameter (e.g., an
    // instantiated member function template), match directly — fargs
    // already includes the object and the type already includes 'this'.
    // N5008 [dcl.fct]/6, [over.match.funcs]/3: an EXPLICIT object
    // parameter (`this Self &&self') is likewise paired with the object
    // argument -- it IS the first parameter, so match with the object in
    // place (removing it left `Self &&' unmatched: no viable get()).
    if(
      !type.parameters().empty() &&
      (type.parameters().front().get_this() || type.get_bool("explicit_this")))
    {
      return fargs.match(
        type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
    }

    // For template function instances (pre-instantiation), the function
    // type doesn't include 'this' yet.  Remove the object and try to
    // match; if that fails, still accept the candidate with a high
    // distance so it can be instantiated and checked properly later.
    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.remove_object();

    if(new_fargs.match(
         type, args_distance, cpp_typecheck, cv_distance, cv_per_argument))
      return true;

    if(expr.id() == ID_template_function_instance)
    {
      args_distance = 10000;
      return true;
    }

    return false;
  }
  else if(
    expr.id() == ID_symbol && !fargs.has_object && !type.parameters().empty() &&
    type.parameters().front().get_this())
  {
    // Instantiated template member function (symbol_exprt with this
    // parameter) called without an explicit object — add a synthetic
    // this for matching purposes. This includes calls with empty
    // operand lists (e.g., variadic methods called with no args).
    // N5008 [over.match.funcs]/5: the implied object argument is
    // CONTRIVED only when there is no object; when fargs already
    // carries one (has_object, operands.front() is the object --
    // e.g. resolving a member operator* inside a trailing-return
    // decltype during deduction, where the candidate arrives as a
    // plain symbol), prepending a second, synthetic object made every
    // such candidate fail the arity check and silently drop
    // ("no match for symbol 'map'", the 26-line trailing-decltype
    // kernel).  Fall through to the direct match instead.
    const typet &object_type =
      to_pointer_type(type.parameters().front().type()).base_type();
    symbol_exprt object(irep_idt(), object_type);
    object.set(ID_C_lvalue, true);

    cpp_typecheck_fargst new_fargs(fargs);
    new_fargs.add_object(object);
    return new_fargs.match(
      type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
  }

  return fargs.match(
    type, args_distance, cpp_typecheck, cv_distance, cv_per_argument);
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
            // N5008 [basic.lookup.qual.general]/1, [dcl.enum]/11: a
            // nested-name-specifier may denote an enumeration, also through
            // a member typedef (`typedef imp::action action;' ...
            // `action::copy', libstdc++'s std::function manager)
            if(t.id() == ID_struct_tag || t.id() == ID_c_enum_tag)
            {
              const irep_idt &tag_id = to_tag_type(t).get_identifier();
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

    // N5008 [basic.lookup.argdep]/2.3: for an ENUMERATION type the
    // associated entities are its innermost enclosing namespace (and,
    // for a class member, the class).  libc++'s poison-pill pattern
    // depends on this: error_code's converting constructor does
    //   using __adl_only::make_error_code;
    //   *this = make_error_code(__e);
    // where only ADL over the enum argument (io_errc, future_errc)
    // can find the real make_error_code overload -- without it the
    // deleted poison pill is the sole candidate and the whole
    // <system_error>/<ios> conversion fails.
    if(arg_type.id() == ID_c_enum_tag)
    {
      const irep_idt &enum_name = to_c_enum_tag_type(arg_type).get_identifier();
      if(!visited.insert(enum_name).second)
        return;
      auto enum_scope_it = cpp_typecheck.cpp_scopes.id_map.find(enum_name);
      if(enum_scope_it == cpp_typecheck.cpp_scopes.id_map.end())
        return;
      for(cpp_scopet *ns = static_cast<cpp_scopet *>(enum_scope_it->second);
          ns != nullptr;
          ns = &ns->get_parent())
      {
        if(ns->is_namespace() || ns->is_root_scope())
        {
          auto tmp_set = ns->lookup(base_name, cpp_scopet::SCOPE_ONLY);
          id_set.insert(tmp_set.begin(), tmp_set.end());
          break; // innermost enclosing namespace only
        }
        if(ns->is_root_scope())
          break;
      }
      return;
    }

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
