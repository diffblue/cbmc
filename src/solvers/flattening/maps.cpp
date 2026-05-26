/*******************************************************************\

Module: Map Theory (base class for array theory)

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// Map Theory — method implementations

#include "maps.h"

#include <util/json.h>
#include <util/std_expr.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>

#ifdef DEBUG
#  include <util/format_expr.h>

#  include <iostream>
#endif

mapst::mapst(
  const namespacet &_ns,
  propt &_prop,
  message_handlert &_message_handler,
  bool _collect_constraint_stats)
  : equalityt(_prop, _message_handler),
    ns(_ns),
    log(_message_handler),
    defer_constraints(false),
    collect_constraint_stats(_collect_constraint_stats)
{
}

void mapst::record_key(const index_exprt &index)
{
  // we are not allowed to put the key directly in the
  //   entry for the root of the equivalence class
  //   because this map is accessed during building the error trace
  std::size_t number = maps.number(index.array());
  if(domain_map[number].insert(index.index()).second)
    dirty_classes.insert(number);
}

void mapst::collect_maps(const exprt &a)
{
  const array_typet &array_type = to_array_type(a.type());

  if(a.id() == ID_with)
  {
    const with_exprt &with_expr = to_with_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == with_expr.old().type(),
      "collect_maps got 'with' without matching types",
      irep_pretty_diagnosticst{a});

    maps.make_union(a, with_expr.old());
    collect_maps(with_expr.old());

    // make sure this shows as an application
    index_exprt index_expr(with_expr.old(), with_expr.where());
    record_key(index_expr);
  }
  else if(a.id() == ID_update)
  {
    const update_exprt &update_expr = to_update_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == update_expr.old().type(),
      "collect_maps got 'update' without matching types",
      irep_pretty_diagnosticst{a});

    maps.make_union(a, update_expr.old());
    collect_maps(update_expr.old());

#if 0
    // make sure this shows as an application
    index_exprt index_expr(update_expr.old(), update_expr.index());
    record_key(index_expr);
#endif
  }
  else if(a.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == if_expr.true_case().type(),
      "collect_maps got if without matching types",
      irep_pretty_diagnosticst{a});

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == if_expr.false_case().type(),
      "collect_maps got if without matching types",
      irep_pretty_diagnosticst{a});

    maps.make_union(a, if_expr.true_case());
    maps.make_union(a, if_expr.false_case());
    collect_maps(if_expr.true_case());
    collect_maps(if_expr.false_case());
  }
  else if(a.id() == ID_symbol)
  {
  }
  else if(a.id() == ID_nondet_symbol)
  {
  }
  else if(a.id() == ID_member)
  {
    const auto &struct_op = to_member_expr(a).struct_op();

    DATA_INVARIANT(
      struct_op.id() == ID_symbol || struct_op.id() == ID_nondet_symbol,
      "unexpected map expression: member with '" + struct_op.id_string() + "'");
  }
  else if(a.is_constant() || a.id() == ID_array || a.id() == ID_string_constant)
  {
  }
  else if(a.id() == ID_array_of)
  {
  }
  else if(
    a.id() == ID_byte_update_little_endian ||
    a.id() == ID_byte_update_big_endian)
  {
    DATA_INVARIANT(false, "byte_update should be removed before collect_maps");
  }
  else if(a.id() == ID_typecast)
  {
    const auto &typecast_op = to_typecast_expr(a).op();

    // cast between map types?
    DATA_INVARIANT(
      typecast_op.type().id() == ID_array,
      "unexpected map type cast from " + typecast_op.type().id_string());

    maps.make_union(a, typecast_op);
    collect_maps(typecast_op);
  }
  else if(a.id() == ID_index)
  {
    // nested unbounded maps
    const auto &array_op = to_index_expr(a).array();
    maps.make_union(a, array_op);
    collect_maps(array_op);
  }
  else if(a.id() == ID_array_comprehension)
  {
  }
  else if(auto let_expr = expr_try_dynamic_cast<let_exprt>(a))
  {
    maps.make_union(a, let_expr->where());
    collect_maps(let_expr->where());
  }
  else
  {
    DATA_INVARIANT(
      false,
      "unexpected map expression (collect_maps): '" + a.id_string() + "'");
  }
}

/// adds map constraints (refine=true...lazily for the refinement loop)
void mapst::add_map_constraint(const lazy_constraintt &lazy, bool refine)
{
  if(defer_constraints && refine)
  {
    // lazily add the constraint
    lazy_constraints.push_back(lazy);
  }
  else
  {
    // add the constraint eagerly
    prop.l_set_to_true(convert(lazy.lazy));
  }
}

void mapst::add_Ackermann_constraints()
{
  // this is quadratic!

#ifdef DEBUG
  std::cout << "maps.size(): " << maps.size() << '\n';
#endif

  // iterate over maps
  for(std::size_t i = 0; i < maps.size(); i++)
  {
    const key_sett &key_set = domain_map[maps.find_number(i)];

#ifdef DEBUG
    std::cout << "key_set.size(): " << key_set.size() << '\n';
#endif

    // iterate over keys, 2x!
    for(key_sett::const_iterator i1 = key_set.begin(); i1 != key_set.end();
        i1++)
      for(key_sett::const_iterator i2 = i1; i2 != key_set.end(); i2++)
        if(i1 != i2)
        {
          if(i1->is_constant() && i2->is_constant())
            continue;

          // key equality
          const equal_exprt indices_equal(
            *i1, typecast_exprt::conditional_cast(*i2, i1->type()));

          literalt indices_equal_lit = convert(indices_equal);

          if(indices_equal_lit != const_literal(false))
          {
            const typet &subtype = to_array_type(maps[i].type()).element_type();
            index_exprt index_expr1(maps[i], *i1, subtype);

            index_exprt index_expr2 = index_expr1;
            index_expr2.index() = *i2;

            equal_exprt values_equal(index_expr1, index_expr2);

            // add constraint
            lazy_constraintt lazy(
              lazy_typet::MAP_ACKERMANN,
              implies_exprt(literal_exprt(indices_equal_lit), values_equal));
            add_map_constraint(lazy, true); // added lazily
            constraint_count[constraint_typet::MAP_ACKERMANN]++;

#if 0 // old code for adding, not significantly faster
            prop.lcnf(!indices_equal_lit, convert(values_equal));
#endif
          }
        }
  }
}

/// merge the keys into the root
void mapst::update_domain_map(std::size_t i)
{
  if(maps.is_root_number(i))
    return;

  std::size_t root_number = maps.find_number(i);
  INVARIANT(root_number != i, "is_root_number incorrect?");

  key_sett &root_key_set = domain_map[root_number];
  key_sett &key_set = domain_map[i];

  root_key_set.insert(key_set.begin(), key_set.end());
}

void mapst::update_domain_map(bool update_all)
{
  // iterate over non-roots
  // possible reasons why update is needed:
  //  -- there are new equivalence classes in maps
  //  -- there are new keys for maps that are not the root
  //     of an equivalence class
  //     (and we cannot do that in record_key())
  //  -- equivalence classes have been merged
  if(update_all)
  {
    for(std::size_t i = 0; i < maps.size(); i++)
      update_domain_map(i);
  }
  else
  {
    for(const auto &key : dirty_classes)
      update_domain_map(key);

    dirty_classes.clear();
  }

#ifdef DEBUG
  // print key sets
  for(const auto &domain_entry : domain_map)
    for(const auto &key : domain_entry.second)
      std::cout << "Key set (" << domain_entry.first << " = "
                << maps.find_number(domain_entry.first) << " = "
                << format(maps[maps.find_number(domain_entry.first)])
                << "): " << format(key) << '\n';
  std::cout << "-----\n";
#endif
}

void mapst::add_map_equality_constraints(
  const key_sett &key_set,
  const map_equalityt &equality)
{
  // add constraints x=y => x[i]=y[i]

  for(const auto &key : key_set)
  {
    const typet &element_type1 =
      to_array_type(equality.f1.type()).element_type();
    index_exprt index_expr1(equality.f1, key, element_type1);

    const typet &element_type2 =
      to_array_type(equality.f2.type()).element_type();
    index_exprt index_expr2(equality.f2, key, element_type2);

    DATA_INVARIANT(
      index_expr1.type() == index_expr2.type(),
      "map elements should all have same type");

    map_equalityt equal;
    equal.f1 = index_expr1;
    equal.f2 = index_expr2;
    equal.l = equality.l;
    equal_exprt equality_expr(index_expr1, index_expr2);

    // add constraint
    // equality constraints are not added lazily
    // convert must be done to guarantee correct update of the key_set
    prop.lcnf(!equality.l, convert(equality_expr));
    constraint_count[constraint_typet::MAP_EQUALITY]++;
  }
}

std::string mapst::enum_to_string(constraint_typet type)
{
  // The internal enum tags are MAP_X, but the JSON strings are kept as
  // arrayX/arrayConstraints because the constraints reported by
  // --show-array-constraints are array-specific (arrayst is the only
  // implementation that records them, and the CLI option name says
  // 'array'). Decoupling here preserves backward compatibility for
  // consumers of --show-array-constraints --json-ui output.
  switch(type)
  {
  case constraint_typet::MAP_ACKERMANN:
    return "arrayAckermann";
  case constraint_typet::MAP_WITH:
    return "arrayWith";
  case constraint_typet::MAP_IF:
    return "arrayIf";
  case constraint_typet::MAP_OF:
    return "arrayOf";
  case constraint_typet::MAP_TYPECAST:
    return "arrayTypecast";
  case constraint_typet::MAP_CONSTANT:
    return "arrayConstant";
  case constraint_typet::MAP_COMPREHENSION:
    return "arrayComprehension";
  case constraint_typet::MAP_EQUALITY:
    return "arrayEquality";
  case constraint_typet::MAP_LET:
    return "arrayLet";
  default:
    UNREACHABLE;
  }
}

void mapst::display_constraint_count()
{
  json_objectt json_result;
  json_objectt &json_array_theory =
    json_result["arrayConstraints"].make_object();

  size_t num_constraints = 0;

  map_constraint_countt::iterator it = constraint_count.begin();
  while(it != constraint_count.end())
  {
    std::string constraint_type_string = enum_to_string(it->first);
    json_array_theory[constraint_type_string] =
      json_numbert(std::to_string(it->second));

    num_constraints += it->second;
    it++;
  }

  json_result["numOfConstraints"] =
    json_numbert(std::to_string(num_constraints));
  log.status() << ",\n" << json_result;
}
