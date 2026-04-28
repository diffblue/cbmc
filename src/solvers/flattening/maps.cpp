/*******************************************************************\

Module: Map Theory (base class for array theory)

Author: Daniel Kroening, kroening@kroening.com

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
  bool _get_array_constraints)
  : equalityt(_prop, _message_handler),
    ns(_ns),
    log(_message_handler),
    lazy_arrays(false),
    incremental_cache(false),
    get_array_constraints(_get_array_constraints)
{
}

void mapst::record_array_index(const index_exprt &index)
{
  // we are not allowed to put the index directly in the
  //   entry for the root of the equivalence class
  //   because this map is accessed during building the error trace
  std::size_t number = arrays.number(index.array());
  if(index_map[number].insert(index.index()).second)
    update_indices.insert(number);
}

void mapst::collect_indices()
{
  for(std::size_t i = 0; i < arrays.size(); i++)
  {
    collect_indices(arrays[i]);
  }
}

void mapst::collect_indices(const exprt &expr)
{
  if(expr.id() != ID_index)
  {
    if(expr.id() == ID_array_comprehension)
      array_comprehension_args.insert(
        to_array_comprehension_expr(expr).arg().get_identifier());

    for(const auto &op : expr.operands())
      collect_indices(op);
  }
  else
  {
    const index_exprt &e = to_index_expr(expr);

    if(
      e.index().id() == ID_symbol &&
      array_comprehension_args.count(
        to_symbol_expr(e.index()).get_identifier()) != 0)
    {
      return;
    }

    collect_indices(e.index()); // necessary?

    const typet &array_op_type = e.array().type();

    if(array_op_type.id() == ID_array)
    {
      const array_typet &array_type = to_array_type(array_op_type);

      if(is_unbounded_array(array_type))
      {
        record_array_index(e);
      }
    }
  }
}

void mapst::collect_arrays(const exprt &a)
{
  const array_typet &array_type = to_array_type(a.type());

  if(a.id() == ID_with)
  {
    const with_exprt &with_expr = to_with_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == with_expr.old().type(),
      "collect_arrays got 'with' without matching types",
      irep_pretty_diagnosticst{a});

    arrays.make_union(a, with_expr.old());
    collect_arrays(with_expr.old());

    // make sure this shows as an application
    index_exprt index_expr(with_expr.old(), with_expr.where());
    record_array_index(index_expr);
  }
  else if(a.id() == ID_update)
  {
    const update_exprt &update_expr = to_update_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == update_expr.old().type(),
      "collect_arrays got 'update' without matching types",
      irep_pretty_diagnosticst{a});

    arrays.make_union(a, update_expr.old());
    collect_arrays(update_expr.old());

#if 0
    // make sure this shows as an application
    index_exprt index_expr(update_expr.old(), update_expr.index());
    record_array_index(index_expr);
#endif
  }
  else if(a.id() == ID_if)
  {
    const if_exprt &if_expr = to_if_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == if_expr.true_case().type(),
      "collect_arrays got if without matching types",
      irep_pretty_diagnosticst{a});

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == if_expr.false_case().type(),
      "collect_arrays got if without matching types",
      irep_pretty_diagnosticst{a});

    arrays.make_union(a, if_expr.true_case());
    arrays.make_union(a, if_expr.false_case());
    collect_arrays(if_expr.true_case());
    collect_arrays(if_expr.false_case());
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
      "unexpected array expression: member with '" + struct_op.id_string() +
        "'");
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
    DATA_INVARIANT(
      false, "byte_update should be removed before collect_arrays");
  }
  else if(a.id() == ID_typecast)
  {
    const auto &typecast_op = to_typecast_expr(a).op();

    // cast between array types?
    DATA_INVARIANT(
      typecast_op.type().id() == ID_array,
      "unexpected array type cast from " + typecast_op.type().id_string());

    arrays.make_union(a, typecast_op);
    collect_arrays(typecast_op);
  }
  else if(a.id() == ID_index)
  {
    // nested unbounded arrays
    const auto &array_op = to_index_expr(a).array();
    arrays.make_union(a, array_op);
    collect_arrays(array_op);
  }
  else if(a.id() == ID_array_comprehension)
  {
  }
  else if(auto let_expr = expr_try_dynamic_cast<let_exprt>(a))
  {
    arrays.make_union(a, let_expr->where());
    collect_arrays(let_expr->where());
  }
  else
  {
    DATA_INVARIANT(
      false,
      "unexpected array expression (collect_arrays): '" + a.id_string() + "'");
  }
}

/// adds array constraints (refine=true...lazily for the refinement loop)
void mapst::add_array_constraint(
  const lazy_constraintt &lazy,
  bool refine)
{
  if(lazy_arrays && refine)
  {
    // lazily add the constraint
    if(incremental_cache)
    {
      if(expr_map.find(lazy.lazy) == expr_map.end())
      {
        lazy_array_constraints.push_back(lazy);
        expr_map[lazy.lazy] = true;
      }
    }
    else
    {
      lazy_array_constraints.push_back(lazy);
    }
  }
  else
  {
    // add the constraint eagerly
    prop.l_set_to_true(convert(lazy.lazy));
  }
}

void mapst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#ifdef DEBUG
  std::cout << "arrays.size(): " << arrays.size() << '\n';
#endif

  // iterate over arrays
  for(std::size_t i = 0; i < arrays.size(); i++)
  {
    const index_sett &index_set = index_map[arrays.find_number(i)];

#ifdef DEBUG
    std::cout << "index_set.size(): " << index_set.size() << '\n';
#endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator i1 = index_set.begin();
        i1 != index_set.end();
        i1++)
      for(index_sett::const_iterator i2 = i1; i2 != index_set.end(); i2++)
        if(i1 != i2)
        {
          if(i1->is_constant() && i2->is_constant())
            continue;

          // index equality
          const equal_exprt indices_equal(
            *i1, typecast_exprt::conditional_cast(*i2, i1->type()));

          literalt indices_equal_lit = convert(indices_equal);

          if(indices_equal_lit != const_literal(false))
          {
            const typet &subtype =
              to_array_type(arrays[i].type()).element_type();
            index_exprt index_expr1(arrays[i], *i1, subtype);

            index_exprt index_expr2 = index_expr1;
            index_expr2.index() = *i2;

            equal_exprt values_equal(index_expr1, index_expr2);

            // add constraint
            lazy_constraintt lazy(
              lazy_typet::ARRAY_ACKERMANN,
              implies_exprt(literal_exprt(indices_equal_lit), values_equal));
            add_array_constraint(lazy, true); // added lazily
            array_constraint_count[constraint_typet::ARRAY_ACKERMANN]++;

#if 0 // old code for adding, not significantly faster
            prop.lcnf(!indices_equal_lit, convert(values_equal));
#endif
          }
        }
  }
}

/// merge the indices into the root
void mapst::update_index_map(std::size_t i)
{
  if(arrays.is_root_number(i))
    return;

  std::size_t root_number = arrays.find_number(i);
  INVARIANT(root_number != i, "is_root_number incorrect?");

  index_sett &root_index_set = index_map[root_number];
  index_sett &index_set = index_map[i];

  root_index_set.insert(index_set.begin(), index_set.end());
}

void mapst::update_index_map(bool update_all)
{
  // iterate over non-roots
  // possible reasons why update is needed:
  //  -- there are new equivalence classes in arrays
  //  -- there are new indices for arrays that are not the root
  //     of an equivalence class
  //     (and we cannot do that in record_array_index())
  //  -- equivalence classes have been merged
  if(update_all)
  {
    for(std::size_t i = 0; i < arrays.size(); i++)
      update_index_map(i);
  }
  else
  {
    for(const auto &index : update_indices)
      update_index_map(index);

    update_indices.clear();
  }

#ifdef DEBUG
  // print index sets
  for(const auto &index_entry : index_map)
    for(const auto &index : index_entry.second)
      std::cout << "Index set (" << index_entry.first << " = "
                << arrays.find_number(index_entry.first) << " = "
                << format(arrays[arrays.find_number(index_entry.first)])
                << "): " << format(index) << '\n';
  std::cout << "-----\n";
#endif
}

void mapst::add_array_constraints_equality(
  const index_sett &index_set,
  const array_equalityt &array_equality)
{
  // add constraints x=y => x[i]=y[i]

  for(const auto &index : index_set)
  {
    const typet &element_type1 =
      to_array_type(array_equality.f1.type()).element_type();
    index_exprt index_expr1(array_equality.f1, index, element_type1);

    const typet &element_type2 =
      to_array_type(array_equality.f2.type()).element_type();
    index_exprt index_expr2(array_equality.f2, index, element_type2);

    DATA_INVARIANT(
      index_expr1.type() == index_expr2.type(),
      "array elements should all have same type");

    array_equalityt equal;
    equal.f1 = index_expr1;
    equal.f2 = index_expr2;
    equal.l = array_equality.l;
    equal_exprt equality_expr(index_expr1, index_expr2);

    // add constraint
    // equality constraints are not added lazily
    // convert must be done to guarantee correct update of the index_set
    prop.lcnf(!array_equality.l, convert(equality_expr));
    array_constraint_count[constraint_typet::ARRAY_EQUALITY]++;
  }
}

std::string mapst::enum_to_string(constraint_typet type)
{
  switch(type)
  {
  case constraint_typet::ARRAY_ACKERMANN:
    return "arrayAckermann";
  case constraint_typet::ARRAY_WITH:
    return "arrayWith";
  case constraint_typet::ARRAY_IF:
    return "arrayIf";
  case constraint_typet::ARRAY_OF:
    return "arrayOf";
  case constraint_typet::ARRAY_TYPECAST:
    return "arrayTypecast";
  case constraint_typet::ARRAY_CONSTANT:
    return "arrayConstant";
  case constraint_typet::ARRAY_COMPREHENSION:
    return "arrayComprehension";
  case constraint_typet::ARRAY_EQUALITY:
    return "arrayEquality";
  case constraint_typet::ARRAY_LET:
    return "arrayLet";
  default:
    UNREACHABLE;
  }
}

void mapst::display_array_constraint_count()
{
  json_objectt json_result;
  json_objectt &json_array_theory =
    json_result["arrayConstraints"].make_object();

  size_t num_constraints = 0;

  array_constraint_countt::iterator it = array_constraint_count.begin();
  while(it != array_constraint_count.end())
  {
    std::string contraint_type_string = enum_to_string(it->first);
    json_array_theory[contraint_type_string] =
      json_numbert(std::to_string(it->second));

    num_constraints += it->second;
    it++;
  }

  json_result["numOfConstraints"] =
    json_numbert(std::to_string(num_constraints));
  log.status() << ",\n" << json_result;
}
