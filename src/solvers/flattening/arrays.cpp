/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arrays.h"

#include <util/arith_tools.h>
#include <util/json.h>
#include <util/message.h>
#include <util/replace_expr.h>
#include <util/std_expr.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>

#ifdef DEBUG
#include <iostream>
#endif

#include <unordered_set>

arrayst::arrayst(
  const namespacet &_ns,
  propt &_prop,
  message_handlert &_message_handler,
  bool _get_array_constraints)
  : equalityt(_prop, _message_handler),
    ns(_ns),
    log(_message_handler),
    message_handler(_message_handler)
{
  lazy_arrays = false;        // will be set to true when --refine is used
  incremental_cache = false;  // for incremental solving
  // get_array_constraints is true when --show-array-constraints is used
  get_array_constraints = _get_array_constraints;
}

void arrayst::record_array_index(const index_exprt &index)
{
  // we are not allowed to put the index directly in the
  //   entry for the root of the equivalence class
  //   because this map is accessed during building the error trace
  std::size_t number=arrays.number(index.array());
  if(index_map[number].insert(index.index()).second)
    update_indices.insert(number);
}

literalt arrayst::record_array_equality(
  const equal_exprt &equality)
{
  const exprt &op0=equality.op0();
  const exprt &op1=equality.op1();

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    op0.type() == op1.type(),
    "record_array_equality got equality without matching types",
    irep_pretty_diagnosticst{equality});

  DATA_INVARIANT(
    op0.type().id() == ID_array,
    "record_array_equality parameter should be array-typed");

  array_equalities.push_back(array_equalityt());

  array_equalities.back().f1=op0;
  array_equalities.back().f2=op1;
  array_equalities.back().l=SUB::equality(op0, op1);

  arrays.make_union(op0, op1);
  collect_arrays(op0);
  collect_arrays(op1);

  return array_equalities.back().l;
}

void arrayst::collect_indices()
{
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    collect_indices(arrays[i]);
  }
}

void arrayst::collect_indices(const exprt &expr)
{
  if(expr.id()!=ID_index)
  {
    if(expr.id() == ID_array_comprehension)
      array_comprehension_args.insert(
        to_array_comprehension_expr(expr).arg().get_identifier());

    forall_operands(op, expr) collect_indices(*op);
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

    if(array_op_type.id()==ID_array)
    {
      const array_typet &array_type=
        to_array_type(array_op_type);

      if(is_unbounded_array(array_type))
      {
        record_array_index(e);
      }
    }
  }
}

void arrayst::collect_arrays(const exprt &a)
{
  const array_typet &array_type = to_array_type(a.type());

  if(a.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == with_expr.old().type(),
      "collect_arrays got 'with' without matching types",
      irep_pretty_diagnosticst{a});

    arrays.make_union(a, with_expr.old());
    collect_arrays(with_expr.old());

    // make sure this shows as an application
    for(std::size_t i = 1; i < with_expr.operands().size(); i += 2)
    {
      index_exprt index_expr(with_expr.old(), with_expr.operands()[i]);
      record_array_index(index_expr);
    }
  }
  else if(a.id()==ID_update)
  {
    const update_exprt &update_expr=to_update_expr(a);

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
  else if(a.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(a);

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
  else if(a.id()==ID_symbol)
  {
  }
  else if(a.id()==ID_nondet_symbol)
  {
  }
  else if(a.id()==ID_member)
  {
    const auto &struct_op = to_member_expr(a).struct_op();

    DATA_INVARIANT(
      struct_op.id() == ID_symbol || struct_op.id() == ID_nondet_symbol,
      "unexpected array expression: member with '" + struct_op.id_string() +
        "'");
  }
  else if(a.id()==ID_constant ||
          a.id()==ID_array ||
          a.id()==ID_string_constant)
  {
  }
  else if(a.id()==ID_array_of)
  {
  }
  else if(a.id()==ID_byte_update_little_endian ||
          a.id()==ID_byte_update_big_endian)
  {
    DATA_INVARIANT(
      false,
      "byte_update should be removed before collect_arrays");
  }
  else if(a.id()==ID_typecast)
  {
    const auto &typecast_op = to_typecast_expr(a).op();

    // cast between array types?
    DATA_INVARIANT(
      typecast_op.type().id() == ID_array,
      "unexpected array type cast from " + typecast_op.type().id_string());

    arrays.make_union(a, typecast_op);
    collect_arrays(typecast_op);
  }
  else if(a.id()==ID_index)
  {
    // nested unbounded arrays
    const auto &array_op = to_index_expr(a).array();
    arrays.make_union(a, array_op);
    collect_arrays(array_op);
  }
  else if(a.id() == ID_array_comprehension)
  {
  }
  else
  {
    DATA_INVARIANT(
      false,
      "unexpected array expression (collect_arrays): '" + a.id_string() + "'");
  }
}

/// adds array constraints (refine=true...lazily for the refinement loop)
void arrayst::add_array_constraint(const lazy_constraintt &lazy, bool refine)
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

void arrayst::add_array_constraints()
{
  collect_indices();
  // at this point all indices should in the index set

  // reduce initial index map
  update_index_map(true);

  // add constraints for if, with, array_of, lambda
  std::set<std::size_t> roots_to_process, updated_roots;
  for(std::size_t i=0; i<arrays.size(); i++)
    roots_to_process.insert(arrays.find_number(i));

  while(!roots_to_process.empty())
  {
    for(std::size_t i = 0; i < arrays.size(); i++)
    {
      if(roots_to_process.count(arrays.find_number(i)) == 0)
        continue;

      // take a copy as arrays may get modified by add_array_constraints
      // in case of nested unbounded arrays
      exprt a = arrays[i];

      add_array_constraints(index_map[arrays.find_number(i)], a);

      // we have to update before it gets used in the next add_* call
      for(const std::size_t u : update_indices)
        updated_roots.insert(arrays.find_number(u));
      update_index_map(false);
    }

    roots_to_process = std::move(updated_roots);
    updated_roots.clear();
  }

  // add constraints for equalities
  for(const auto &equality : array_equalities)
  {
    add_array_constraints_equality(
      index_map[arrays.find_number(equality.f1)],
      equality);

    // update_index_map should not be necessary here
  }

  // add the Ackermann constraints
  add_array_Ackermann_constraints();
}

void arrayst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#ifdef DEBUG
  std::cout << "arrays.size(): " << arrays.size() << '\n';
#endif

  // iterate over arrays
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    const index_sett &index_set=index_map[arrays.find_number(i)];

#ifdef DEBUG
    std::cout << "index_set.size(): " << index_set.size() << '\n';
#endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator
        i1=index_set.begin();
        i1!=index_set.end();
        i1++)
      for(index_sett::const_iterator
          i2=i1;
          i2!=index_set.end();
          i2++)
        if(i1!=i2)
        {
          if(i1->is_constant() && i2->is_constant())
            continue;

          // index equality
          const equal_exprt indices_equal(
            *i1, typecast_exprt::conditional_cast(*i2, i1->type()));

          literalt indices_equal_lit=convert(indices_equal);

          if(indices_equal_lit!=const_literal(false))
          {
            const typet &subtype = arrays[i].type().subtype();
            index_exprt index_expr1(arrays[i], *i1, subtype);

            index_exprt index_expr2=index_expr1;
            index_expr2.index()=*i2;

            equal_exprt values_equal(index_expr1, index_expr2);

            // add constraint
            lazy_constraintt lazy(lazy_typet::ARRAY_ACKERMANN,
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
void arrayst::update_index_map(std::size_t i)
{
  if(arrays.is_root_number(i))
    return;

  std::size_t root_number=arrays.find_number(i);
  INVARIANT(root_number!=i, "is_root_number incorrect?");

  index_sett &root_index_set=index_map[root_number];
  index_sett &index_set=index_map[i];

  root_index_set.insert(index_set.begin(), index_set.end());
}

void arrayst::update_index_map(bool update_all)
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
    for(std::size_t i=0; i<arrays.size(); i++)
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

void arrayst::add_array_constraints_equality(
  const index_sett &index_set,
  const array_equalityt &array_equality)
{
  // add constraints x=y => x[i]=y[i]

  for(const auto &index : index_set)
  {
    const typet &subtype1 = array_equality.f1.type().subtype();
    index_exprt index_expr1(array_equality.f1, index, subtype1);

    const typet &subtype2 = array_equality.f2.type().subtype();
    index_exprt index_expr2(array_equality.f2, index, subtype2);

    DATA_INVARIANT(
      index_expr1.type()==index_expr2.type(),
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

void arrayst::add_array_constraints(
  const index_sett &index_set,
  const exprt &expr)
{
  if(expr.id()==ID_with)
    return add_array_constraints_with(index_set, to_with_expr(expr));
  else if(expr.id()==ID_update)
    return add_array_constraints_update(index_set, to_update_expr(expr));
  else if(expr.id()==ID_if)
    return add_array_constraints_if(index_set, to_if_expr(expr));
  else if(expr.id()==ID_array_of)
    return add_array_constraints_array_of(index_set, to_array_of_expr(expr));
  else if(expr.id() == ID_array)
    return add_array_constraints_array_constant(index_set, to_array_expr(expr));
  else if(expr.id() == ID_array_comprehension)
  {
    return add_array_constraints_comprehension(
      index_set, to_array_comprehension_expr(expr));
  }
  else if(expr.id()==ID_symbol ||
          expr.id()==ID_nondet_symbol ||
          expr.id()==ID_constant ||
          expr.id()=="zero_string" ||
          expr.id()==ID_string_constant)
  {
  }
  else if(
    expr.id() == ID_member &&
    (to_member_expr(expr).struct_op().id() == ID_symbol ||
     to_member_expr(expr).struct_op().id() == ID_nondet_symbol))
  {
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    INVARIANT(false, "byte_update should be removed before arrayst");
  }
  else if(expr.id()==ID_typecast)
  {
    // we got a=(type[])b
    const auto &expr_typecast_op = to_typecast_expr(expr).op();

    // add a[i]=b[i]
    for(const auto &index : index_set)
    {
      const typet &subtype = expr.type().subtype();
      index_exprt index_expr1(expr, index, subtype);
      index_exprt index_expr2(expr_typecast_op, index, subtype);

      DATA_INVARIANT(
        index_expr1.type()==index_expr2.type(),
        "array elements should all have same type");

      // add constraint
      lazy_constraintt lazy(lazy_typet::ARRAY_TYPECAST,
        equal_exprt(index_expr1, index_expr2));
      add_array_constraint(lazy, false); // added immediately
      array_constraint_count[constraint_typet::ARRAY_TYPECAST]++;
    }
  }
  else if(expr.id()==ID_index)
  {
  }
  else
  {
    DATA_INVARIANT(
      false,
      "unexpected array expression (add_array_constraints): '" +
        expr.id_string() + "'");
  }
}

void arrayst::add_array_constraints_with(
  const index_sett &index_set,
  const with_exprt &expr)
{
  // We got x=(y with [i:=v, j:=w, ...]).
  // First add constraints x[i]=v, x[j]=w, ...
  std::unordered_set<exprt, irep_hash> updated_indices;

  const exprt::operandst &operands = expr.operands();
  for(std::size_t i = 1; i + 1 < operands.size(); i += 2)
  {
    const exprt &index = operands[i];
    const exprt &value = operands[i + 1];

    index_exprt index_expr(expr, index, expr.type().subtype());

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      index_expr.type() == value.type(),
      "with-expression operand should match array element type",
      irep_pretty_diagnosticst{expr});

    lazy_constraintt lazy(
      lazy_typet::ARRAY_WITH, equal_exprt(index_expr, value));
    add_array_constraint(lazy, false); // added immediately
    array_constraint_count[constraint_typet::ARRAY_WITH]++;

    updated_indices.insert(index);
  }

  // For all other indices use the existing value, i.e., add constraints
  // x[I]=y[I] for I!=i,j,...

  for(auto other_index : index_set)
  {
    if(updated_indices.find(other_index) == updated_indices.end())
    {
      // we first build the guard
      exprt::operandst disjuncts;
      disjuncts.reserve(updated_indices.size());
      for(const auto &index : updated_indices)
      {
        disjuncts.push_back(equal_exprt{
          index, typecast_exprt::conditional_cast(other_index, index.type())});
      }

      literalt guard_lit = convert(disjunction(disjuncts));

      if(guard_lit!=const_literal(true))
      {
        const typet &subtype = expr.type().subtype();
        index_exprt index_expr1(expr, other_index, subtype);
        index_exprt index_expr2(expr.old(), other_index, subtype);

        equal_exprt equality_expr(index_expr1, index_expr2);

        // add constraint
        lazy_constraintt lazy(lazy_typet::ARRAY_WITH, or_exprt(equality_expr,
                                literal_exprt(guard_lit)));

        add_array_constraint(lazy, false); // added immediately
        array_constraint_count[constraint_typet::ARRAY_WITH]++;

#if 0 // old code for adding, not significantly faster
        {
          literalt equality_lit=convert(equality_expr);

          bvt bv;
          bv.reserve(2);
          bv.push_back(equality_lit);
          bv.push_back(guard_lit);
          prop.lcnf(bv);
        }
#endif
      }
    }
  }
}

void arrayst::add_array_constraints_update(
  const index_sett &,
  const update_exprt &)
{
  // we got x=UPDATE(y, [i], v)
  // add constaint x[i]=v

#if 0
  const exprt &index=expr.where();
  const exprt &value=expr.new_value();

  {
    index_exprt index_expr(expr, index, expr.type().subtype());

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      index_expr.type()==value.type(),
      "update operand should match array element type",
      irep_pretty_diagnosticst{expr});

    set_to_true(equal_exprt(index_expr, value));
  }

  // use other array index applications for "else" case
  // add constraint x[I]=y[I] for I!=i

  for(auto other_index : index_set)
  {
    if(other_index!=index)
    {
      // we first build the guard

      other_index = typecast_exprt::conditional_cast(other_index, index.type());

      literalt guard_lit=convert(equal_exprt(index, other_index));

      if(guard_lit!=const_literal(true))
      {
        const typet &subtype=expr.type().subtype();
        index_exprt index_expr1(expr, other_index, subtype);
        index_exprt index_expr2(expr.op0(), other_index, subtype);

        equal_exprt equality_expr(index_expr1, index_expr2);

        literalt equality_lit=convert(equality_expr);

        // add constraint
        bvt bv;
        bv.reserve(2);
        bv.push_back(equality_lit);
        bv.push_back(guard_lit);
        prop.lcnf(bv);
      }
    }
  }
#endif
}

void arrayst::add_array_constraints_array_of(
  const index_sett &index_set,
  const array_of_exprt &expr)
{
  // we got x=array_of[v]
  // get other array index applications
  // and add constraint x[i]=v

  for(const auto &index : index_set)
  {
    const typet &element_type = expr.type().element_type();
    index_exprt index_expr(expr, index, element_type);

    DATA_INVARIANT(
      index_expr.type() == expr.what().type(),
      "array_of operand type should match array element type");

    // add constraint
    lazy_constraintt lazy(
      lazy_typet::ARRAY_OF, equal_exprt(index_expr, expr.what()));
    add_array_constraint(lazy, false); // added immediately
    array_constraint_count[constraint_typet::ARRAY_OF]++;
  }
}

void arrayst::add_array_constraints_array_constant(
  const index_sett &index_set,
  const array_exprt &expr)
{
  // we got x = { v, ... } - add constraint x[i] = v
  const exprt::operandst &operands = expr.operands();

  for(const auto &index : index_set)
  {
    const typet &element_type = expr.type().element_type();
    const index_exprt index_expr{expr, index, element_type};

    if(index.is_constant())
    {
      // We have a constant index - just pick the element at that index from the
      // array constant.

      const std::size_t i =
        numeric_cast_v<std::size_t>(to_constant_expr(index));
      // if the access is out of bounds, we leave it unconstrained
      if(i >= operands.size())
        continue;

      const exprt v = operands[i];
      DATA_INVARIANT(
        index_expr.type() == v.type(),
        "array operand type should match array element type");

      // add constraint
      lazy_constraintt lazy{lazy_typet::ARRAY_CONSTANT,
                            equal_exprt{index_expr, v}};
      add_array_constraint(lazy, false); // added immediately
      array_constraint_count[constraint_typet::ARRAY_CONSTANT]++;
    }
    else
    {
      // We have a non-constant index into an array constant. We need to build a
      // case statement testing the index against all possible values. Whenever
      // neighbouring array elements are the same, we can test the index against
      // the range rather than individual elements. This should be particularly
      // helpful when we have arrays of zeros, as is the case for initializers.

      std::vector<std::pair<std::size_t, std::size_t>> ranges;

      for(std::size_t i = 0; i < operands.size(); ++i)
      {
        if(ranges.empty() || operands[i] != operands[ranges.back().first])
          ranges.emplace_back(i, i);
        else
          ranges.back().second = i;
      }

      for(const auto &range : ranges)
      {
        exprt index_constraint;

        if(range.first == range.second)
        {
          index_constraint =
            equal_exprt{index, from_integer(range.first, index.type())};
        }
        else
        {
          index_constraint = and_exprt{
            binary_predicate_exprt{
              from_integer(range.first, index.type()), ID_le, index},
            binary_predicate_exprt{
              index, ID_le, from_integer(range.second, index.type())}};
        }

        lazy_constraintt lazy{
          lazy_typet::ARRAY_CONSTANT,
          implies_exprt{index_constraint,
                        equal_exprt{index_expr, operands[range.first]}}};
        add_array_constraint(lazy, true); // added lazily
        array_constraint_count[constraint_typet::ARRAY_CONSTANT]++;
      }
    }
  }
}

void arrayst::add_array_constraints_comprehension(
  const index_sett &index_set,
  const array_comprehension_exprt &expr)
{
  // we got x=lambda(i: e)
  // get all other array index applications
  // and add constraints x[j]=e[i/j]

  for(const auto &index : index_set)
  {
    index_exprt index_expr{expr, index};
    exprt comprehension_body = expr.body();
    replace_expr(expr.arg(), index, comprehension_body);

    // add constraint
    lazy_constraintt lazy(
      lazy_typet::ARRAY_COMPREHENSION,
      equal_exprt(index_expr, comprehension_body));

    add_array_constraint(lazy, false); // added immediately
    array_constraint_count[constraint_typet::ARRAY_COMPREHENSION]++;
  }
}

void arrayst::add_array_constraints_if(
  const index_sett &index_set,
  const if_exprt &expr)
{
  // we got x=(c?a:b)
  literalt cond_lit=convert(expr.cond());

  // get other array index applications
  // and add c => x[i]=a[i]
  //        !c => x[i]=b[i]

  // first do true case

  for(const auto &index : index_set)
  {
    const typet subtype = expr.type().subtype();
    index_exprt index_expr1(expr, index, subtype);
    index_exprt index_expr2(expr.true_case(), index, subtype);

    // add implication
    lazy_constraintt lazy(lazy_typet::ARRAY_IF,
                            or_exprt(literal_exprt(!cond_lit),
                              equal_exprt(index_expr1, index_expr2)));
    add_array_constraint(lazy, false); // added immediately
    array_constraint_count[constraint_typet::ARRAY_IF]++;

#if 0 // old code for adding, not significantly faster
    prop.lcnf(!cond_lit, convert(equal_exprt(index_expr1, index_expr2)));
#endif
  }

  // now the false case
  for(const auto &index : index_set)
  {
    const typet subtype = expr.type().subtype();
    index_exprt index_expr1(expr, index, subtype);
    index_exprt index_expr2(expr.false_case(), index, subtype);

    // add implication
    lazy_constraintt lazy(
      lazy_typet::ARRAY_IF,
      or_exprt(literal_exprt(cond_lit),
      equal_exprt(index_expr1, index_expr2)));
    add_array_constraint(lazy, false); // added immediately
    array_constraint_count[constraint_typet::ARRAY_IF]++;

#if 0 // old code for adding, not significantly faster
    prop.lcnf(cond_lit, convert(equal_exprt(index_expr1, index_expr2)));
#endif
  }
}

std::string arrayst::enum_to_string(constraint_typet type)
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
  default:
    UNREACHABLE;
  }
}

void arrayst::display_array_constraint_count()
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
