/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arrays.h"

#include <util/arith_tools.h>
#include <util/range.h>
#include <util/replace_expr.h>
#include <util/replace_symbol.h>
#include <util/std_expr.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>

#ifdef DEBUG
#  include <util/format_expr.h>

#  include <iostream>
#endif

#include <unordered_set>

arrayst::arrayst(
  const namespacet &_ns,
  propt &_prop,
  message_handlert &_message_handler,
  bool _get_array_constraints)
  : mapst(_ns, _prop, _message_handler, _get_array_constraints),
    message_handler(_message_handler)
{
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

void arrayst::record_array_let_binding(
  const symbol_exprt &symbol,
  const exprt &value)
{
  DATA_INVARIANT(
    symbol.type().id() == ID_array,
    "record_array_let_binding parameter should be array-typed");

  const equal_exprt eq{symbol, value};
  const literalt eq_lit = record_array_equality(eq);
  prop.l_set_to_true(eq_lit);
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
  else if(
    expr.id() == ID_symbol || expr.id() == ID_nondet_symbol ||
    expr.is_constant() || expr.id() == "zero_string" ||
    expr.id() == ID_string_constant)
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
      const typet &element_type = to_array_type(expr.type()).element_type();
      index_exprt index_expr1(expr, index, element_type);
      index_exprt index_expr2(expr_typecast_op, index, element_type);

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
  else if(auto let_expr = expr_try_dynamic_cast<let_exprt>(expr))
  {
    // we got x=let(a=e, A)
    // add x[i]=A[a/e][i]

    exprt where = let_expr->where();
    replace_symbolt replace_symbol;
    for(const auto &binding :
        make_range(let_expr->variables()).zip(let_expr->values()))
    {
      replace_symbol.insert(binding.first, binding.second);
    }
    replace_symbol(where);

    for(const auto &index : index_set)
    {
      index_exprt index_expr{expr, index};
      index_exprt where_indexed{where, index};

      // add constraint
      lazy_constraintt lazy{
        lazy_typet::ARRAY_LET, equal_exprt{index_expr, where_indexed}};

      add_array_constraint(lazy, false); // added immediately
      array_constraint_count[constraint_typet::ARRAY_LET]++;
    }
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
  // We got x=(y with [i:=v]).
  // First add constraint x[i]=v
  std::unordered_set<exprt, irep_hash> updated_indices;

  index_exprt index_expr(
    expr, expr.where(), to_array_type(expr.type()).element_type());

  DATA_INVARIANT_WITH_DIAGNOSTICS(
    index_expr.type() == expr.new_value().type(),
    "with-expression operand should match array element type",
    irep_pretty_diagnosticst{expr});

  lazy_constraintt lazy(
    lazy_typet::ARRAY_WITH, equal_exprt(index_expr, expr.new_value()));
  add_array_constraint(lazy, false); // added immediately
  array_constraint_count[constraint_typet::ARRAY_WITH]++;

  updated_indices.insert(expr.where());

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
        const typet &element_type = to_array_type(expr.type()).element_type();
        index_exprt index_expr1(expr, other_index, element_type);
        index_exprt index_expr2(expr.old(), other_index, element_type);

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

      const std::optional<std::size_t> i =
        numeric_cast<std::size_t>(to_constant_expr(index));
      // if the access is out of bounds, we leave it unconstrained
      if(!i.has_value() || *i >= operands.size())
        continue;

      const exprt v = operands[*i];
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
    const typet &element_type = to_array_type(expr.type()).element_type();
    index_exprt index_expr1(expr, index, element_type);
    index_exprt index_expr2(expr.true_case(), index, element_type);

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
    const typet &element_type = to_array_type(expr.type()).element_type();
    index_exprt index_expr1(expr, index, element_type);
    index_exprt index_expr2(expr.false_case(), index, element_type);

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
