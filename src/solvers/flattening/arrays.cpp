/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arrays.h"

#include <cassert>
#include <iostream>

#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/format_expr.h>
#include <util/namespace.h>
#include <util/std_expr.h>
#include <util/std_types.h>

#include <solvers/prop/prop.h>

arrayst::arrayst(
  const namespacet &_ns,
  propt &_prop):equalityt(_ns, _prop)
{
}

void arrayst::record_array_index(const index_exprt &index)
{
  collect_arrays(index.array());
  std::size_t number=arrays.number(index.array());
  index_map[number].insert(index.index());
}

literalt arrayst::record_array_equality(
  const equal_exprt &equality)
{
  const exprt &op0=equality.op0();
  const exprt &op1=equality.op1();

  // check types
  if(!base_type_eq(op0.type(), op1.type(), ns))
  {
    std::cout << equality.pretty() << '\n';
    throw "record_array_equality got equality without matching types";
  }

  INVARIANT(ns.follow(op0.type()).id()==ID_array,
            "equality has array type");

  std::size_t a1=arrays.number(op0);
  std::size_t a2=arrays.number(op1);

  literalt l=SUB::equality(op0, op1);

  // one undirected edge for each array equality
  add_weg_edge(a1, a2, l);

  collect_arrays(op0);
  collect_arrays(op1);

  return l;
}

void arrayst::collect_indices(const exprt &expr)
{
  if(expr.id()!=ID_index)
  {
    forall_operands(op, expr)
      collect_indices(*op);
  }
  else
  {
    const index_exprt &e = to_index_expr(expr);
    collect_indices(e.index());
    collect_indices(e.array());

    const typet &array_op_type=ns.follow(e.array().type());

    if(array_op_type.id()==ID_array)
    {
      const array_typet &array_type=
        to_array_type(array_op_type);

      if(is_unbounded_array(array_type))
        record_array_index(e);
    }
  }
}

void arrayst::collect_arrays(const exprt &a)
{
  const array_typet &array_type=
    to_array_type(ns.follow(a.type()));

  // remember it
  wegt::node_indext a_ind=arrays.number(a);

  if(a.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(a);

    // check types
    if(!base_type_eq(array_type, with_expr.old().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got 'with' without matching types";
    }

    collect_indices(with_expr.where());
    collect_indices(with_expr.new_value());

    // one undirected edge for each array update
    std::size_t expr_old_ind=arrays.number(with_expr.old());
    add_weg_edge(a_ind, expr_old_ind, with_expr);

    // record 'old'
    collect_arrays(with_expr.old());
  }
  else if(a.id()==ID_update)
  {
    const update_exprt &update_expr=to_update_expr(a);

    // check types
    if(!base_type_eq(array_type, update_expr.old().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got 'update' without matching types";
    }

    collect_indices(update_expr.new_value());

    // record 'old'
    collect_arrays(update_expr.old());
  }
  else if(a.id()==ID_if)
  {
    const if_exprt &if_expr=to_if_expr(a);

    // check types
    if(!base_type_eq(array_type, if_expr.true_case().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got if without matching types";
    }

    // check types
    if(!base_type_eq(array_type, if_expr.false_case().type(), ns))
    {
      std::cout << a.pretty() << '\n';
      throw "collect_arrays got if without matching types";
    }

    // do weg edges
    std::size_t expr_true_ind=arrays.number(if_expr.true_case());
    std::size_t expr_false_ind=arrays.number(if_expr.false_case());
    literalt cond=convert(if_expr.cond());
    add_weg_edge(a_ind, expr_true_ind, cond);
    add_weg_edge(a_ind, expr_false_ind, !cond);

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
    if(to_member_expr(a).struct_op().id()!=ID_symbol)
      throw
        "unexpected array expression: member with `"+a.op0().id_string()+"'";
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
    assert(false);
  }
  else if(a.id()==ID_typecast)
  {
    // cast between array types?
    const exprt &op=to_typecast_expr(a).op();

    if(op.type().id()==ID_array)
    {
      collect_arrays(op);
    }
    else
      throw "unexpected array type cast from "+op.type().id_string();
  }
  else if(a.id()==ID_index)
  {
    // an array of arrays!
    collect_arrays(to_index_expr(a).array());
  }
  else
    throw "unexpected array expression (collect_arrays): `"+a.id_string()+"'";
}

bool arrayst::must_be_different(
  const exprt &x, const exprt &y)
{
  return false;
}

void arrayst::weg_path_condition(
  const weg_patht &path,
  const exprt &index_a,
  exprt::operandst &cond)
{
  for(const auto &pn : path)
  {
#if ARRAY_SPEEDUP_DEBUG
    std::cout << "edge: " << pn.n << "->" <<
      pn.edge->first << " " <<
      format(arrays[pn.n]) << "\n";
#endif

    const weg_edget &weg_edge=pn.edge->second;

    if(weg_edge.update.is_not_nil())
    {
      const auto &with_expr=to_with_expr(weg_edge.update);
      notequal_exprt inequality(with_expr.where(), index_a);
      cond.push_back(inequality);
    }

    if(!weg_edge.condition.is_true())
      cond.push_back(literal_exprt(weg_edge.condition));
  }
}

void arrayst::process_weg_path(const weg_patht &path)
{
  INVARIANT(!path.empty(), "path is not empty");
  wegt::node_indext a=path.front().n;
  wegt::node_indext b=path.back().n;

  // do constraints
  const index_sett &index_set_a=index_map[a];
  const index_sett &index_set_b=index_map[b];

#if ARRAY_SPEEDUP_DEBUG
  std::cout << "b is: "
            << format(arrays[b])
            << '\n';
#endif

  for(const auto &index_a : index_set_a)
  {
    // lazily instantiate read-over-write
    if(arrays[b].id()==ID_with)
    {
      // we got x=(y with [i:=v])
      const auto &expr_b=to_with_expr(arrays[b]);
      const exprt &index_b=expr_b.where();
      const exprt &value_b=expr_b.new_value();

      // 1. we got a[i]...b[j], given as edges on the stack
      // 2. add (i=j AND path_cond)=>a[i]=b[j]
      // 3. The path condition requires the update indices
      //    on the stack to be different from i.
      exprt::operandst cond;
      cond.reserve(path.size()+1);
      cond.push_back(equal_exprt(index_a, index_b));
      weg_path_condition(path, index_a, cond);

      // a_i=b_i
      index_exprt a_i(arrays[a], index_a);
      // cond => a_i=b_i
      implies_exprt implication(
        conjunction(cond),
        equal_exprt(a_i, value_b));
#if ARRAY_SPEEDUP_DEBUG
      std::cout << "C2a: "
                << format(implication)
                << '\n';
#endif
      set_to_true(implication);
    }
    else if(arrays[b].id()==ID_array_of)
    {
      const auto &expr_b=to_array_of_expr(arrays[b]);
      const exprt &value_b=expr_b.what();

      // 1. we got a[i]...b[j], given as edges on the stack
      // 2. add (i=j AND path_cond)=>a[i]=b[j]
      // 3. The path condition requires the update indices
      //    on the stack to be different from i.
      exprt::operandst cond;
      cond.reserve(path.size());
      weg_path_condition(path, index_a, cond);

      // a_i=value
      index_exprt a_i(arrays[a], index_a);
      // cond => a_i=b_i
      implies_exprt implication(
        conjunction(cond),
        equal_exprt(a_i, value_b));
#if ARRAY_SPEEDUP_DEBUG
      std::cout << "C2b: "
                << format(implication)
                << '\n';
#endif
      set_to_true(implication);
    }

    if(a!=b)
    {
      for(const auto &index_b : index_set_b)
      {
        if(must_be_different(index_a, index_b))
          continue;

        // 1. we got a[i]...b[j], given as edges on the stack
        // 2. add (i=j AND path_cond)=>a[i]=b[j]
        // 3. The path condition requires the update indices
        //    on the stack to be different from i.
        exprt::operandst cond;
        cond.reserve(path.size()+1);
        cond.push_back(equal_exprt(index_a, index_b));
        weg_path_condition(path, index_a, cond);

        // a_i=b_i
        index_exprt a_i(arrays[a], index_a);
        index_exprt b_i(arrays[b], index_b);
        // cond => a_i=b_i
        implies_exprt implication(
          conjunction(cond),
          equal_exprt(a_i, b_i));
#if ARRAY_SPEEDUP_DEBUG
        std::cout << "C3: "
                  << format(implication)
                  << '\n';
#endif
        set_to_true(implication);
      }
    }
  }
}

void arrayst::add_array_constraints()
{
#if ARRAY_SPEEDUP_DEBUG
  for(const auto & a : arrays)
  {
    std::cout << "array: " << format(a)
              << '\n';
  }
#endif

  // auxiliary bit per node for DFS
  std::vector<bool> visited;
  visited.resize(weg.size());

  for(wegt::node_indext a=0; a<arrays.size(); a++)
  {
#if ARRAY_SPEEDUP_DEBUG
    std::cout << "a is: "
              << format(arrays[a])
              << '\n';
#endif

    // DFS from a_i to anything reachable in 'weg'
    std::fill(visited.begin(), visited.end(), false);

    weg_patht path;
    path.push_back(stack_entryt(a, weg[a].out.begin()));
    visited[a]=true;
    process_weg_path(path); // also process 'a' itself

    while(!path.empty())
    {
      // get next edge a->b
      stack_entryt &entry=path.back();
      if(entry.next==weg[entry.n].out.end())
      {
        // no further successor
        path.pop_back();
        continue;
      }

      entry.edge=entry.next;
      entry.next++;
      wegt::node_indext b=entry.edge->first;

      if(visited[b])
        continue; // already done it

      visited[b]=true;

      // add node 'b' to path
      path.push_back(stack_entryt(b, weg[b].out.begin()));

      // process
      process_weg_path(path);
    }
  }

  // add the Ackermann constraints
  add_array_Ackermann_constraints();
}

void arrayst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#if 0
  std::cout << "arrays.size(): " << arrays.size() << '\n';
#endif

  // iterate over arrays
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    const index_sett &index_set=index_map[i];

#if 0
    std::cout << "index_set.size(): " << index_set.size() << '\n';
#endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator
        i1=index_set.begin();
        i1!=index_set.end();
        i1++)
    {
      index_sett::const_iterator next=i1;
      next++;
      for(index_sett::const_iterator
          i2=next;
          i2!=index_set.end();
          i2++)
      {
        if(i1->is_constant() && i2->is_constant())
          continue;

        // index equality
        equal_exprt indices_equal(*i1, *i2);

        if(indices_equal.op0().type()!=
           indices_equal.op1().type())
        {
          indices_equal.op1().
            make_typecast(indices_equal.op0().type());
        }

        literalt indices_equal_lit=convert(indices_equal);

        if(indices_equal_lit!=const_literal(false))
        {
          const typet &subtype=ns.follow(arrays[i].type()).subtype();
          index_exprt index_expr1(arrays[i], *i1, subtype);

          index_exprt index_expr2=index_expr1;
          index_expr2.index()=*i2;

          equal_exprt values_equal(index_expr1, index_expr2);
          prop.lcnf(!indices_equal_lit, convert(values_equal));

#if ARRAY_SPEEDUP_DEBUG
          std::cout << "C4: "
                    << format(indices_equal)
                    << " => "
                    << format(values_equal)
                    << '\n';
#endif
        }
      }
    }
  }
}

