/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "arrays.h"

#include <util/arith_tools.h>
#include <util/json.h>
#include <util/std_expr.h>

#include <solvers/prop/literal_expr.h>
#include <solvers/prop/prop.h>

#ifdef DEBUG_ARRAYST
#  include <iostream>
#endif

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
  // get_array_constraints is true when --show-array-constraints is used
  get_array_constraints = _get_array_constraints;
}

void arrayst::record_array_index(const index_exprt &index)
{
  collect_indices(index);
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

  literalt l = SUB::equality(op0, op1);
#ifdef DEBUG_ARRAYST
  std::cout << "LIT " << l.get() << " == " << format(equality) << '\n';
#endif

  wegt::node_indext a1 = collect_arrays(op0);
  wegt::node_indext a2 = collect_arrays(op1);

  // one undirected edge for each array equality
  add_weg_edge(a1, a2, literal_exprt{l});

  return l;
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

    collect_indices(e.index());
    collect_indices(e.array());

    const typet &array_op_type = e.array().type();

    if(array_op_type.id()==ID_array)
    {
      const array_typet &array_type=
        to_array_type(array_op_type);

      if(is_unbounded_array(array_type))
      {
#ifdef DEBUG_ARRAYST
        std::cout << "RAI: " << format(e) << '\n';
#endif
        wegt::node_indext number = collect_arrays(e.array());
        index_map[number].insert(e.index());
      }
    }
  }
}

arrayst::wegt::node_indext arrayst::collect_arrays(const exprt &a)
{
  wegt::node_indext a_ind = arrays.number(a);
  expand_weg(a_ind);

  const array_typet &array_type = to_array_type(a.type());

  // remember it
  if(a.id()==ID_with)
  {
    const with_exprt &with_expr=to_with_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == with_expr.old().type(),
      "collect_arrays got 'with' without matching types",
      irep_pretty_diagnosticst{a});

    for(std::size_t i = 1; i < with_expr.operands().size(); i += 2)
    {
      collect_indices(with_expr.operands()[i]);     // where
      collect_indices(with_expr.operands()[i + 1]); // new value
    }

    // record 'old'
    wegt::node_indext expr_old_ind = collect_arrays(with_expr.old());

    // one undirected edge for each array update
    add_weg_edge(a_ind, expr_old_ind, with_expr);
  }
  else if(a.id()==ID_update)
  {
    const update_exprt &update_expr=to_update_expr(a);

    DATA_INVARIANT_WITH_DIAGNOSTICS(
      array_type == update_expr.old().type(),
      "collect_arrays got 'update' without matching types",
      irep_pretty_diagnosticst{a});

    UNIMPLEMENTED;
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

    wegt::node_indext expr_true_ind = collect_arrays(if_expr.true_case());
    wegt::node_indext expr_false_ind = collect_arrays(if_expr.false_case());

    // do weg edges
    literalt cond = convert(if_expr.cond());
#ifdef DEBUG_ARRAYST
    std::cout << "LIT " << cond.get() << " == " << format(if_expr.cond())
              << '\n';
#endif
    add_weg_edge(a_ind, expr_true_ind, literal_exprt{cond});
    add_weg_edge(a_ind, expr_false_ind, literal_exprt{!cond});
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
  else if(a.id() == ID_array || a.id() == ID_string_constant)
  {
  }
  else if(a.id()==ID_array_of)
  {
  }
  else if(a.id()==ID_typecast)
  {
    const auto &typecast_op = to_typecast_expr(a).op();

    // cast between array types?
    DATA_INVARIANT(
      typecast_op.type().id() == ID_array,
      "unexpected array type cast from " + typecast_op.type().id_string());

    wegt::node_indext op_ind = collect_arrays(typecast_op);

    add_weg_edge(a_ind, op_ind, literal_exprt{const_literal(true)});
  }
  else if(a.id()==ID_index)
  {
    // an array of arrays!
    const exprt &array = to_index_expr(a).array();

    collect_arrays(array);
  }
  else if(a.id() == ID_array_comprehension)
  {
    const array_comprehension_exprt &array_comprehension =
      to_array_comprehension_expr(a);
    collect_indices(array_comprehension.body());
  }
  else
    throw "unexpected array expression (collect_arrays): `" + a.id_string() +
      "'";

  return a_ind;
}

void arrayst::weg_path_condition(
  const weg_patht &path,
  const exprt &index_a,
  exprt::operandst &cond) const
{
  for(const auto &pn : path)
  {
    if(!pn.edge.has_value())
      break;

#ifdef DEBUG_ARRAYST
    std::cout << "edge: " << pn.n << "->" << (*pn.edge)->first << " "
              << format(arrays[pn.n]) << "\n";
#endif

    const exprt &weg_edge = (*pn.edge)->second;

    // TODO: we should filter out trivially-false conjunctions when literals and
    // their negations or equalities and their notequal counterparts are
    // included
    if(weg_edge.id() == ID_with)
    {
      const auto &with_expr = to_with_expr(weg_edge);
      for(std::size_t i = 1; i + 1 < with_expr.operands().size(); i += 2)
      {
        notequal_exprt inequality(with_expr.operands()[i], index_a);
        cond.push_back(inequality);
      }
    }
    else if(
      weg_edge.id() == ID_literal &&
      weg_edge != literal_exprt{const_literal(true)})
    {
      cond.push_back(weg_edge);
    }
    else
      UNIMPLEMENTED;
  }
}

void arrayst::process_weg_path(const weg_patht &path)
{
  INVARIANT(!path.empty(), "path is not empty");
  wegt::node_indext a = path.front().n;
  wegt::node_indext b = path.back().n;

#ifdef DEBUG_ARRAYST
  std::cout << "PATH: ";
  for(const auto &n : path)
    std::cout << n.n << ",";
  std::cout << '\n';
#endif

  // do constraints
  const index_sett &index_set_a = index_map[a];
  const index_sett &index_set_b = index_map[b];

#ifdef DEBUG_ARRAYST
  std::cout << "b is: " << format(arrays[b]) << '\n';
#endif

  for(const auto &index_a : index_set_a)
  {
    // lazily instantiate read-over-write
    if(arrays[b].id() == ID_with)
    {
#if 0
      // we got x=(y with [i:=v, j:=w, ...])
      const auto &expr_b = to_with_expr(arrays[b]);
      for(std::size_t i = 1; i + 1 < expr_b.operands().size(); i += 2)
      {
        const exprt &index_b = expr_b.operands()[i];
        const exprt &value_b = expr_b.operands()[i + 1];

        // 1. we got a[i]...b[j], given as edges on the stack
        // 2. add (i=j AND path_cond)=>a[i]=b[j]
        // 3. The path condition requires the update indices
        //    on the stack to be different from i.
        exprt::operandst cond;
        cond.reserve(path.size() + 1);
        cond.push_back(equal_exprt(index_a, index_b));
        weg_path_condition(path, index_a, cond);

        // a_i=b_i
        index_exprt a_i(arrays[a], index_a);
        // cond => a_i=b_i
        implies_exprt implication(conjunction(cond), equal_exprt(a_i, value_b));
#  ifdef DEBUG_ARRAYST
        std::cout << "C2a: " << format(implication) << '\n';
#  endif
        set_to_true(implication);
      }
#endif
    }
    else if(arrays[b].id() == ID_array_of)
    {
#if 0
      const auto &expr_b = to_array_of_expr(arrays[b]);
      const exprt &value_b = expr_b.what();

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
      implies_exprt implication(conjunction(cond), equal_exprt(a_i, value_b));
#  ifdef DEBUG_ARRAYST
      std::cout << "C2b: " << format(implication) << '\n';
#  endif
      set_to_true(implication);
#endif
    }
    else if(arrays[b].id() == ID_array)
    {
#if 0
      // we got x=[a, b, c, ...]
      const auto &array_expr = to_array_expr(arrays[b]);
      for(std::size_t i = 0; i < array_expr.operands().size(); ++i)
      {
        const exprt index_b = from_integer(i, index_a.type());
        const exprt &value_b = array_expr.operands()[i];

        // 1. we got a[i]...b[j], given as edges on the stack
        // 2. add (i=j AND path_cond)=>a[i]=b[j]
        // 3. The path condition requires the update indices
        //    on the stack to be different from i.
        exprt::operandst cond;
        cond.reserve(path.size() + 1);
        cond.push_back(equal_exprt(index_a, index_b));
        weg_path_condition(path, index_a, cond);

        // a_i=b_i
        index_exprt a_i(arrays[a], index_a);
        // cond => a_i=b_i
        implies_exprt implication(conjunction(cond), equal_exprt(a_i, value_b));
#  ifdef DEBUG_ARRAYST
        std::cout << "C2c: " << format(implication) << '\n';
#  endif
        set_to_true(implication);
      }
#endif
    }
    else if(arrays[b].id() == ID_array_comprehension)
    {
#if 0
      const auto &expr_b = to_array_comprehension_expr(arrays[b]);
      exprt value_b = expr_b.instantiate({index_a});

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
      implies_exprt implication(true_exprt{}, /*conjunction(cond),*/ equal_exprt(a_i, value_b));
#  ifdef DEBUG_ARRAYST
      std::cout << "C2d: " << format(implication) << '\n';
#  endif
      set_to_true(implication);
#endif
    }
    else
    {
      DATA_INVARIANT_WITH_DIAGNOSTICS(
        arrays[b].id() == ID_nondet_symbol || arrays[b].id() == ID_symbol ||
          arrays[b].id() == ID_if || arrays[b].id() == ID_index,
        "expected symbol, if, or index; got ",
        arrays[b].pretty());
    }

    // TODO: a != b should be trivially true as we don't do self loops
    if(
      a !=
      b) // we handle same-array-different index in add_array_Ackermann_constraints
    {
      for(const auto &index_b : index_set_b)
      {
        // skip over comparisons that are trivially false
        if(index_a.is_constant() && index_b.is_constant() && index_a != index_b)
        {
          continue;
        }

        // 1. we got a[i]...b[j], given as edges on the stack
        // 2. add (i=j AND path_cond)=>a[i]=b[j]
        // 3. The path condition requires the update indices
        //    on the stack to be different from i.
        exprt::operandst cond;
        cond.reserve(path.size() + 1);
        cond.push_back(equal_exprt(index_a, index_b));
        weg_path_condition(path, index_a, cond);

        // a_i=b_i
        index_exprt a_i(arrays[a], index_a);
        index_exprt b_i(arrays[b], index_b);
        // cond => a_i=b_i
        implies_exprt implication(conjunction(cond), equal_exprt(a_i, b_i));
#ifdef DEBUG_ARRAYST
        std::cout << "C3: " << format(implication) << '\n';
#endif
        set_to_true(implication);
      }
    }
  }

#if 0
  // extensional array encoding -- do this first as it may add to the index sets
  if(a != b)
  {
    exprt::operandst cond;
    cond.reserve(path.size());
    // collect all indices in with expressions along this path
    // record the first and last with expression
    // compute the path condition from a to first and last to b
    //weg_path_condition(path, nil_exprt{}, cond);

    implies_exprt implication(conjunction(cond), equal_exprt(arrays[a], arrays[b]));
#  ifdef DEBUG_ARRAYST
    std::cout << "E1: " << format(implication) << '\n';
#  endif
    set_to_true(implication);
  }
#endif
}

void arrayst::add_array_constraints()
{
  // preprocessing
  for(std::size_t i = 0; i < arrays.size(); ++i)
  {
    if(arrays[i].id() == ID_array)
    {
      const auto &array_expr = to_array_expr(arrays[i]);

      for(std::size_t j = 0; j < array_expr.operands().size(); ++j)
      {
        const exprt index_constant =
          from_integer(j, to_array_type(array_expr.type()).index_type());
        const exprt &value = array_expr.operands()[j];

        index_map[i].insert(index_constant);
        equal_exprt eq{index_exprt{array_expr, index_constant}, value};
#ifdef DEBUG_ARRAYST
        std::cout << "PREPROC: " << format(eq) << '\n';
#endif
        set_to_true(eq);
      }
    }
    else if(arrays[i].id() == ID_array_comprehension)
    {
      const auto &array_comprehension = to_array_comprehension_expr(arrays[i]);
      for(const auto r : weg.get_reachable(i, true))
        index_map[i].insert(index_map[r].begin(), index_map[r].end());

      for(const auto &index : index_map[i])
      {
        equal_exprt eq{
          index_exprt{array_comprehension, index},
          array_comprehension.instantiate({index})};
#ifdef DEBUG_ARRAYST
        std::cout << "PREPROC: " << format(eq) << '\n';
#endif
        set_to_true(eq);
      }
    }
    else if(arrays[i].id() == ID_array_of)
    {
      const auto &array_of_expr = to_array_of_expr(arrays[i]);
      const auto &value = array_of_expr.what();

      for(const auto &index : index_map[i])
      {
        equal_exprt eq{index_exprt{array_of_expr, index}, value};
#ifdef DEBUG_ARRAYST
        std::cout << "PREPROC: " << format(eq) << '\n';
#endif
        set_to_true(eq);
      }
    }
    else if(arrays[i].id() == ID_with)
    {
      const with_exprt &with_expr = to_with_expr(arrays[i]);

      for(std::size_t j = 1; j < with_expr.operands().size(); j += 2)
      {
        index_map[i].insert(with_expr.operands()[j]);
        equal_exprt eq{
          index_exprt{with_expr, with_expr.operands()[j]},
          with_expr.operands()[j + 1]};
#ifdef DEBUG_ARRAYST
        std::cout << "PREPROC: " << format(eq) << '\n';
#endif
        set_to_true(eq);
      }
    }
  }

#ifdef DEBUG_ARRAYST
  weg.output_dot(std::cout);
  for(std::size_t i = 0; i < arrays.size(); ++i)
  {
    std::cout << "IS of " << i << ":";
    for(const auto &ind : index_map[i])
      std::cout << " " << format(ind);
    std::cout << '\n';
  }
#endif

#ifdef DEBUG_ARRAYST
  for(const auto &a : arrays)
  {
    std::cout << "array: " << format(a) << '\n';
  }
#endif

  // Implement Algorithms 7.4.1 and 7.4.2 by enumerating all simple paths
  // instead of iterating over all pairs of arrays and indices. Paths are
  // enumerated by performing depth-first search from each node.

  // auxiliary bit per node for DFS
  std::vector<bool> visited;
  visited.resize(weg.size());

  for(wegt::node_indext a = 0; a < arrays.size(); a++)
  {
#ifdef DEBUG_ARRAYST
    std::cout << "a is: " << format(arrays[a]) << '\n';
#endif

    // DFS from a_i to anything reachable in 'weg'
    std::fill(visited.begin(), visited.end(), false);

    weg_patht path;
    path.emplace_back(a, std::set<wegt::node_indext>());
    visited[a] = true;

    while(!path.empty())
    {
      // get next edge a->b
      stack_entryt &entry = path.back();

      if(!entry.edge.has_value())
      {
        if(weg[entry.n].out.empty())
        {
          // no successors
          path.pop_back();
          continue;
        }

        entry.edge = weg[entry.n].out.cbegin();
      }
      else if(std::next(*entry.edge) == weg[entry.n].out.end())
      {
        // no further successor
        path.pop_back();
        continue;
      }
      else
        ++(*entry.edge);

      wegt::node_indext b = (*entry.edge)->first;

      if(entry.path_nodes.find(b) != entry.path_nodes.end())
        continue; // already done it

      visited[b] = true;

      // add node 'b' to path
      path.emplace_back(b, entry.path_nodes);

      // process
      process_weg_path(path);
    }
  }

  // add the Ackermann constraints
  add_array_Ackermann_constraints();
}

#if 1
void arrayst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#  ifdef DEBUG_ARRAYST
  std::cout << "arrays.size(): " << arrays.size() << '\n';
#  endif

  // iterate over arrays
  // TODO: not clear when we really need this: certainly with arrays[i] ==
  // ID_array, perhaps also in other cases
  for(std::size_t i = 0; i < arrays.size(); i++)
  {
    const index_sett &index_set = index_map[i];

#  ifdef DEBUG_ARRAYST
    std::cout << "index_set.size(): " << index_set.size() << '\n';
#  endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator i1 = index_set.begin();
        i1 != index_set.end();
        i1++)
    {
      index_sett::const_iterator next = i1;
      next++;
      for(index_sett::const_iterator i2 = next; i2 != index_set.end(); i2++)
      {
        if(i1->is_constant() && i2->is_constant())
          continue;

        // index equality
        equal_exprt indices_equal(*i1, *i2);

        if(indices_equal.op0().type() != indices_equal.op1().type())
        {
          indices_equal.op1() =
            typecast_exprt(indices_equal.op1(), indices_equal.op0().type());
        }

        literalt indices_equal_lit = convert(indices_equal);

        if(indices_equal_lit != const_literal(false))
        {
          const typet &subtype = arrays[i].type().subtype();
          index_exprt index_expr1(arrays[i], *i1, subtype);

          index_exprt index_expr2 = index_expr1;
          index_expr2.index() = *i2;

          equal_exprt values_equal(index_expr1, index_expr2);
          prop.lcnf(!indices_equal_lit, convert(values_equal));

#  ifdef DEBUG_ARRAYST
          std::cout << "C4: " << format(indices_equal) << " => "
                    << format(values_equal) << '\n';
#  endif
        }
      }
    }
  }
}
#endif

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
