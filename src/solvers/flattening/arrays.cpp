/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

//#define DEBUG

#include <cassert>
#include <iostream>

#include <langapi/language_util.h>

#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/arith_tools.h>
#include <util/base_type.h>
#include <util/namespace.h>

#include <solvers/prop/prop.h>

#include "arrays.h"

/*******************************************************************\

Function: arrayst::arrayst

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

arrayst::arrayst(
  const namespacet &_ns,
  propt &_prop):equalityt(_ns, _prop)
{
  lazy_arrays = false;        // will be set to true when --refine is used
  incremental_cache = false;  // for incremental solving
}

/*******************************************************************\

Function: arrayst::record_array_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::record_array_index(const index_exprt &index)
{
  // we are not allowed to put the index directly in the
  //   entry for the root of the equivalence class
  //   because this map is accessed during building the error trace
  std::size_t number=arrays.number(index.array());
  index_map[number].insert(index.index());
  update_indices.insert(number);
}

/*******************************************************************\

Function: arrayst::record_array_equality

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt arrayst::record_array_equality(
  const equal_exprt &equality)
{
  const exprt &op0=equality.op0();
  const exprt &op1=equality.op1();

  // check types
  if(!base_type_eq(op0.type(), op1.type(), ns))
  {
    std::cout << equality.pretty() << std::endl;
    throw "record_array_equality got equality without matching types";
  }

  assert(ns.follow(op0.type()).id()==ID_array);

  array_equalities.push_back(array_equalityt());

  array_equalities.back().f1=op0;
  array_equalities.back().f2=op1;
  array_equalities.back().l=SUB::equality(op0, op1);

  arrays.make_union(op0, op1);
  collect_arrays(op0);
  collect_arrays(op1);

  return array_equalities.back().l;
}

/*******************************************************************\

Function: arrayst::collect_indices

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
    forall_operands(op,expr) collect_indices(*op);
  }
  else
  {
    const index_exprt &e = to_index_expr(expr);
    collect_indices(e.index()); //necessary?

    const typet &array_op_type=ns.follow(e.array().type());

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

/*******************************************************************\

Function: arrayst::collect_arrays

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::collect_arrays(const exprt &a)
{
  const array_typet &array_type=
    to_array_type(ns.follow(a.type()));

  if(a.id()==ID_with)
  {
    if(a.operands().size()!=3)
      throw "with expected to have three operands";

    // check types
    if(!base_type_eq(array_type, a.op0().type(), ns))
    {
      std::cout << a.pretty() << std::endl;
      throw "collect_arrays got 'with' without matching types";
    }

    arrays.make_union(a, a.op0());
    collect_arrays(a.op0());

    // make sure this shows as an application
    index_exprt index_expr;
    index_expr.type()=array_type.subtype();
    index_expr.array()=a.op0();
    index_expr.index()=a.op1();
    record_array_index(index_expr);
  }
  else if(a.id()==ID_update) //TODO: is this obsolete?
  {
    if(a.operands().size()!=3)
      throw "update expected to have three operands";

    // check types
    if(!base_type_eq(array_type, a.op0().type(), ns))
    {
      std::cout << a.pretty() << std::endl;
      throw "collect_arrays got 'update' without matching types";
    }

    arrays.make_union(a, a.op0());
    collect_arrays(a.op0());

#if 0
    // make sure this shows as an application
    index_exprt index_expr;
    index_expr.type()=array_type.subtype();
    index_expr.array()=a.op0();
    index_expr.index()=a.op1();
    record_array_index(index_expr);
#endif
  }
  else if(a.id()==ID_if)
  {
    if(a.operands().size()!=3)
      throw "if expected to have three operands";

    // check types
    if(!base_type_eq(array_type, a.op1().type(), ns))
    {
      std::cout << a.pretty() << std::endl;
      throw "collect_arrays got if without matching types";
    }

    // check types
    if(!base_type_eq(array_type, a.op2().type(), ns))
    {
      std::cout << a.pretty() << std::endl;
      throw "collect_arrays got if without matching types";
    }

    arrays.make_union(a, a.op1());
    arrays.make_union(a, a.op2());
    collect_arrays(a.op1());
    collect_arrays(a.op2());
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
      throw "unexpected array expression: member with `"+a.op0().id_string()+"'";
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
    assert(0);
  }
  else if(a.id()==ID_typecast)
  {
    // cast between array types?
    assert(a.operands().size()==1);

    if(a.op0().type().id()==ID_array)
    {
      arrays.make_union(a, a.op0());
      collect_arrays(a.op0());
    }
    else
      throw "unexpected array type cast from "+a.op0().type().id_string();
  }
  else if(a.id()==ID_index)
  {
    // nested unbounded arrays
    arrays.make_union(a, a.op0());
    collect_arrays(a.op0());
  }
  else
    throw "unexpected array expression (collect_arrays): `"+a.id_string()+"'";
}

/*******************************************************************\

Function: arrayst::add_array_constraint

  Inputs:

 Outputs:

 Purpose: adds array constraints
          (refine=true...lazily for the refinement loop)

\*******************************************************************/


void arrayst::add_array_constraint(const lazy_constraintt &lazy, bool refine)
{
  if (lazy_arrays && refine)
  {
    // lazily add the constraint
    if (incremental_cache)
    {
      if (expr_map.find(lazy.lazy) == expr_map.end())
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

/*******************************************************************\

Function: arrayst::add_array_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::add_array_constraints()
{
  collect_indices();
  // at this point all indices should in the index set

  // reduce initial index map
  update_index_map(true);

  // add constraints for if, with, array_of
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    // take a copy as arrays may get modified by add_array_constraints
    // in case of nested unbounded arrays
    exprt a=arrays[i];

    add_array_constraints(index_map[arrays.find_number(i)], a);

    //we have to update before it gets used in the next add_* call
    update_index_map(false);
  }

  // add constraints for equalities
  for(array_equalitiest::const_iterator it=
      array_equalities.begin();
      it!=array_equalities.end();
      it++)
  {
    add_array_constraints(
      index_map[arrays.find_number(it->f1)],
      *it);

    // update_index_map should not be necessary here
  }

  // add the Ackermann constraints
  add_array_Ackermann_constraints();
}

/*******************************************************************\

Function: arrayst::add_array_Ackermann_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::add_array_Ackermann_constraints()
{
  // this is quadratic!

#if 0
  std::cout << "arrays.size(): " << arrays.size() << std::endl;
#endif

  // iterate over arrays
  for(std::size_t i=0; i<arrays.size(); i++)
  {
    const index_sett &index_set=index_map[arrays.find_number(i)];

#if 0
    std::cout << "index_set.size(): " << index_set.size() << std::endl;
#endif

    // iterate over indices, 2x!
    for(index_sett::const_iterator
        i1=index_set.begin();
        i1!=index_set.end();
        i1++)
      for(index_sett::const_iterator
          i2=index_set.begin();
          i2!=index_set.end();
          i2++)
        if(i1!=i2)
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
            index_exprt index_expr1;
            index_expr1.type()=ns.follow(arrays[i].type()).subtype();
            index_expr1.array()=arrays[i];
            index_expr1.index()=*i1;

            index_exprt index_expr2=index_expr1;
            index_expr2.index()=*i2;

            equal_exprt values_equal(index_expr1, index_expr2);

            //add constraint
            lazy_constraintt lazy(ARRAY_ACKERMANN,
              or_exprt(literal_exprt(!indices_equal_lit), values_equal));
            add_array_constraint(lazy, true); //added lazily

#if 0 // old code for adding, not significantly faster
            prop.lcnf(!indices_equal_lit, convert(values_equal));
#endif
          }
        }
  }
}

/*******************************************************************\

Function: arrayst::update_index_map

  Inputs:

 Outputs:

 Purpose: merge the indices into the root

\*******************************************************************/

void arrayst::update_index_map(std::size_t i)
{
  if(arrays.is_root_number(i))
    return;

  std::size_t root_number=arrays.find_number(i);
  assert(root_number!=i);

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
    for(std::size_t i=0; i<arrays.size(); i++)
      update_index_map(i);
  else
  {
    for(std::set<std::size_t>::const_iterator
        it=update_indices.begin();
        it!=update_indices.end(); it++)
      update_index_map(*it);
    update_indices.clear();
  }

#ifdef DEBUG
  //print index sets
  for(index_mapt::const_iterator
      i1=index_map.begin();
      i1!=index_map.end();
      i1++)
    for(index_sett::const_iterator
        i2=i1->second.begin();
        i2!=i1->second.end();
        i2++)
      std::cout << "Index set (" << i1->first << " = "
                << arrays.find_number(i1->first) << " = "
                << from_expr(ns,"",arrays[arrays.find_number(i1->first)]) << "): "
                << from_expr(ns,"",*i2) << std::endl;
   std::cout << "-----" << std::endl;
#endif
}

/*******************************************************************\

Function: arrayst::add_array_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::add_array_constraints(
  const index_sett &index_set,
  const array_equalityt &array_equality)
{
  // add constraints x=y => x[i]=y[i]

  for(index_sett::const_iterator
      it=index_set.begin();
      it!=index_set.end();
      it++)
  {
    index_exprt index_expr1;
    index_expr1.type()=ns.follow(array_equality.f1.type()).subtype();
    index_expr1.array()=array_equality.f1;
    index_expr1.index()=*it;

    index_exprt index_expr2;
    index_expr2.type()=ns.follow(array_equality.f2.type()).subtype();
    index_expr2.array()=array_equality.f2;
    index_expr2.index()=*it;

    assert(index_expr1.type()==index_expr2.type());

    array_equalityt equal;
    equal.f1 = index_expr1;
    equal.f2 = index_expr2;
    equal.l = array_equality.l;
    equal_exprt equality_expr(index_expr1, index_expr2);

    // add constraint
    // equality constraints are not added lazily
    // convert must be done to guarantee correct update of the index_set
    prop.lcnf(!array_equality.l, convert(equality_expr));
  }
}

/*******************************************************************\

Function: arrayst::add_array_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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
  else if(expr.id()==ID_symbol ||
          expr.id()==ID_nondet_symbol ||
          expr.id()==ID_constant ||
          expr.id()=="zero_string" ||
          expr.id()==ID_array ||
          expr.id()==ID_string_constant)
  {
  }
  else if(expr.id()==ID_member &&
          to_member_expr(expr).struct_op().id()==ID_symbol)
  {
  }
  else if(expr.id()==ID_byte_update_little_endian ||
          expr.id()==ID_byte_update_big_endian)
  {
    assert(0);
  }
  else if(expr.id()==ID_typecast)
  {
    // we got a=(type[])b
    assert(expr.operands().size()==1);

    // add a[i]=b[i]
    for(index_sett::const_iterator
        it=index_set.begin();
        it!=index_set.end();
        it++)
    {
      index_exprt index_expr1;
      index_expr1.type()=ns.follow(expr.type()).subtype();
      index_expr1.array()=expr;
      index_expr1.index()=*it;

      index_exprt index_expr2;
      index_expr2.type()=ns.follow(expr.type()).subtype();
      index_expr2.array()=expr.op0();
      index_expr2.index()=*it;

      assert(index_expr1.type()==index_expr2.type());

      // add constraint
      lazy_constraintt lazy(ARRAY_TYPECAST,
        equal_exprt(index_expr1, index_expr2));
      add_array_constraint(lazy, false); //added immediately
    }
  }
  else if(expr.id()==ID_index)
  {
  }
  else
    throw "unexpected array expression (add_array_constraints): `"+expr.id_string()+"'";
}

/*******************************************************************\

Function: arrayst::add_array_constraints_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::add_array_constraints_with(
  const index_sett &index_set,
  const with_exprt &expr)
{
  // we got x=(y with [i:=v])
  // add constraint x[i]=v

  const exprt &index=expr.where();
  const exprt &value=expr.new_value();

  {
    index_exprt index_expr;
    index_expr.type()=ns.follow(expr.type()).subtype();
    index_expr.array()=expr;
    index_expr.index()=index;

    if(index_expr.type()!=value.type())
    {
      std::cout << expr.pretty() << std::endl;
      assert(false);
    }

     lazy_constraintt lazy(ARRAY_WITH, equal_exprt(index_expr, value));
     add_array_constraint(lazy,false); //added immediately
  }

  // use other array index applications for "else" case
  // add constraint x[I]=y[I] for I!=i

  for(index_sett::const_iterator
      it=index_set.begin();
      it!=index_set.end();
      it++)
  {
    exprt other_index=*it;

    if(other_index!=index)
    {
      // we first build the guard

      if(other_index.type()!=index.type())
        other_index.make_typecast(index.type());

      literalt guard_lit=convert(equal_exprt(index, other_index));

      if(guard_lit!=const_literal(true))
      {
        index_exprt index_expr1;
        index_expr1.type()=ns.follow(expr.type()).subtype();
        index_expr1.array()=expr;
        index_expr1.index()=other_index;

        index_exprt index_expr2;
        index_expr2.type()=ns.follow(expr.type()).subtype();
        index_expr2.array()=expr.op0();
        index_expr2.index()=other_index;

        assert(index_expr1.type()==index_expr2.type());

        equal_exprt equality_expr(index_expr1, index_expr2);

        // add constraint
        lazy_constraintt lazy(ARRAY_WITH, or_exprt(equality_expr,
                                literal_exprt(guard_lit)));
        add_array_constraint(lazy,false); //added immediately

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

/*******************************************************************\

Function: arrayst::add_array_constraints_update

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::add_array_constraints_update(
  const index_sett &index_set,
  const update_exprt &expr)
{
  // we got x=UPDATE(y, [i], v)
  // add constaint x[i]=v

#if 0
  const exprt &index=expr.where();
  const exprt &value=expr.new_value();

  {
    index_exprt index_expr;
    index_expr.type()=ns.follow(expr.type()).subtype();
    index_expr.array()=expr;
    index_expr.index()=index;

    if(index_expr.type()!=value.type())
    {
      std::cout << expr.pretty() << std::endl;
      assert(false);
    }

    set_to_true(equal_exprt(index_expr, value));
  }

  // use other array index applications for "else" case
  // add constraint x[I]=y[I] for I!=i

  for(index_sett::const_iterator
      it=index_set.begin();
      it!=index_set.end();
      it++)
  {
    exprt other_index=*it;

    if(other_index!=index)
    {
      // we first build the guard

      if(other_index.type()!=index.type())
        other_index.make_typecast(index.type());

      literalt guard_lit=convert(equal_exprt(index, other_index));

      if(guard_lit!=const_literal(true))
      {
        index_exprt index_expr1;
        index_expr1.type()=ns.follow(expr.type()).subtype();
        index_expr1.array()=expr;
        index_expr1.index()=other_index;

        index_exprt index_expr2;
        index_expr2.type()=ns.follow(expr.type()).subtype();
        index_expr2.array()=expr.op0();
        index_expr2.index()=other_index;

        assert(index_expr1.type()==index_expr2.type());

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

/*******************************************************************\

Function: arrayst::add_array_constraints_array_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void arrayst::add_array_constraints_array_of(
  const index_sett &index_set,
  const array_of_exprt &expr)
{
  // we got x=array_of[v]
  // get other array index applications
  // and add constraint x[i]=v

  for(index_sett::const_iterator
      it=index_set.begin();
      it!=index_set.end();
      it++)
  {
    index_exprt index_expr;
    index_expr.type()=ns.follow(expr.type()).subtype();
    index_expr.array()=expr;
    index_expr.index()=*it;

    assert(base_type_eq(index_expr.type(), expr.op0().type(), ns));

    // add constraint
    lazy_constraintt lazy(ARRAY_OF, equal_exprt(index_expr, expr.op0()));
    add_array_constraint(lazy, false); //added immediately
  }
}

/*******************************************************************\

Function: arrayst::add_array_constraints_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

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

  for(index_sett::const_iterator
      it=index_set.begin();
      it!=index_set.end();
      it++)
  {
    index_exprt index_expr1;
    index_expr1.type()=ns.follow(expr.type()).subtype();
    index_expr1.array()=expr;
    index_expr1.index()=*it;

    index_exprt index_expr2;
    index_expr2.type()=ns.follow(expr.type()).subtype();
    index_expr2.array()=expr.true_case();
    index_expr2.index()=*it;

    assert(index_expr1.type()==index_expr2.type());

    // add implication
    lazy_constraintt lazy(ARRAY_IF,
                            or_exprt(literal_exprt(!cond_lit),
                              equal_exprt(index_expr1, index_expr2)));
    add_array_constraint(lazy, false); //added immediately

#if 0 // old code for adding, not significantly faster
    prop.lcnf(!cond_lit, convert(equal_exprt(index_expr1, index_expr2)));
#endif
  }

  // now the false case
  for(index_sett::const_iterator
      it=index_set.begin();
      it!=index_set.end();
      it++)
  {
    index_exprt index_expr1;
    index_expr1.type()=ns.follow(expr.type()).subtype();
    index_expr1.array()=expr;
    index_expr1.index()=*it;

    index_exprt index_expr2;
    index_expr2.type()=ns.follow(expr.type()).subtype();
    index_expr2.array()=expr.false_case();
    index_expr2.index()=*it;

    assert(index_expr1.type()==index_expr2.type());

    // add implication
    lazy_constraintt lazy(ARRAY_IF, or_exprt(literal_exprt(cond_lit),
                          equal_exprt(index_expr1, index_expr2)));
    add_array_constraint(lazy, false); //added immediately

#if 0 //old code for adding, not significantly faster
    prop.lcnf(cond_lit, convert(equal_exprt(index_expr1, index_expr2)));
#endif
  }
}
