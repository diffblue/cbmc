/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "prop_conv.h"
#include <algorithm>

/// determine whether a variable is in the final conflict
bool prop_convt::is_in_conflict(literalt) const
{
  UNREACHABLE;
  return false;
}

void prop_convt::set_assumptions(const bvt &)
{
  UNREACHABLE;
}

void prop_convt::set_frozen(const literalt)
{
  UNREACHABLE;
}

void prop_convt::set_frozen(const bvt &bv)
{
  for(const auto &bit : bv)
    if(!bit.is_constant())
      set_frozen(bit);
}

bool prop_conv_solvert::literal(const symbol_exprt &expr, literalt &dest) const
{
  PRECONDITION(expr.type().id() == ID_bool);

  const irep_idt &identifier = expr.get_identifier();

  symbolst::const_iterator result = symbols.find(identifier);

  if(result == symbols.end())
    return true;

  dest = result->second;
  return false;
}

literalt prop_conv_solvert::get_literal(const irep_idt &identifier)
{
  auto result =
    symbols.insert(std::pair<irep_idt, literalt>(identifier, literalt()));

  if(!result.second)
    return result.first->second;

  literalt literal=prop.new_variable();
  prop.set_variable_name(literal, identifier);

  // insert
  result.first->second=literal;

  return literal;
}

/// get a boolean value from counter example if not valid
bool prop_conv_solvert::get_bool(const exprt &expr, tvt &value) const
{
  // trivial cases

  if(expr.is_true())
  {
    value=tvt(true);
    return false;
  }
  else if(expr.is_false())
  {
    value=tvt(false);
    return false;
  }
  else if(expr.id()==ID_symbol)
  {
    symbolst::const_iterator result=
      symbols.find(to_symbol_expr(expr).get_identifier());

    if(result==symbols.end())
      return true;

    value=prop.l_get(result->second);
    return false;
  }

  // sub-expressions

  if(expr.id()==ID_not)
  {
    if(expr.type().id()==ID_bool &&
       expr.operands().size()==1)
    {
      if(get_bool(expr.op0(), value))
        return true;
      value=!value;
      return false;
    }
  }
  else if(expr.id()==ID_and || expr.id()==ID_or)
  {
    if(expr.type().id()==ID_bool &&
       expr.operands().size()>=1)
    {
      value=tvt(expr.id()==ID_and);

      forall_operands(it, expr)
      {
        tvt tmp;
        if(get_bool(*it, tmp))
          return true;

        if(expr.id()==ID_and)
        {
          if(tmp.is_false())
          {
            value=tvt(false);
            return false;
          }

          value=value && tmp;
        }
        else // or
        {
          if(tmp.is_true())
          {
            value=tvt(true);
            return false;
          }

          value=value || tmp;
        }
      }

      return false;
    }
  }

  // check cache

  cachet::const_iterator cache_result=cache.find(expr);
  if(cache_result==cache.end())
    return true;

  value=prop.l_get(cache_result->second);
  return false;
}

literalt prop_conv_solvert::convert(const exprt &expr)
{
  if(!use_cache ||
     expr.id()==ID_symbol ||
     expr.id()==ID_constant)
  {
    literalt literal=convert_bool(expr);
    if(freeze_all && !literal.is_constant())
      prop.set_frozen(literal);
    return literal;
  }

  // check cache first
  auto result = cache.insert({expr, literalt()});

  if(!result.second)
    return result.first->second;

  literalt literal=convert_bool(expr);

  // insert into cache

  result.first->second=literal;
  if(freeze_all && !literal.is_constant())
    prop.set_frozen(literal);

  #if 0
  std::cout << literal << "=" << expr << '\n';
  #endif

  return literal;
}

literalt prop_conv_solvert::convert_bool(const exprt &expr)
{
  PRECONDITION(expr.type().id() == ID_bool);

  const exprt::operandst &op=expr.operands();

  if(expr.is_constant())
  {
    if(expr.is_true())
      return const_literal(true);
    else
    {
      INVARIANT(
        expr.is_false(),
        "constant expression of type bool should be either true or false");
      return const_literal(false);
    }
  }
  else if(expr.id()==ID_symbol)
  {
    return get_literal(to_symbol_expr(expr).get_identifier());
  }
  else if(expr.id()==ID_literal)
  {
    return to_literal_expr(expr).get_literal();
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    return prop.new_variable();
  }
  else if(expr.id()==ID_implies)
  {
    const implies_exprt &implies_expr = to_implies_expr(expr);
    return prop.limplies(
      convert(implies_expr.op0()), convert(implies_expr.op1()));
  }
  else if(expr.id()==ID_if)
  {
    const if_exprt &if_expr = to_if_expr(expr);
    return prop.lselect(
      convert(if_expr.cond()),
      convert(if_expr.true_case()),
      convert(if_expr.false_case()));
  }
  else if(expr.id()==ID_constraint_select_one)
  {
    DATA_INVARIANT(
      op.size() >= 2,
      "constraint_select_one should have at least two operands");

    std::vector<literalt> op_bv;
    op_bv.resize(op.size());

    unsigned i=0;
    forall_operands(it, expr)
      op_bv[i++]=convert(*it);

    // add constraints

    bvt b;
    b.reserve(op_bv.size()-1);

    for(unsigned i=1; i<op_bv.size(); i++)
      b.push_back(prop.lequal(op_bv[0], op_bv[i]));

    prop.l_set_to_true(prop.lor(b));

    return op_bv[0];
  }
  else if(expr.id()==ID_or || expr.id()==ID_and || expr.id()==ID_xor ||
          expr.id()==ID_nor || expr.id()==ID_nand)
  {
    INVARIANT(
      !op.empty(),
      "operator `" + expr.id_string() + "' takes at least one operand");

    bvt bv;

    forall_expr(it, op)
      bv.push_back(convert(*it));

    if(!bv.empty())
    {
      if(expr.id()==ID_or)
        return prop.lor(bv);
      else if(expr.id()==ID_nor)
        return !prop.lor(bv);
      else if(expr.id()==ID_and)
        return prop.land(bv);
      else if(expr.id()==ID_nand)
        return !prop.land(bv);
      else if(expr.id()==ID_xor)
        return prop.lxor(bv);
    }
  }
  else if(expr.id()==ID_not)
  {
    INVARIANT(op.size() == 1, "not takes one operand");
    return !convert(op.front());
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    INVARIANT(op.size() == 2, "equality takes two operands");
    bool equal=(expr.id()==ID_equal);

    if(op[0].type().id()==ID_bool &&
       op[1].type().id()==ID_bool)
    {
      literalt tmp1=convert(op[0]),
               tmp2=convert(op[1]);
      return
        equal?prop.lequal(tmp1, tmp2):prop.lxor(tmp1, tmp2);
    }
  }
  else if(expr.id()==ID_let)
  {
    const let_exprt &let_expr=to_let_expr(expr);

    // first check whether this is all boolean
    if(let_expr.value().type().id()==ID_bool &&
       let_expr.where().type().id()==ID_bool)
    {
      literalt value=convert(let_expr.value());

      // We expect the identifier of the bound symbols to be unique,
      // and thus, these can go straight into the symbol map.
      // This property also allows us to cache any subexpressions.
      const irep_idt &id=let_expr.symbol().get_identifier();
      symbols[id]=value;
      literalt result=convert(let_expr.where());

      // remove again
      symbols.erase(id);
      return result;
    }
  }

  return convert_rest(expr);
}

literalt prop_conv_solvert::convert_rest(const exprt &expr)
{
  // fall through
  ignoring(expr);
  return prop.new_variable();
}

bool prop_conv_solvert::set_equality_to_true(const equal_exprt &expr)
{
  if(!equality_propagation)
    return true;

  // optimization for constraint of the form
  // new_variable = value

  if(expr.lhs().id()==ID_symbol)
  {
    const irep_idt &identifier=
      to_symbol_expr(expr.lhs()).get_identifier();

    literalt tmp=convert(expr.rhs());

    std::pair<symbolst::iterator, bool> result=
      symbols.insert(std::pair<irep_idt, literalt>(identifier, tmp));

    if(result.second)
      return false; // ok, inserted!

    // nah, already there
  }

  return true;
}

void prop_conv_solvert::set_to(const exprt &expr, bool value)
{
  PRECONDITION(expr.type().id() == ID_bool);

  const bool has_only_boolean_operands = std::all_of(
    expr.operands().begin(),
    expr.operands().end(),
    [](const exprt &expr) { return expr.type().id() == ID_bool; });

  if(has_only_boolean_operands)
  {
    if(expr.id()==ID_not)
    {
      if(expr.operands().size()==1)
      {
        set_to(expr.op0(), !value);
        return;
      }
    }
    else
    {
      if(value)
      {
        // set_to_true

        if(expr.id()==ID_and)
        {
          forall_operands(it, expr)
            set_to_true(*it);

          return;
        }
        else if(expr.id()==ID_or)
        {
          // Special case for a CNF-clause,
          // i.e., a constraint that's a disjunction.

          if(!expr.operands().empty())
          {
            bvt bv;
            bv.reserve(expr.operands().size());

            forall_operands(it, expr)
              bv.push_back(convert(*it));

            prop.lcnf(bv);
            return;
          }
        }
        else if(expr.id()==ID_implies)
        {
          if(expr.operands().size()==2)
          {
            literalt l0=convert(expr.op0());
            literalt l1=convert(expr.op1());
            prop.lcnf(!l0, l1);
            return;
          }
        }
        else if(expr.id()==ID_equal)
        {
          if(!set_equality_to_true(to_equal_expr(expr)))
            return;
        }
      }
      else
      {
        // set_to_false
        if(expr.id()==ID_implies) // !(a=>b)  ==  (a && !b)
        {
          const implies_exprt &implies_expr = to_implies_expr(expr);

          set_to_true(implies_expr.op0());
          set_to_false(implies_expr.op1());
          return;
        }
        else if(expr.id()==ID_or) // !(a || b)  ==  (!a && !b)
        {
          forall_operands(it, expr)
            set_to_false(*it);
          return;
        }
      }
    }
  }

  // fall back to convert
  prop.l_set_to(convert(expr), value);
}

void prop_conv_solvert::ignoring(const exprt &expr)
{
  // fall through

  warning() << "warning: ignoring " << expr.pretty() << eom;
}

void prop_conv_solvert::post_process()
{
}

decision_proceduret::resultt prop_conv_solvert::dec_solve()
{
  // post-processing isn't incremental yet
  if(!post_processing_done)
  {
    statistics() << "Post-processing" << eom;
    post_process();
    post_processing_done=true;
  }

  statistics() << "Solving with " << prop.solver_text() << eom;

  switch(prop.prop_solve())
  {
    case propt::resultt::P_SATISFIABLE: return resultt::D_SATISFIABLE;
    case propt::resultt::P_UNSATISFIABLE: return resultt::D_UNSATISFIABLE;
    default: return resultt::D_ERROR;
  }
}

exprt prop_conv_solvert::get(const exprt &expr) const
{
  tvt value;

  if(expr.type().id()==ID_bool &&
     !get_bool(expr, value))
  {
    switch(value.get_value())
    {
     case tvt::tv_enumt::TV_TRUE:  return true_exprt();
     case tvt::tv_enumt::TV_FALSE: return false_exprt();
     case tvt::tv_enumt::TV_UNKNOWN: return false_exprt(); // default
    }
  }

  exprt tmp = expr;
  for(auto &op : tmp.operands())
  {
    exprt tmp_op = get(op);
    op.swap(tmp_op);
  }
  return tmp;
}

void prop_conv_solvert::print_assignment(std::ostream &out) const
{
  for(const auto &symbol : symbols)
    out << symbol.first << " = " << prop.l_get(symbol.second) << '\n';
}
