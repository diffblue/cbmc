/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "simplify_expr_class.h"

#include "arith_tools.h"
#include "c_types.h"
#include "expr_util.h"
#include "mathematical_expr.h"
#include "namespace.h"
#include "std_expr.h"

#include <unordered_set>

simplify_exprt::resultt<> simplify_exprt::simplify_boolean(const exprt &expr)
{
  if(!expr.has_operands())
    return unchanged(expr);

  if(!expr.is_boolean())
    return unchanged(expr);

  if(expr.id()==ID_implies)
  {
    const auto &implies_expr = to_implies_expr(expr);

    if(!implies_expr.op0().is_boolean() || !implies_expr.op1().is_boolean())
    {
      return unchanged(expr);
    }

    // turn a => b into !a || b

    binary_exprt new_expr = implies_expr;
    new_expr.id(ID_or);
    new_expr.op0() = simplify_not(not_exprt(new_expr.op0()));
    return changed(simplify_boolean(new_expr));
  }
  else if(expr.id()==ID_xor)
  {
    bool no_change = true;
    bool negate = false;

    exprt::operandst new_operands = expr.operands();

    for(exprt::operandst::const_iterator it = new_operands.begin();
        it != new_operands.end();)
    {
      if(!it->is_boolean())
        return unchanged(expr);

      bool erase;

      if(it->is_true())
      {
        erase=true;
        negate=!negate;
      }
      else
        erase=it->is_false();

      if(erase)
      {
        it = new_operands.erase(it);
        no_change = false;
      }
      else
        it++;
    }

    if(new_operands.empty())
    {
      return make_boolean_expr(negate);
    }
    else if(new_operands.size() == 1)
    {
      if(negate)
        return changed(simplify_not(not_exprt(new_operands.front())));
      else
        return std::move(new_operands.front());
    }

    if(!no_change)
    {
      auto tmp = expr;
      tmp.operands() = std::move(new_operands);
      return std::move(tmp);
    }
  }
  else if(expr.id()==ID_and || expr.id()==ID_or)
  {
    std::unordered_set<exprt, irep_hash> expr_set;

    bool no_change = true;
    bool may_be_reducible_to_interval =
      expr.id() == ID_or && expr.operands().size() > 2;
    bool may_be_reducible_to_singleton_interval =
      expr.id() == ID_and && expr.operands().size() == 2;

    exprt::operandst new_operands = expr.operands();

    for(exprt::operandst::const_iterator it = new_operands.begin();
        it != new_operands.end();)
    {
      if(!it->is_boolean())
        return unchanged(expr);

      bool is_true=it->is_true();
      bool is_false=it->is_false();

      if(expr.id()==ID_and && is_false)
      {
        return false_exprt();
      }
      else if(expr.id()==ID_or && is_true)
      {
        return true_exprt();
      }

      bool erase=
        (expr.id()==ID_and ? is_true : is_false) ||
        !expr_set.insert(*it).second;

      if(erase)
      {
        it = new_operands.erase(it);
        no_change = false;
      }
      else
      {
        if(may_be_reducible_to_interval)
          may_be_reducible_to_interval = it->id() == ID_equal;
        it++;
      }
    }

    // NOLINTNEXTLINE(whitespace/line_length)
    // This block reduces singleton intervals like (value >= 255 && value <= 255)
    // to just (value == 255). We also need to be careful with the operands
    // as some of them are erased in the previous step. We proceed only if
    // no operands have been erased (i.e. the expression structure has been
    // preserved by previous simplification rounds.)
    if(may_be_reducible_to_singleton_interval && new_operands.size() == 2)
    {
      struct boundst
      {
        mp_integer lower;
        mp_integer higher;
        exprt non_const_value;
      };
      boundst bounds;

      // Before we do anything else, we need to "pattern match" against the
      // expression and make sure that it has the structure we're looking for.
      // The structure we're looking for is going to be
      //      (value >= 255 && !(value >= 256))   -- 255, 256 values indicative.
      // (this is because previous simplification runs will have transformed
      //  the less_than_or_equal expression to a not(greater_than_or_equal)
      // expression)

      // matching (value >= 255)
      auto const match_first_operand = [&bounds](const exprt &op) -> bool {
        if(
          const auto ge_expr =
            expr_try_dynamic_cast<greater_than_or_equal_exprt>(op))
        {
          // The construction of these expressions ensures that the RHS
          // is constant, therefore if we don't have a constant, it's a
          // different expression, so we bail.
          if(!ge_expr->rhs().is_constant())
            return false;
          if(
            auto int_opt =
              numeric_cast<mp_integer>(to_constant_expr(ge_expr->rhs())))
          {
            bounds.non_const_value = ge_expr->lhs();
            bounds.lower = *int_opt;
            return true;
          }
          return false;
        }
        return false;
      };

      // matching !(value >= 256)
      auto const match_second_operand = [&bounds](const exprt &op) -> bool {
        if(const auto not_expr = expr_try_dynamic_cast<not_exprt>(op))
        {
          PRECONDITION(not_expr->operands().size() == 1);
          if(
            const auto ge_expr =
              expr_try_dynamic_cast<greater_than_or_equal_exprt>(
                not_expr->op()))
          {
            // If the rhs() is not constant, it has a different structure
            // (e.g. i >= j)
            if(!ge_expr->rhs().is_constant())
              return false;
            if(ge_expr->lhs() != bounds.non_const_value)
              return false;
            if(
              auto int_opt =
                numeric_cast<mp_integer>(to_constant_expr(ge_expr->rhs())))
            {
              bounds.higher = *int_opt - 1;
              return true;
            }
            return false;
          }
          return false;
        }
        return false;
      };

      // We need to match both operands, at the particular sequence we expect.
      bool structure_matched = match_first_operand(new_operands[0]) &&
                               match_second_operand(new_operands[1]);

      if(structure_matched && bounds.lower == bounds.higher)
      {
        // If we are here, we have matched the structure we expected, so we can
        // make some reasonable assumptions about where certain info we need is
        // located at.
        const auto ge_expr =
          expr_dynamic_cast<greater_than_or_equal_exprt>(new_operands[0]);
        equal_exprt new_expr{ge_expr.lhs(), ge_expr.rhs()};
        return changed(new_expr);
      }
    }

    if(may_be_reducible_to_interval)
    {
      std::optional<symbol_exprt> symbol_opt;
      std::set<mp_integer> values;
      for(const exprt &op : new_operands)
      {
        equal_exprt eq = to_equal_expr(op);
        if(eq.lhs().is_constant())
          std::swap(eq.lhs(), eq.rhs());
        if(auto s = expr_try_dynamic_cast<symbol_exprt>(eq.lhs()))
        {
          if(!symbol_opt.has_value())
            symbol_opt = *s;

          if(*s == *symbol_opt)
          {
            if(auto c = expr_try_dynamic_cast<constant_exprt>(eq.rhs()))
            {
              constant_exprt c_tmp = *c;
              if(c_tmp.type().id() == ID_c_enum_tag)
                c_tmp.type() = ns.follow_tag(to_c_enum_tag_type(c_tmp.type()));
              if(auto int_opt = numeric_cast<mp_integer>(c_tmp))
              {
                values.insert(*int_opt);
                continue;
              }
            }
          }
        }

        symbol_opt.reset();
        break;
      }

      if(symbol_opt.has_value() && values.size() >= 3)
      {
        mp_integer lower = *values.begin();
        mp_integer upper = *std::prev(values.end());
        if(upper - lower + 1 == mp_integer{values.size()})
        {
          typet type = symbol_opt->type();
          if(symbol_opt->type().id() == ID_c_enum_tag)
          {
            type = ns.follow_tag(to_c_enum_tag_type(symbol_opt->type()))
                     .underlying_type();
          }

          less_than_or_equal_exprt lb{
            from_integer(lower, type),
            typecast_exprt::conditional_cast(*symbol_opt, type)};
          less_than_or_equal_exprt ub{
            typecast_exprt::conditional_cast(*symbol_opt, type),
            from_integer(upper, type)};

          return and_exprt{lb, ub};
        }
      }
    }

    // search for a and !a
    for(const exprt &op : new_operands)
      if(
        op.id() == ID_not && op.is_boolean() &&
        expr_set.find(to_not_expr(op).op()) != expr_set.end())
      {
        return make_boolean_expr(expr.id() == ID_or);
      }

    if(new_operands.empty())
    {
      return make_boolean_expr(expr.id() == ID_and);
    }
    else if(new_operands.size() == 1)
    {
      return std::move(new_operands.front());
    }

    if(!no_change)
    {
      auto tmp = expr;
      tmp.operands() = std::move(new_operands);
      return std::move(tmp);
    }
  }

  return unchanged(expr);
}

simplify_exprt::resultt<> simplify_exprt::simplify_not(const not_exprt &expr)
{
  const exprt &op = expr.op();

  if(!expr.is_boolean() || !op.is_boolean())
  {
    return unchanged(expr);
  }

  if(op.id()==ID_not) // (not not a) == a
  {
    return to_not_expr(op).op();
  }
  else if(op.is_false())
  {
    return true_exprt();
  }
  else if(op.is_true())
  {
    return false_exprt();
  }
  else if(op.id()==ID_and ||
          op.id()==ID_or)
  {
    exprt tmp = op;

    Forall_operands(it, tmp)
    {
      *it = simplify_not(not_exprt(*it));
    }

    tmp.id(tmp.id() == ID_and ? ID_or : ID_and);

    return std::move(tmp);
  }
  else if(op.id()==ID_notequal) // !(a!=b) <-> a==b
  {
    exprt tmp = op;
    tmp.id(ID_equal);
    return std::move(tmp);
  }
  else if(op.id()==ID_exists) // !(exists: a) <-> forall: not a
  {
    auto const &op_as_exists = to_exists_expr(op);
    return forall_exprt{op_as_exists.variables(),
                        simplify_not(not_exprt(op_as_exists.where()))};
  }
  else if(op.id() == ID_forall) // !(forall: a) <-> exists: not a
  {
    auto const &op_as_forall = to_forall_expr(op);
    return exists_exprt{op_as_forall.variables(),
                        simplify_not(not_exprt(op_as_forall.where()))};
  }

  return unchanged(expr);
}
