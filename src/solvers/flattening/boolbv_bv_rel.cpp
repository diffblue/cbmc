/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "boolbv.h"

#include <util/std_types.h>

#include "boolbv_type.h"

#include <solvers/floatbv/float_utils.h>

/// Flatten <, >, <= and >= expressions.
literalt boolbvt::convert_bv_rel(const binary_relation_exprt &expr)
{
  const irep_idt &rel=expr.id();

  const exprt &lhs = expr.lhs();
  const exprt &rhs = expr.rhs();

  const bvt &bv_lhs = convert_bv(lhs);
  const bvt &bv_rhs = convert_bv(rhs);

  bvtypet bvtype_lhs = get_bvtype(lhs.type());
  bvtypet bvtype_rhs = get_bvtype(rhs.type());

  if(
    bv_lhs.size() == bv_rhs.size() && !bv_lhs.empty() &&
    bvtype_lhs == bvtype_rhs)
  {
    if(bvtype_lhs == bvtypet::IS_FLOAT)
    {
      float_utilst float_utils(prop, to_floatbv_type(lhs.type()));

      if(rel == ID_le)
        return float_utils.relation(bv_lhs, float_utilst::relt::LE, bv_rhs);
      else if(rel == ID_lt)
        return float_utils.relation(bv_lhs, float_utilst::relt::LT, bv_rhs);
      else if(rel == ID_ge)
        return float_utils.relation(bv_lhs, float_utilst::relt::GE, bv_rhs);
      else if(rel == ID_gt)
        return float_utils.relation(bv_lhs, float_utilst::relt::GT, bv_rhs);
      else
        return SUB::convert_rest(expr);
    }
    else if(
      (lhs.type().id() == ID_range && rhs.type() == lhs.type()) ||
      bvtype_lhs == bvtypet::IS_SIGNED || bvtype_lhs == bvtypet::IS_UNSIGNED ||
      bvtype_lhs == bvtypet::IS_FIXED)
    {
      literalt literal;

      bv_utilst::representationt rep = ((bvtype_lhs == bvtypet::IS_SIGNED) ||
                                        (bvtype_lhs == bvtypet::IS_FIXED))
                                         ? bv_utilst::representationt::SIGNED
                                         : bv_utilst::representationt::UNSIGNED;

#if 1

      return bv_utils.rel(bv_lhs, expr.id(), bv_rhs, rep);

#else
      literalt literal = bv_utils.rel(bv_lhs, expr.id(), bv_rhs, rep);

      if(prop.has_set_to())
      {
        // it's unclear if this helps
        if(bv_lhs.size() > 8)
        {
          literalt equal_lit = equality(lhs, rhs);

          if(or_equal)
            prop.l_set_to_true(prop.limplies(equal_lit, literal));
          else
            prop.l_set_to_true(prop.limplies(equal_lit, !literal));
        }
      }

      return literal;
#endif
    }
    else if(
      (bvtype_lhs == bvtypet::IS_VERILOG_SIGNED ||
       bvtype_lhs == bvtypet::IS_VERILOG_UNSIGNED) &&
      lhs.type() == rhs.type())
    {
      // extract number bits
      bvt extract0, extract1;

      extract0.resize(bv_lhs.size() / 2);
      extract1.resize(bv_rhs.size() / 2);

      for(std::size_t i = 0; i < extract0.size(); i++)
        extract0[i] = bv_lhs[i * 2];

      for(std::size_t i = 0; i < extract1.size(); i++)
        extract1[i] = bv_rhs[i * 2];

      bv_utilst::representationt rep = bv_utilst::representationt::UNSIGNED;

      // now compare
      return bv_utils.rel(extract0, expr.id(), extract1, rep);
    }
  }

  return SUB::convert_rest(expr);
}
