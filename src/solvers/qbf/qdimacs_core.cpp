/*******************************************************************\

Module:

Author: CM Wintersteiger

\*******************************************************************/

#include <util/arith_tools.h>
#include <util/std_expr.h>

//#include <solvers/flattening/boolbv_width.h>

#include "qdimacs_core.h"

/*******************************************************************\

Function: qdimacs_coret::simplify_extractbits

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void qdimacs_coret::simplify_extractbits(exprt &expr) const
{
  if(expr.id()==ID_and)
  {
    typedef std::map<exprt, std::set<exprt> > used_bits_mapt;
    used_bits_mapt used_bits_map;

    forall_operands(it, expr)
    {
      if(it->id()==ID_extractbit && it->op1().is_constant())
      {
        used_bits_map[it->op0()].insert(it->op1());
      }
      else if(it->id()==ID_not &&
              it->op0().id()==ID_extractbit && it->op0().op1().is_constant())
      {
        used_bits_map[it->op0().op0()].insert(it->op0().op1());
      }
    }

    for(used_bits_mapt::const_iterator it=used_bits_map.begin();
        it!=used_bits_map.end();
        it++)
    {
      #if 0
      unsigned width;
      boolbv_get_width(it->first.type(), width);

      std::string value_string;
      value_string.resize(width, '0');

      if(it->second.size() == width) // all bits extracted from this one!
      {
        const irep_idt &ident=it->first.get(ID_identifier);
        const exprt::operandst &old_operands=expr.operands();
        exprt::operandst new_operands;

        for(exprt::operandst::const_iterator oit=old_operands.begin();
            oit!=old_operands.end();
            oit++)
        {
          if(oit->id()==ID_extractbit &&
             oit->op1().is_constant())
          {
            if(oit->op0().get(ID_identifier)==ident)
            {
              const exprt &val_expr=oit->op1();
              mp_integer value;
              to_integer(val_expr, value);
              value_string[value.to_ulong()] = '1';

              #if 0
              std::cout << "[" << value << "] = 1" << std::endl;
              #endif

              continue;
            }
          }
          else if(oit->id()==ID_not &&
                  oit->op0().id()==ID_extractbit &&
                  oit->op0().op1().is_constant())
          {
            if(oit->op0().op0().get(ID_identifier)==ident)
            {
              // just kick it; the bit in value_string is 0 anyways
              continue;
            }
          }

          new_operands.push_back(*oit);
        }

        exprt new_value(ID_constant, it->first.type());
        new_value.set(ID_value, value_string);
        new_operands.push_back(equality_exprt(it->first, new_value));

        #if 0
        std::cout << "FINAL: " << value_string << std::endl;
        #endif

        expr.operands() = new_operands;
      }
      #endif
    }
  }
}
