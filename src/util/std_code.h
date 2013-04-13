/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_STD_CODE_H
#define CPROVER_STD_CODE_H

#include <cassert>

#include "expr.h"

/*! \brief A statement in a programming language
*/
class codet:public exprt
{
public:
  inline codet():exprt(ID_code, typet(ID_code))
  {
  }
  
  inline explicit codet(const irep_idt &statement):
    exprt(ID_code, typet(ID_code))
  {
    set_statement(statement);
  }
  
  inline void set_statement(const irep_idt &statement)
  {
    set(ID_statement, statement);
  }

  inline const irep_idt &get_statement() const
  {
    return get(ID_statement);
  }
  
  codet &first_statement();
  const codet &first_statement() const;
  codet &last_statement();
  const codet &last_statement() const;
  class code_blockt &make_block();
};

extern inline const codet &to_code(const exprt &expr)
{
  assert(expr.id()==ID_code);
  return static_cast<const codet &>(expr);
}

extern inline codet &to_code(exprt &expr)
{
  assert(expr.id()==ID_code);
  return static_cast<codet &>(expr);
}

/*! \brief Sequential composition
*/
class code_blockt:public codet
{
public:
  inline code_blockt():codet(ID_block)
  {
  }
  
  explicit code_blockt(const std::list<codet> &_list):codet(ID_block)
  {
    operandst &o=operands();
    o.reserve(_list.size());
    for(std::list<codet>::const_iterator
        it=_list.begin();
        it!=_list.end();
        it++)
      o.push_back(*it);        
  }
  
  inline void add(const codet &code)
  {
    copy_to_operands(code);
  }
  
  // This is the closing '}' or 'END' at the end of a block
  locationt end_location() const
  {
    return static_cast<const locationt &>(find(ID_C_end_location));
  }
};

extern inline const code_blockt &to_code_block(const codet &code)
{
  assert(code.get_statement()==ID_block);
  return static_cast<const code_blockt &>(code);
}

extern inline code_blockt &to_code_block(codet &code)
{
  assert(code.get_statement()==ID_block);
  return static_cast<code_blockt &>(code);
}

/*! \brief Skip
*/
class code_skipt:public codet
{
public:
  code_skipt():codet(ID_skip)
  {
  }
};

/*! \brief Assignment
*/
class code_assignt:public codet
{
public:
  inline code_assignt():codet(ID_assign)
  {
    operands().resize(2);
  }
  
  inline code_assignt(const exprt &lhs, const exprt &rhs):codet(ID_assign)
  {
    copy_to_operands(lhs, rhs);
  }
  
  inline exprt &lhs()
  {
    return op0();
  }

  inline exprt &rhs()
  {
    return op1();
  }

  inline const exprt &lhs() const
  {
    return op0();
  }

  inline const exprt &rhs() const
  {
    return op1();
  }
};

extern inline const code_assignt &to_code_assign(const codet &code)
{
  assert(code.get_statement()==ID_assign && code.operands().size()==2);
  return static_cast<const code_assignt &>(code);
}

extern inline code_assignt &to_code_assign(codet &code)
{
  assert(code.get_statement()==ID_assign && code.operands().size()==2);
  return static_cast<code_assignt &>(code);
}

/*! \brief A declaration of a local variable
*/
class code_declt:public codet
{
public:
  inline code_declt():codet(ID_decl)
  {
    operands().resize(1);
  }
  
  inline explicit code_declt(const exprt &symbol):codet(ID_decl)
  {
    copy_to_operands(symbol);
  }
  
  inline exprt &symbol()
  {
    return op0();
  }

  inline const exprt &symbol() const
  {
    return op0();
  }

  #if 0  
  inline exprt &initializer()
  {
    return op1();
  }

  inline const exprt &initializer() const
  {
    return op1();
  }
  #endif
  
  const irep_idt &get_identifier() const;

  friend inline const code_declt &to_code_decl(const codet &code)
  {
    // will be size()==1 in the future
    assert(code.get_statement()==ID_decl && code.operands().size()>=1);
    return static_cast<const code_declt &>(code);
  }

  friend inline code_declt &to_code_decl(codet &code)
  {
    // will be size()==1 in the future
    assert(code.get_statement()==ID_decl && code.operands().size()>=1);
    return static_cast<code_declt &>(code);
  }

};

const code_declt &to_code_decl(const codet &code);
code_declt &to_code_decl(codet &code);

/*! \brief A removal of a local variable
*/
class code_deadt:public codet
{
public:
  inline code_deadt():codet(ID_dead)
  {
    operands().resize(1);
  }
  
  inline explicit code_deadt(const exprt &symbol):codet(ID_dead)
  {
    copy_to_operands(symbol);
  }
  
  inline exprt &symbol()
  {
    return op0();
  }

  inline const exprt &symbol() const
  {
    return op0();
  }

  const irep_idt &get_identifier() const;

  friend inline const code_deadt &to_code_dead(const codet &code)
  {
    assert(code.get_statement()==ID_dead && code.operands().size()==1);
    return static_cast<const code_deadt &>(code);
  }

  friend inline code_deadt &to_code_dead(codet &code)
  {
    assert(code.get_statement()==ID_dead && code.operands().size()==1);
    return static_cast<code_deadt &>(code);
  }

};

const code_deadt &to_code_dead(const codet &code);
code_deadt &to_code_dead(codet &code);

/*! \brief An assumption
*/
class code_assumet:public codet
{
public:
  inline code_assumet():codet(ID_assume)
  {
    // will change to resize(1) in the future
    operands().reserve(1);
  }

  inline explicit code_assumet(const exprt &expr):codet(ID_assume)
  {
    copy_to_operands(expr);
  }

  inline const exprt &assumption() const
  {
    return op0();
  }

  inline exprt &assumption()
  {
    return op0();
  }
};

extern inline const code_assumet &to_code_assume(const codet &code)
{
  assert(code.get_statement()==ID_assume);
  return static_cast<const code_assumet &>(code);
}

extern inline code_assumet &to_code_assume(codet &code)
{
  assert(code.get_statement()==ID_assume);
  return static_cast<code_assumet &>(code);
}

/*! \brief An assertion
*/
class code_assertt:public codet
{
public:
  inline code_assertt():codet(ID_assert)
  {
    // will change to resize(1) in the future
    operands().reserve(1);
  }
  
  inline explicit code_assertt(const exprt &expr):codet(ID_assert)
  {
    copy_to_operands(expr);
  }

  inline const exprt &assertion() const
  {
    return op0();
  }

  inline exprt &assertion()
  {
    return op0();
  }
};

extern inline const code_assertt &to_code_assert(const codet &code)
{
  assert(code.get_statement()==ID_assert);
  return static_cast<const code_assertt &>(code);
}

extern inline code_assertt &to_code_assert(codet &code)
{
  assert(code.get_statement()==ID_assert);
  return static_cast<code_assertt &>(code);
}

/*! \brief An if-then-else
*/
class code_ifthenelset:public codet
{
public:
  inline code_ifthenelset():codet(ID_ifthenelse)
  {
    operands().resize(3);
    op1().make_nil();
    op2().make_nil();
  }
  
  inline const exprt &cond() const
  {
    return op0();
  }
  
  inline exprt &cond()
  {
    return op0();
  }
  
  inline const exprt &then_case() const
  {
    return op1();
  }

  inline const exprt &else_case() const
  {
    return op2();
  }

  inline exprt &then_case()
  {
    return op1();
  }

  inline exprt &else_case()
  {
    return op2();
  }
};

extern inline const code_ifthenelset &to_code_ifthenelse(const codet &code)
{
  assert(code.get_statement()==ID_ifthenelse &&
         code.operands().size()==3);
  return static_cast<const code_ifthenelset &>(code);
}

extern inline code_ifthenelset &to_code_ifthenelse(codet &code)
{
  assert(code.get_statement()==ID_ifthenelse &&
         code.operands().size()==3);
  return static_cast<code_ifthenelset &>(code);
}

/*! \brief A `switch' instruction
*/
class code_switcht:public codet
{
public:
  inline code_switcht():codet(ID_switch)
  {
    operands().resize(2);
  }
  
  inline const exprt &value() const
  {
    return op0();
  }
  
  inline exprt &value()
  {
    return op0();
  }
  
  inline const codet &body() const
  {
    return to_code(op1());
  }

  inline codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

extern inline const code_switcht &to_code_switch(const codet &code)
{
  assert(code.get_statement()==ID_switch &&
         code.operands().size()==2);
  return static_cast<const code_switcht &>(code);
}

extern inline code_switcht &to_code_switch(codet &code)
{
  assert(code.get_statement()==ID_switch &&
         code.operands().size()==2);
  return static_cast<code_switcht &>(code);
}


/*! \brief A `while' instruction
*/
class code_whilet:public codet
{
public:
  inline code_whilet():codet(ID_while)
  {
    operands().resize(2);
  }
  
  inline const exprt &cond() const
  {
    return op0();
  }
  
  inline exprt &cond()
  {
    return op0();
  }
  
  inline const codet &body() const
  {
    return to_code(op1());
  }

  inline codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

extern inline const code_whilet &to_code_while(const codet &code)
{
  assert(code.get_statement()==ID_while &&
         code.operands().size()==2);
  return static_cast<const code_whilet &>(code);
}

extern inline code_whilet &to_code_while(codet &code)
{
  assert(code.get_statement()==ID_while &&
         code.operands().size()==2);
  return static_cast<code_whilet &>(code);
}

/*! \brief A `do while' instruction
*/
class code_dowhilet:public codet
{
public:
  inline code_dowhilet():codet(ID_dowhile)
  {
    operands().resize(2);
  }
  
  inline const exprt &cond() const
  {
    return op0();
  }
  
  inline exprt &cond()
  {
    return op0();
  }
  
  inline const codet &body() const
  {
    return to_code(op1());
  }

  inline codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

extern inline const code_dowhilet &to_code_dowhile(const codet &code)
{
  assert(code.get_statement()==ID_dowhile &&
         code.operands().size()==2);
  return static_cast<const code_dowhilet &>(code);
}

extern inline code_dowhilet &to_code_dowhile(codet &code)
{
  assert(code.get_statement()==ID_dowhile &&
         code.operands().size()==2);
  return static_cast<code_dowhilet &>(code);
}

/*! \brief A `for' instruction
*/
class code_fort:public codet
{
public:
  inline code_fort():codet(ID_for)
  {
    operands().resize(4);
  }

  // nil or a statement  
  inline const exprt &init() const
  {
    return op0();
  }

  inline exprt &init()
  {
    return op0();
  }

  inline const exprt &cond() const
  {
    return op1();
  }
  
  inline exprt &cond()
  {
    return op1();
  }
  
  inline const exprt &iter() const
  {
    return op2();
  }
  
  inline exprt &iter()
  {
    return op2();
  }
  
  inline const codet &body() const
  {
    return to_code(op3());
  }

  inline codet &body()
  {
    return static_cast<codet &>(op3());
  }
};

extern inline const code_fort &to_code_for(const codet &code)
{
  assert(code.get_statement()==ID_for &&
         code.operands().size()==4);
  return static_cast<const code_fort &>(code);
}

extern inline code_fort &to_code_for(codet &code)
{
  assert(code.get_statement()==ID_for &&
         code.operands().size()==4);
  return static_cast<code_fort &>(code);
}

/*! \brief A function call
    
    The function call instruction has three operands.
    The first is the expression that is used to store
    the return value. The second is the function called.
    The third is a vector of argument values.
*/
class code_function_callt:public codet
{
public:
  inline code_function_callt():codet(ID_function_call)
  {
    operands().resize(3);
    lhs().make_nil();
    op2().id(ID_arguments);
  }
  
  inline exprt &lhs()
  {
    return op0();
  }

  inline const exprt &lhs() const
  {
    return op0();
  }

  inline exprt &function()
  {
    return op1();
  }

  inline const exprt &function() const
  {
    return op1();
  }

  typedef exprt::operandst argumentst;

  inline argumentst &arguments()
  {
    return op2().operands();
  }

  inline const argumentst &arguments() const
  {
    return op2().operands();
  }
};

extern inline const code_function_callt &to_code_function_call(const codet &code)
{
  assert(code.get_statement()==ID_function_call);
  return static_cast<const code_function_callt &>(code);
}

extern inline code_function_callt &to_code_function_call(codet &code)
{
  assert(code.get_statement()==ID_function_call);
  return static_cast<code_function_callt &>(code);
}

/*! \brief Return from a function
*/
class code_returnt:public codet
{
public:
  inline code_returnt():codet(ID_return)
  {
    operands().reserve(1);
  }
  
  explicit inline code_returnt(const exprt &_op):codet(ID_return)
  {
    copy_to_operands(_op);
  }
  
  inline const exprt &return_value() const
  {
    return op0();
  }
  
  inline exprt &return_value()
  {
    operands().resize(1);
    return op0();
  }
  
  inline bool has_return_value() const
  {
    return operands().size()==1;
  }
};

extern inline const code_returnt &to_code_return(const codet &code)
{
  assert(code.get_statement()==ID_return);
  return static_cast<const code_returnt &>(code);
}

extern inline code_returnt &to_code_return(codet &code)
{
  assert(code.get_statement()==ID_return);
  return static_cast<code_returnt &>(code);
}

/*! \brief A label for branch targets
*/
class code_labelt:public codet
{
public:
  inline code_labelt():codet(ID_label)
  {
    operands().resize(1);
  }

  inline bool is_default() const
  {
    return get_bool(ID_default);
  }

  inline const exprt::operandst &case_op() const
  {
    return static_cast<const exprt &>(find(ID_case)).operands();
  }
  
  inline const irep_idt &get_label() const
  {
    return get(ID_label);
  }

  inline void set_label(const irep_idt &label)
  {
    set(ID_label, label);
  }
  
  codet &code()
  {
    return static_cast<codet &>(op0());
  }

  const codet &code() const
  {
    return static_cast<const codet &>(op0());
  }
};

extern inline const code_labelt &to_code_label(const codet &code)
{
  assert(code.get_statement()==ID_label);
  return static_cast<const code_labelt &>(code);
}

extern inline code_labelt &to_code_label(codet &code)
{
  assert(code.get_statement()==ID_label);
  return static_cast<code_labelt &>(code);
}

/*! \brief A break for `for' and `while' loops
*/
class code_breakt:public codet
{
public:
  inline code_breakt():codet(ID_break)
  {
  }
};

extern inline const code_breakt &to_code_break(const codet &code)
{
  assert(code.get_statement()==ID_break);
  return static_cast<const code_breakt &>(code);
}

extern inline code_breakt &to_code_break(codet &code)
{
  assert(code.get_statement()==ID_break);
  return static_cast<code_breakt &>(code);
}

/*! \brief A continue for `for' and `while' loops
*/
class code_continuet:public codet
{
public:
  inline code_continuet():codet(ID_continue)
  {
  }
};

extern inline const code_continuet &to_code_continue(const codet &code)
{
  assert(code.get_statement()==ID_continue);
  return static_cast<const code_continuet &>(code);
}

extern inline code_continuet &to_code_continue(codet &code)
{
  assert(code.get_statement()==ID_continue);
  return static_cast<code_continuet &>(code);
}

/*! \brief An expression statement
*/
class code_expressiont:public codet
{
public:
  inline code_expressiont():codet(ID_expression)
  {
    operands().resize(1);
  }
  
  inline explicit code_expressiont(const exprt &expr):codet(ID_expression)
  {
    operands().push_back(expr);
  }
  
  inline friend code_expressiont &to_code_expression(codet &code)
  {
    assert(code.get_statement()==ID_expression &&
           code.operands().size()==1);
    return static_cast<code_expressiont &>(code);
  }

  inline friend const code_expressiont &to_code_expression(const codet &code)
  {
    assert(code.get_statement()==ID_expression &&
           code.operands().size()==1);
    return static_cast<const code_expressiont &>(code);
  }
  
  inline const exprt &expression() const
  {
    return op0();
  }

  inline exprt &expression()
  {
    return op0();
  }
};

code_expressiont &to_code_expression(codet &code);
const code_expressiont &to_code_expression(const codet &code);

/*! \brief An expression containing a side effect
    \remark The ID will eventually change to ID_side_effect
*/
class side_effect_exprt:public exprt
{
public:
  inline explicit side_effect_exprt(const irep_idt &statement):exprt(ID_sideeffect)
  {
    set_statement(statement);
  }

  inline side_effect_exprt(const irep_idt &statement, const typet &_type):
    exprt(ID_sideeffect, _type)
  {
    set_statement(statement);
  }

  inline friend side_effect_exprt &to_side_effect_expr(exprt &expr)
  {
    assert(expr.id()==ID_sideeffect);
    return static_cast<side_effect_exprt &>(expr);
  }

  inline friend const side_effect_exprt &to_side_effect_expr(const exprt &expr)
  {
    assert(expr.id()==ID_sideeffect);
    return static_cast<const side_effect_exprt &>(expr);
  }
  
  inline const irep_idt &get_statement() const
  {
    return get(ID_statement);
  }

  inline void set_statement(const irep_idt &statement)
  {
    return set(ID_statement, statement);
  }
};

side_effect_exprt &to_side_effect_expr(exprt &expr);
const side_effect_exprt &to_side_effect_expr(const exprt &expr);

/*! \brief A side effect that returns a non-deterministically chosen value
*/
class side_effect_expr_nondett:public side_effect_exprt
{
public:
  inline side_effect_expr_nondett():side_effect_exprt(ID_nondet)
  {
  }

  inline explicit side_effect_expr_nondett(const typet &_type):
    side_effect_exprt(ID_nondet, _type)
  {
  }
};

/*! \brief A function call side effect
*/
class side_effect_expr_function_callt:public side_effect_exprt
{
public:
  inline side_effect_expr_function_callt():side_effect_exprt(ID_function_call)
  {
    operands().resize(2);
    op1().id(ID_arguments);
  }

  inline exprt &function()
  {
    return op0();
  }

  inline const exprt &function() const
  {
    return op0();
  }

  inline exprt::operandst &arguments()
  {
    return op1().operands();
  }

  inline const exprt::operandst &arguments() const
  {
    return op1().operands();
  }

  inline friend side_effect_expr_function_callt &to_side_effect_expr_function_call(exprt &expr)
  {
    assert(expr.id()==ID_sideeffect);
    assert(expr.get(ID_statement)==ID_function_call);
    return static_cast<side_effect_expr_function_callt &>(expr);
  }

  inline friend const side_effect_expr_function_callt &to_side_effect_expr_function_call(const exprt &expr)
  {
    assert(expr.id()==ID_sideeffect);
    assert(expr.get(ID_statement)==ID_function_call);
    return static_cast<const side_effect_expr_function_callt &>(expr);
  }
};

side_effect_expr_function_callt &to_side_effect_expr_function_call(exprt &expr);
const side_effect_expr_function_callt &to_side_effect_expr_function_call(const exprt &expr);

#endif
