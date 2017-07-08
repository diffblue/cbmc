/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_STD_CODE_H
#define CPROVER_UTIL_STD_CODE_H

#include <cassert>

#include "expr.h"

/*! \brief A statement in a programming language
*/
class codet:public exprt
{
public:
  codet():exprt(ID_code, typet(ID_code))
  {
  }

  explicit codet(const irep_idt &statement):
    exprt(ID_code, typet(ID_code))
  {
    set_statement(statement);
  }

  void set_statement(const irep_idt &statement)
  {
    set(ID_statement, statement);
  }

  const irep_idt &get_statement() const
  {
    return get(ID_statement);
  }

  codet &first_statement();
  const codet &first_statement() const;
  codet &last_statement();
  const codet &last_statement() const;
  class code_blockt &make_block();
};

inline const codet &to_code(const exprt &expr)
{
  assert(expr.id()==ID_code);
  return static_cast<const codet &>(expr);
}

inline codet &to_code(exprt &expr)
{
  assert(expr.id()==ID_code);
  return static_cast<codet &>(expr);
}

/*! \brief Sequential composition
*/
class code_blockt:public codet
{
public:
  code_blockt():codet(ID_block)
  {
  }

  explicit code_blockt(const std::list<codet> &_list):codet(ID_block)
  {
    operandst &o=operands();
    reserve_operands(_list.size());
    for(std::list<codet>::const_iterator
        it=_list.begin();
        it!=_list.end();
        it++)
      o.push_back(*it);
  }

  void add(const codet &code)
  {
    copy_to_operands(code);
  }

  void append(const code_blockt &extra_block);

  // This is the closing '}' or 'END' at the end of a block
  source_locationt end_location() const
  {
    return static_cast<const source_locationt &>(find(ID_C_end_location));
  }

  codet &find_last_statement()
  {
    codet *last=this;

    while(true)
    {
      const irep_idt &statement=last->get_statement();

      if(statement==ID_block &&
         !last->operands().empty())
      {
        last=&to_code(last->operands().back());
      }
      else if(statement==ID_label)
      {
        assert(last->operands().size()==1);
        last=&(to_code(last->op0()));
      }
      else
        break;
    }

    return *last;
  }
};

inline const code_blockt &to_code_block(const codet &code)
{
  assert(code.get_statement()==ID_block);
  return static_cast<const code_blockt &>(code);
}

inline code_blockt &to_code_block(codet &code)
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
  code_assignt():codet(ID_assign)
  {
    operands().resize(2);
  }

  code_assignt(const exprt &lhs, const exprt &rhs):codet(ID_assign)
  {
    copy_to_operands(lhs, rhs);
  }

  exprt &lhs()
  {
    return op0();
  }

  exprt &rhs()
  {
    return op1();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  const exprt &rhs() const
  {
    return op1();
  }
};

inline const code_assignt &to_code_assign(const codet &code)
{
  assert(code.get_statement()==ID_assign && code.operands().size()==2);
  return static_cast<const code_assignt &>(code);
}

inline code_assignt &to_code_assign(codet &code)
{
  assert(code.get_statement()==ID_assign && code.operands().size()==2);
  return static_cast<code_assignt &>(code);
}

/*! \brief A declaration of a local variable
*/
class code_declt:public codet
{
public:
  code_declt():codet(ID_decl)
  {
    operands().resize(1);
  }

  explicit code_declt(const exprt &symbol):codet(ID_decl)
  {
    copy_to_operands(symbol);
  }

  exprt &symbol()
  {
    return op0();
  }

  const exprt &symbol() const
  {
    return op0();
  }

  const irep_idt &get_identifier() const;
};

inline const code_declt &to_code_decl(const codet &code)
{
  // will be size()==1 in the future
  assert(code.get_statement()==ID_decl && code.operands().size()>=1);
  return static_cast<const code_declt &>(code);
}

inline code_declt &to_code_decl(codet &code)
{
  // will be size()==1 in the future
  assert(code.get_statement()==ID_decl && code.operands().size()>=1);
  return static_cast<code_declt &>(code);
}

/*! \brief A removal of a local variable
*/
class code_deadt:public codet
{
public:
  code_deadt():codet(ID_dead)
  {
    operands().resize(1);
  }

  explicit code_deadt(const exprt &symbol):codet(ID_dead)
  {
    copy_to_operands(symbol);
  }

  exprt &symbol()
  {
    return op0();
  }

  const exprt &symbol() const
  {
    return op0();
  }

  const irep_idt &get_identifier() const;
};

inline const code_deadt &to_code_dead(const codet &code)
{
  assert(code.get_statement()==ID_dead && code.operands().size()==1);
  return static_cast<const code_deadt &>(code);
}

inline code_deadt &to_code_dead(codet &code)
{
  assert(code.get_statement()==ID_dead && code.operands().size()==1);
  return static_cast<code_deadt &>(code);
}

/*! \brief An assumption
*/
class code_assumet:public codet
{
public:
  code_assumet():codet(ID_assume)
  {
    operands().resize(1);
  }

  explicit code_assumet(const exprt &expr):codet(ID_assume)
  {
    copy_to_operands(expr);
  }

  const exprt &assumption() const
  {
    return op0();
  }

  exprt &assumption()
  {
    return op0();
  }
};

inline const code_assumet &to_code_assume(const codet &code)
{
  assert(code.get_statement()==ID_assume);
  return static_cast<const code_assumet &>(code);
}

inline code_assumet &to_code_assume(codet &code)
{
  assert(code.get_statement()==ID_assume);
  return static_cast<code_assumet &>(code);
}

/*! \brief An assertion
*/
class code_assertt:public codet
{
public:
  code_assertt():codet(ID_assert)
  {
    operands().resize(1);
  }

  explicit code_assertt(const exprt &expr):codet(ID_assert)
  {
    copy_to_operands(expr);
  }

  const exprt &assertion() const
  {
    return op0();
  }

  exprt &assertion()
  {
    return op0();
  }
};

inline const code_assertt &to_code_assert(const codet &code)
{
  assert(code.get_statement()==ID_assert);
  return static_cast<const code_assertt &>(code);
}

inline code_assertt &to_code_assert(codet &code)
{
  assert(code.get_statement()==ID_assert);
  return static_cast<code_assertt &>(code);
}

/*! \brief An if-then-else
*/
class code_ifthenelset:public codet
{
public:
  code_ifthenelset():codet(ID_ifthenelse)
  {
    operands().resize(3);
    op1().make_nil();
    op2().make_nil();
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const codet &then_case() const
  {
    return static_cast<const codet &>(op1());
  }

  bool has_else_case() const
  {
    return op2().is_not_nil();
  }

  const codet &else_case() const
  {
    return static_cast<const codet &>(op2());
  }

  codet &then_case()
  {
    return static_cast<codet &>(op1());
  }

  codet &else_case()
  {
    return static_cast<codet &>(op2());
  }
};

inline const code_ifthenelset &to_code_ifthenelse(const codet &code)
{
  assert(code.get_statement()==ID_ifthenelse &&
         code.operands().size()==3);
  return static_cast<const code_ifthenelset &>(code);
}

inline code_ifthenelset &to_code_ifthenelse(codet &code)
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
  code_switcht():codet(ID_switch)
  {
    operands().resize(2);
  }

  const exprt &value() const
  {
    return op0();
  }

  exprt &value()
  {
    return op0();
  }

  const codet &body() const
  {
    return to_code(op1());
  }

  codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

inline const code_switcht &to_code_switch(const codet &code)
{
  assert(code.get_statement()==ID_switch &&
         code.operands().size()==2);
  return static_cast<const code_switcht &>(code);
}

inline code_switcht &to_code_switch(codet &code)
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
  code_whilet():codet(ID_while)
  {
    operands().resize(2);
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const codet &body() const
  {
    return to_code(op1());
  }

  codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

inline const code_whilet &to_code_while(const codet &code)
{
  assert(code.get_statement()==ID_while &&
         code.operands().size()==2);
  return static_cast<const code_whilet &>(code);
}

inline code_whilet &to_code_while(codet &code)
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
  code_dowhilet():codet(ID_dowhile)
  {
    operands().resize(2);
  }

  const exprt &cond() const
  {
    return op0();
  }

  exprt &cond()
  {
    return op0();
  }

  const codet &body() const
  {
    return to_code(op1());
  }

  codet &body()
  {
    return static_cast<codet &>(op1());
  }
};

inline const code_dowhilet &to_code_dowhile(const codet &code)
{
  assert(code.get_statement()==ID_dowhile &&
         code.operands().size()==2);
  return static_cast<const code_dowhilet &>(code);
}

inline code_dowhilet &to_code_dowhile(codet &code)
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
  code_fort():codet(ID_for)
  {
    operands().resize(4);
  }

  // nil or a statement
  const exprt &init() const
  {
    return op0();
  }

  exprt &init()
  {
    return op0();
  }

  const exprt &cond() const
  {
    return op1();
  }

  exprt &cond()
  {
    return op1();
  }

  const exprt &iter() const
  {
    return op2();
  }

  exprt &iter()
  {
    return op2();
  }

  const codet &body() const
  {
    return to_code(op3());
  }

  codet &body()
  {
    return static_cast<codet &>(op3());
  }
};

inline const code_fort &to_code_for(const codet &code)
{
  assert(code.get_statement()==ID_for &&
         code.operands().size()==4);
  return static_cast<const code_fort &>(code);
}

inline code_fort &to_code_for(codet &code)
{
  assert(code.get_statement()==ID_for &&
         code.operands().size()==4);
  return static_cast<code_fort &>(code);
}

/*! \brief A `goto' instruction
*/
class code_gotot:public codet
{
public:
  code_gotot():codet(ID_goto)
  {
  }

  explicit code_gotot(const irep_idt &label):codet(ID_goto)
  {
    set_destination(label);
  }

  void set_destination(const irep_idt &label)
  {
    set(ID_destination, label);
  }

  const irep_idt &get_destination() const
  {
    return get(ID_destination);
  }
};

inline const code_gotot &to_code_goto(const codet &code)
{
  assert(code.get_statement()==ID_goto &&
         code.operands().empty());
  return static_cast<const code_gotot &>(code);
}

inline code_gotot &to_code_goto(codet &code)
{
  assert(code.get_statement()==ID_goto &&
         code.operands().empty());
  return static_cast<code_gotot &>(code);
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
  code_function_callt():codet(ID_function_call)
  {
    operands().resize(3);
    lhs().make_nil();
    op2().id(ID_arguments);
  }

  exprt &lhs()
  {
    return op0();
  }

  const exprt &lhs() const
  {
    return op0();
  }

  exprt &function()
  {
    return op1();
  }

  const exprt &function() const
  {
    return op1();
  }

  typedef exprt::operandst argumentst;

  argumentst &arguments()
  {
    return op2().operands();
  }

  const argumentst &arguments() const
  {
    return op2().operands();
  }
};

inline const code_function_callt &to_code_function_call(const codet &code)
{
  assert(code.get_statement()==ID_function_call);
  return static_cast<const code_function_callt &>(code);
}

inline code_function_callt &to_code_function_call(codet &code)
{
  assert(code.get_statement()==ID_function_call);
  return static_cast<code_function_callt &>(code);
}

/*! \brief Return from a function
*/
class code_returnt:public codet
{
public:
  code_returnt():codet(ID_return)
  {
    operands().resize(1);
    op0().make_nil();
  }

  explicit code_returnt(const exprt &_op):codet(ID_return)
  {
    copy_to_operands(_op);
  }

  const exprt &return_value() const
  {
    return op0();
  }

  exprt &return_value()
  {
    return op0();
  }

  bool has_return_value() const
  {
    if(operands().empty())
      return false; // backwards compatibility
    return return_value().is_not_nil();
  }
};

inline const code_returnt &to_code_return(const codet &code)
{
  assert(code.get_statement()==ID_return);
  return static_cast<const code_returnt &>(code);
}

inline code_returnt &to_code_return(codet &code)
{
  assert(code.get_statement()==ID_return);
  return static_cast<code_returnt &>(code);
}

/*! \brief A label for branch targets
*/
class code_labelt:public codet
{
public:
  code_labelt():codet(ID_label)
  {
    operands().resize(1);
  }

  explicit code_labelt(const irep_idt &_label):codet(ID_label)
  {
    operands().resize(1);
    set_label(_label);
  }

  code_labelt(
    const irep_idt &_label, const codet &_code):codet(ID_label)
  {
    operands().resize(1);
    set_label(_label);
    code()=_code;
  }

  const irep_idt &get_label() const
  {
    return get(ID_label);
  }

  void set_label(const irep_idt &label)
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

inline const code_labelt &to_code_label(const codet &code)
{
  assert(code.get_statement()==ID_label && code.operands().size()==1);
  return static_cast<const code_labelt &>(code);
}

inline code_labelt &to_code_label(codet &code)
{
  assert(code.get_statement()==ID_label && code.operands().size()==1);
  return static_cast<code_labelt &>(code);
}

/*! \brief A switch-case
*/
class code_switch_caset:public codet
{
public:
  code_switch_caset():codet(ID_switch_case)
  {
    operands().resize(2);
  }

  code_switch_caset(
    const exprt &_case_op, const codet &_code):codet(ID_switch_case)
  {
    copy_to_operands(_case_op, _code);
  }

  bool is_default() const
  {
    return get_bool(ID_default);
  }

  void set_default()
  {
    return set(ID_default, true);
  }

  const exprt &case_op() const
  {
    return op0();
  }

  exprt &case_op()
  {
    return op0();
  }

  codet &code()
  {
    return static_cast<codet &>(op1());
  }

  const codet &code() const
  {
    return static_cast<const codet &>(op1());
  }
};

inline const code_switch_caset &to_code_switch_case(const codet &code)
{
  assert(code.get_statement()==ID_switch_case && code.operands().size()==2);
  return static_cast<const code_switch_caset &>(code);
}

inline code_switch_caset &to_code_switch_case(codet &code)
{
  assert(code.get_statement()==ID_switch_case && code.operands().size()==2);
  return static_cast<code_switch_caset &>(code);
}

/*! \brief A break for `for' and `while' loops
*/
class code_breakt:public codet
{
public:
  code_breakt():codet(ID_break)
  {
  }
};

inline const code_breakt &to_code_break(const codet &code)
{
  assert(code.get_statement()==ID_break);
  return static_cast<const code_breakt &>(code);
}

inline code_breakt &to_code_break(codet &code)
{
  assert(code.get_statement()==ID_break);
  return static_cast<code_breakt &>(code);
}

/*! \brief A continue for `for' and `while' loops
*/
class code_continuet:public codet
{
public:
  code_continuet():codet(ID_continue)
  {
  }
};

inline const code_continuet &to_code_continue(const codet &code)
{
  assert(code.get_statement()==ID_continue);
  return static_cast<const code_continuet &>(code);
}

inline code_continuet &to_code_continue(codet &code)
{
  assert(code.get_statement()==ID_continue);
  return static_cast<code_continuet &>(code);
}

/*! \brief An inline assembler statement
*/
class code_asmt:public codet
{
public:
  code_asmt():codet(ID_asm)
  {
  }

  explicit code_asmt(const exprt &expr):codet(ID_asm)
  {
    copy_to_operands(expr);
  }

  const irep_idt &get_flavor() const
  {
    return get(ID_flavor);
  }

  void set_flavor(const irep_idt &f)
  {
    set(ID_flavor, f);
  }
};

inline code_asmt &to_code_asm(codet &code)
{
  assert(code.get_statement()==ID_asm);
  return static_cast<code_asmt &>(code);
}

inline const code_asmt &to_code_asm(const codet &code)
{
  assert(code.get_statement()==ID_asm);
  return static_cast<const code_asmt &>(code);
}

/*! \brief An expression statement
*/
class code_expressiont:public codet
{
public:
  code_expressiont():codet(ID_expression)
  {
    operands().resize(1);
  }

  explicit code_expressiont(const exprt &expr):codet(ID_expression)
  {
    copy_to_operands(expr);
  }

  const exprt &expression() const
  {
    return op0();
  }

  exprt &expression()
  {
    return op0();
  }
};

inline code_expressiont &to_code_expression(codet &code)
{
  assert(code.get_statement()==ID_expression &&
         code.operands().size()==1);
  return static_cast<code_expressiont &>(code);
}

inline const code_expressiont &to_code_expression(const codet &code)
{
  assert(code.get_statement()==ID_expression &&
         code.operands().size()==1);
  return static_cast<const code_expressiont &>(code);
}

/*! \brief An expression containing a side effect
*/
class side_effect_exprt:public exprt
{
public:
  explicit side_effect_exprt(const irep_idt &statement):
    exprt(ID_side_effect)
  {
    set_statement(statement);
  }

  side_effect_exprt(const irep_idt &statement, const typet &_type):
    exprt(ID_side_effect, _type)
  {
    set_statement(statement);
  }

  const irep_idt &get_statement() const
  {
    return get(ID_statement);
  }

  void set_statement(const irep_idt &statement)
  {
    return set(ID_statement, statement);
  }
};

inline side_effect_exprt &to_side_effect_expr(exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  return static_cast<side_effect_exprt &>(expr);
}

inline const side_effect_exprt &to_side_effect_expr(const exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  return static_cast<const side_effect_exprt &>(expr);
}

/*! \brief A side effect that returns a non-deterministically chosen value
*/
class side_effect_expr_nondett:public side_effect_exprt
{
public:
  side_effect_expr_nondett():side_effect_exprt(ID_nondet)
  {
    set_nullable(true);
  }

  explicit side_effect_expr_nondett(const typet &_type):
    side_effect_exprt(ID_nondet, _type)
  {
    set_nullable(true);
  }

  void set_nullable(bool nullable)
  {
    set(ID_is_nondet_nullable, nullable);
  }

  bool get_nullable() const
  {
    return get_bool(ID_is_nondet_nullable);
  }
};

inline side_effect_expr_nondett &to_side_effect_expr_nondet(exprt &expr)
{
  auto &side_effect_expr_nondet=to_side_effect_expr(expr);
  assert(side_effect_expr_nondet.get_statement()==ID_nondet);
  return static_cast<side_effect_expr_nondett &>(side_effect_expr_nondet);
}

inline const side_effect_expr_nondett &to_side_effect_expr_nondet(
  const exprt &expr)
{
  const auto &side_effect_expr_nondet=to_side_effect_expr(expr);
  assert(side_effect_expr_nondet.get_statement()==ID_nondet);
  return static_cast<const side_effect_expr_nondett &>(side_effect_expr_nondet);
}

/*! \brief A function call side effect
*/
class side_effect_expr_function_callt:public side_effect_exprt
{
public:
  side_effect_expr_function_callt():side_effect_exprt(ID_function_call)
  {
    operands().resize(2);
    op1().id(ID_arguments);
  }

  exprt &function()
  {
    return op0();
  }

  const exprt &function() const
  {
    return op0();
  }

  exprt::operandst &arguments()
  {
    return op1().operands();
  }

  const exprt::operandst &arguments() const
  {
    return op1().operands();
  }
};

inline side_effect_expr_function_callt
  &to_side_effect_expr_function_call(exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  assert(expr.get(ID_statement)==ID_function_call);
  return static_cast<side_effect_expr_function_callt &>(expr);
}

inline const side_effect_expr_function_callt
  &to_side_effect_expr_function_call(const exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  assert(expr.get(ID_statement)==ID_function_call);
  return static_cast<const side_effect_expr_function_callt &>(expr);
}

/*! \brief A side effect that throws an exception
*/
class side_effect_expr_throwt:public side_effect_exprt
{
public:
  side_effect_expr_throwt():side_effect_exprt(ID_throw)
  {
  }

  explicit side_effect_expr_throwt(const irept &exception_list):
    side_effect_exprt(ID_throw)
  {
    set(ID_exception_list, exception_list);
  }
};

inline side_effect_expr_throwt &to_side_effect_expr_throw(exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  assert(expr.get(ID_statement)==ID_throw);
  return static_cast<side_effect_expr_throwt &>(expr);
}

inline const side_effect_expr_throwt &to_side_effect_expr_throw(
  const exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  assert(expr.get(ID_statement)==ID_throw);
  return static_cast<const side_effect_expr_throwt &>(expr);
}
/*! \brief A side effect that pushes/pops a catch handler
*/
class side_effect_expr_catcht:public side_effect_exprt
{
public:
  side_effect_expr_catcht():side_effect_exprt(ID_push_catch)
  {
  }
  explicit side_effect_expr_catcht(const irept &exception_list):
    side_effect_exprt(ID_push_catch)
  {
    set(ID_exception_list, exception_list);
  }
};

static inline side_effect_expr_catcht &to_side_effect_expr_catch(exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  assert(expr.get(ID_statement)==ID_push_catch);
  return static_cast<side_effect_expr_catcht &>(expr);
}

static inline const side_effect_expr_catcht &to_side_effect_expr_catch(
  const exprt &expr)
{
  assert(expr.id()==ID_side_effect);
  assert(expr.get(ID_statement)==ID_push_catch);
  return static_cast<const side_effect_expr_catcht &>(expr);
}

/*! \brief A try/catch block
*/
class code_try_catcht:public codet
{
public:
  code_try_catcht():codet(ID_try_catch)
  {
    operands().resize(1);
  }

  codet &try_code()
  {
    return static_cast<codet &>(op0());
  }

  const codet &try_code() const
  {
    return static_cast<const codet &>(op0());
  }

  code_declt &get_catch_decl(unsigned i)
  {
    assert((2*i+2)<operands().size());
    return to_code_decl(to_code(operands()[2*i+1]));
  }

  const code_declt &get_catch_decl(unsigned i) const
  {
    assert((2*i+2)<operands().size());
    return to_code_decl(to_code(operands()[2*i+1]));
  }

  codet &get_catch_code(unsigned i)
  {
    assert((2*i+2)<operands().size());
    return to_code(operands()[2*i+2]);
  }

  const codet &get_catch_code(unsigned i) const
  {
    assert((2*i+2)<operands().size());
    return to_code(operands()[2*i+2]);
  }

  void add_catch(const code_declt &to_catch, const codet &code_catch)
  {
    operands().reserve(operands().size()+2);
    copy_to_operands(to_catch);
    copy_to_operands(code_catch);
  }
};

inline const code_try_catcht &to_code_try_catch(const codet &code)
{
  assert(code.get_statement()==ID_try_catch && code.operands().size()>=3);
  return static_cast<const code_try_catcht &>(code);
}

inline code_try_catcht &to_code_try_catch(codet &code)
{
  assert(code.get_statement()==ID_try_catch && code.operands().size()>=3);
  return static_cast<code_try_catcht &>(code);
}

#endif // CPROVER_UTIL_STD_CODE_H
