/*******************************************************************\

Module: Interpreter unit tests.

Author: Diffblue Ltd.

\*******************************************************************/

#include <testing-utils/use_catch.h>

#include <goto-programs/goto_functions.h>
#include <goto-programs/interpreter_class.h>
#include <util/message.h>
#include <util/mp_arith.h>
#include <util/namespace.h>

typedef interpretert::mp_vectort mp_vectort;

class interpreter_testt
{
  symbol_tablet symbol_table;
  goto_functionst goto_functions;
  null_message_handlert null_message_handler;
  interpretert interpreter;

public:
  explicit interpreter_testt()
    : interpreter(symbol_table, goto_functions, null_message_handler)
  {
  }

  mp_vectort evaluate(const exprt &expression)
  {
    mp_vectort result;
    interpreter.evaluate(expression, result);
    return result;
  }
};

SCENARIO("interpreter evaluation null pointer expressions")
{
  interpreter_testt interpreter_test;
  mp_vectort null_vector = {0};

  THEN("null pointer without operands")
  {
    unsignedbv_typet java_char(16);
    pointer_typet pointer_type(java_char, 64);

    constant_exprt constant_expr(ID_NULL, pointer_type);

    mp_vectort mp_vector = interpreter_test.evaluate(constant_expr);

    REQUIRE_THAT(mp_vector, Catch::Equals(null_vector));
  }
  THEN("null pointer with operands")
  {
    pointer_typet outer_pointer_type(empty_typet(), 64);
    constant_exprt outer_expression(
      "0000000000000000000000000000000000000000000000000000000000000000",
      outer_pointer_type);

    outer_expression.add_to_operands(
      null_pointer_exprt(pointer_typet(empty_typet(), 64)));

    mp_vectort mp_vector = interpreter_test.evaluate(outer_expression);

    REQUIRE_THAT(mp_vector, Catch::Equals(null_vector));
  }
}
