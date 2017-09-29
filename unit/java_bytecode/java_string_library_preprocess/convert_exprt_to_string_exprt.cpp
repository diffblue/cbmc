/*******************************************************************\

 Module: Java string library preprocess.
         Test for converting an expression to a string expression.

 Author: Diffblue Limited. All rights reserved.

\*******************************************************************/

#include <catch.hpp>
#include <util/c_types.h>
#include <util/expr.h>
#include <util/std_code.h>
#include <java_bytecode/java_string_library_preprocess.h>
#include <langapi/language_util.h>
#include <java_bytecode/java_bytecode_language.h>
#include <util/namespace.h>
#include <langapi/mode.h>

exprt convert_exprt_to_string_exprt_unit_test(
  java_string_library_preprocesst &preprocess,
  const exprt &deref,
  const source_locationt &loc,
  symbol_tablet &symbol_table,
  code_blockt &init_code)
{
  return preprocess.convert_exprt_to_string_exprt(
    deref, loc, symbol_table, init_code);
}

TEST_CASE("Convert exprt to string exprt")
{
  source_locationt loc;
  symbol_tablet symbol_table;
  namespacet ns(symbol_table);
  code_blockt code;
  java_string_library_preprocesst preprocess;
  preprocess.add_string_type("java.lang.String", symbol_table);
  symbol_typet java_string_type("java::java.lang.String");
  symbol_exprt expr("a", pointer_type(java_string_type));
  convert_exprt_to_string_exprt_unit_test(
    preprocess, expr, loc, symbol_table, code);
  register_language(new_java_bytecode_language);

  std::vector<std::string> code_string;
  for(auto op : code.operands())
    code_string.push_back(from_expr(ns, "", op));

  REQUIRE(code_string.size()==7);
  REQUIRE(code_string[0]=="int cprover_string_length$1;");
  REQUIRE(code_string[1]=="char cprover_string_array$2[INFINITY()];");
  REQUIRE(code_string[2]=="cprover_string_length$1 = a->length;");
  REQUIRE(code_string[3]=="__CPROVER_assume(!(a->data == null));");
  REQUIRE(code_string[4]=="cprover_string_array$2 = *a->data;");
  REQUIRE(code_string[5]=="struct __CPROVER_refined_string_type { int length; "
    "char content[INFINITY()]; } cprover_string$3;");
  REQUIRE(code_string[6]=="cprover_string$3 = { .=cprover_string_length$1, "
    ".=cprover_string_array$2 };");
}
