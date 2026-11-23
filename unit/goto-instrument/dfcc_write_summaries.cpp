/*******************************************************************\

Module: Unit tests for the write summaries of the DFCC loop assigns
        inference

Author: Michael Tautschnig

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>

#include <goto-instrument/contracts/dynamic-frames/dfcc_write_summaries.h>
#include <testing-utils/get_goto_model_from_c.h>
#include <testing-utils/use_catch.h>

#include <functional>

/// The summary of \p function in the program \p code.
static write_summaryt
summary_of(const std::string &code, const irep_idt &function)
{
  const goto_modelt goto_model = get_goto_model_from_c(code);
  const namespacet ns{goto_model.symbol_table};
  write_summariest summaries{goto_model.goto_functions, ns};
  summaries.compute({function});
  return summaries[function];
}

TEST_CASE(
  "Write summaries record writes to globals and through parameters",
  "[core][goto-instrument][dfcc_write_summaries]")
{
  SECTION("Write through a parameter")
  {
    const auto summary = summary_of(
      "void f(int *p, int *q) { *p = *q; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.parameters == std::set<std::size_t>{0});
    REQUIRE(summary.globals.empty());
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("Write to a global")
  {
    const auto summary = summary_of(
      "int g;\n"
      "void f(void) { int l; l = 1; g = l; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.globals == std::set<irep_idt>{"g"});
    REQUIRE(summary.parameters.empty());
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("Write through a local that points to a parameter's object")
  {
    const auto summary = summary_of(
      "void f(int *p, int *q) { int *l = q; *l = 1; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.parameters == std::set<std::size_t>{1});
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("Writes of callees, through the arguments they are given")
  {
    const auto summary = summary_of(
      "int g;\n"
      "void h(int *a) { *a = 1; g = 2; }\n"
      "void f(int *p, int *q) { int l; h(&l); h(q); }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.parameters == std::set<std::size_t>{1});
    REQUIRE(summary.globals == std::set<irep_idt>{"g"});
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("Write through a cast parameter")
  {
    const auto summary = summary_of(
      "void f(void *v) { *(int *)v = 1; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.parameters == std::set<std::size_t>{0});
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("Recursion iterates to a fixpoint")
  {
    const auto summary = summary_of(
      "void f(int *p, int *q, int n)\n"
      "{ if(n) f(q, p, n - 1); else *p = 1; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.parameters == std::set<std::size_t>{0, 1});
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("Array operations and havoc_object write through their pointer")
  {
    const auto summary = summary_of(
      "void f(int *a, int *b, int *c)\n"
      "{\n"
      "  " CPROVER_PREFIX
      "array_set(a, 0);\n"
      "  " CPROVER_PREFIX
      "havoc_object(b);\n"
      "  int t = *c;\n"
      "}\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.parameters == std::set<std::size_t>{0, 1});
    REQUIRE_FALSE(summary.unknown);
  }
}

/// The summary of `f` in \p code after adding an OTHER instruction with
/// \p statement and \p operands to the end of its body.
static write_summaryt summary_with_other(
  const std::string &code,
  const irep_idt &statement,
  const std::function<exprt::operandst(const namespacet &)> &operands)
{
  goto_modelt goto_model = get_goto_model_from_c(code);
  const namespacet ns{goto_model.symbol_table};
  goto_programt &body = goto_model.goto_functions.function_map.at("f").body;
  codet other{statement};
  other.operands() = operands(ns);
  body.insert_before(
    std::prev(body.instructions.end()), goto_programt::make_other(other));
  write_summariest summaries{goto_model.goto_functions, ns};
  summaries.compute({"f"});
  return summaries["f"];
}

TEST_CASE(
  "Write summaries of OTHER instructions",
  "[core][goto-instrument][dfcc_write_summaries]")
{
  const std::string code =
    "_Bool g;\n"
    "void f(int *a, int *b) {}\n"
    "void main() {}\n";

  SECTION("array_equal writes its third operand")
  {
    const auto summary = summary_with_other(
      code,
      ID_array_equal,
      [](const namespacet &ns)
      {
        return exprt::operandst{
          ns.lookup("f::a").symbol_expr(),
          ns.lookup("f::b").symbol_expr(),
          ns.lookup("g").symbol_expr()};
      });
    REQUIRE(summary.globals == std::set<irep_idt>{"g"});
    REQUIRE(summary.parameters.empty());
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("A statement that writes nothing")
  {
    const auto summary = summary_with_other(
      code,
      ID_printf,
      [](const namespacet &ns)
      { return exprt::operandst{ns.lookup("f::a").symbol_expr()}; });
    REQUIRE(summary.globals.empty());
    REQUIRE(summary.parameters.empty());
    REQUIRE_FALSE(summary.unknown);
  }

  SECTION("A statement the analysis does not know")
  {
    const auto summary = summary_with_other(
      code,
      ID_cpp_delete,
      [](const namespacet &ns)
      { return exprt::operandst{ns.lookup("f::a").symbol_expr()}; });
    REQUIRE(summary.unknown);
  }
}

TEST_CASE(
  "Write summaries record what the result may point to",
  "[core][goto-instrument][dfcc_write_summaries]")
{
  SECTION("A parameter or a global")
  {
    const auto summary = summary_of(
      "int g;\n"
      "int *f(int *p, int n) { return n ? p : &g; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.result.parameters == std::set<std::size_t>{0});
    REQUIRE(summary.result.globals == std::set<irep_idt>{"g"});
    REQUIRE_FALSE(summary.result.unknown);
    REQUIRE(summary.parameters.empty());
  }

  SECTION("A pointer loaded from memory")
  {
    const auto summary = summary_of(
      "int *f(int **pp) { return *pp; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.result.unknown);
  }
}

TEST_CASE(
  "Write summaries are unknown where the analysis cannot name the target",
  "[core][goto-instrument][dfcc_write_summaries]")
{
  SECTION("Write through a pointer loaded from memory")
  {
    const auto summary = summary_of(
      "void f(int **pp) { **pp = 1; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Write through a pointer made from an integer")
  {
    const auto summary = summary_of(
      "void f(unsigned long a) { *(int *)a = 1; }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Pointer stored through a member of a union")
  {
    const auto summary = summary_of(
      "void f(int *q)\n"
      "{\n"
      "  union { int *p; unsigned long l; } u;\n"
      "  u.l = (unsigned long)q;\n"
      "  *u.p = 2;\n"
      "}\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Pointer in a union literal")
  {
    const auto summary = summary_of(
      "union U { int *p; unsigned long l; };\n"
      "void f(int *q)\n"
      "{\n"
      "  union U u = {.l = (unsigned long)q};\n"
      "  *u.p = 2;\n"
      "}\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Pointer stored as an integer through a cast pointer")
  {
    const auto summary = summary_of(
      "void f(int *q)\n"
      "{\n"
      "  int *p;\n"
      "  *(unsigned long *)&p = (unsigned long)q;\n"
      "  *p = 2;\n"
      "}\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Pointer loaded from an integer through a cast pointer")
  {
    const auto summary = summary_of(
      "void f(int *q)\n"
      "{\n"
      "  unsigned long l = (unsigned long)q;\n"
      "  **(int **)&l = 2;\n"
      "}\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Call through a function pointer")
  {
    const auto summary = summary_of(
      "void f(void (*fp)(void)) { fp(); }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Call to a function without a body")
  {
    const auto summary = summary_of(
      "void h(int *);\n"
      "void f(void) { int l; h(&l); }\n"
      "void main() {}\n",
      "f");
    REQUIRE(summary.unknown);
  }

  SECTION("Built-ins without a body only write their result")
  {
    const auto summary = summary_of(
      "int nondet_int(void);\n"
      "void f(void) { int l = nondet_int(); }\n"
      "void main() {}\n",
      "f");
    REQUIRE_FALSE(summary.unknown);
    REQUIRE(summary.globals.empty());
  }
}

/// Whether \p program assigns to an expression for which \p predicate holds.
static bool assigns(
  const goto_programt &program,
  const std::function<bool(const exprt &)> &predicate)
{
  for(const auto &instruction : program.instructions)
  {
    if(instruction.is_assign() && predicate(instruction.assign_lhs()))
      return true;
  }
  return false;
}

TEST_CASE(
  "Write summary bodies replace and restore the bodies",
  "[core][goto-instrument][dfcc_write_summaries]")
{
  goto_modelt goto_model = get_goto_model_from_c(
    "int g;\n"
    "void __VERIFIER_record(int *p) { int t = g; *p = t + 1; }\n"
    "void __VERIFIER_unknown(int **pp) { **pp = 1; }\n"
    "void __VERIFIER_uncalled(void) { g = 1; }\n"
    "void user(int *p) { *p = 1; __VERIFIER_record(p); }\n"
    "void loop(void)\n"
    "{\n"
    "  int x;\n"
    "  int *p = &x;\n"
    "  user(&x);\n"
    "  __VERIFIER_unknown(&p);\n"
    "}\n"
    "void main() { __VERIFIER_uncalled(); }\n");
  const namespacet ns{goto_model.symbol_table};
  auto &function_map = goto_model.goto_functions.function_map;
  const std::size_t record_size =
    function_map.at("__VERIFIER_record").body.instructions.size();
  const std::size_t unknown_size =
    function_map.at("__VERIFIER_unknown").body.instructions.size();
  const std::size_t user_size =
    function_map.at("user").body.instructions.size();
  const std::size_t uncalled_size =
    function_map.at("__VERIFIER_uncalled").body.instructions.size();

  const std::function<bool(const exprt &)> is_parameter_dereference =
    [](const exprt &lhs)
  {
    return lhs.id() == ID_dereference &&
           to_dereference_expr(lhs).pointer().id() == ID_symbol &&
           to_symbol_expr(to_dereference_expr(lhs).pointer()).identifier() ==
             "__VERIFIER_record::p";
  };

  {
    // The functions that the body of `loop` may call, directly or through
    // `user`, are summarized.
    write_summary_bodiest summary_bodies{
      goto_model.goto_functions, function_map.at("loop").body, ns};
    const goto_programt &summary = function_map.at("__VERIFIER_record").body;
    REQUIRE(summary.instructions.size() == 2);
    REQUIRE(assigns(summary, is_parameter_dereference));
    REQUIRE(summary.instructions.back().is_end_function());
    // A function that may write through a pointer the summary cannot name,
    // and a function DFCC instruments, keep their bodies.
    REQUIRE(
      function_map.at("__VERIFIER_unknown").body.instructions.size() ==
      unknown_size);
    REQUIRE(function_map.at("user").body.instructions.size() == user_size);
    // A function that `loop` cannot call keeps its body.
    REQUIRE(
      function_map.at("__VERIFIER_uncalled").body.instructions.size() ==
      uncalled_size);
  }

  REQUIRE(
    function_map.at("__VERIFIER_record").body.instructions.size() ==
    record_size);
}
