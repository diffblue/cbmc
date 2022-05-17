/*******************************************************************\

Module: Unit tests for ait

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for ait

#include <testing-utils/message.h>
#include <testing-utils/use_catch.h>

#include <analyses/ai.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/goto_convert_functions.h>

#include <langapi/mode.h>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/c_types.h>
#include <util/optional.h>

/// A very simple analysis that counts executed instructions along a particular
/// path, taking the max at merge points and saturating at 100 instructions.
/// It should indicate that instructions not within a loop have a certain path
/// length, and those reachable from a loop have a path length of 100
/// (i.e. potentially infinity)
class instruction_counter_domaint : public ai_domain_baset
{
public:

  optionalt<unsigned> path_length;

  void transform(
    const irep_idt &,
    trace_ptrt,
    const irep_idt &,
    trace_ptrt,
    ai_baset &,
    const namespacet &) override
  {
    if(*path_length < 100)
      ++*path_length;
  }

  void make_bottom() override
  {
    path_length = {};
  }
  void make_top() override
  {
    UNREACHABLE;
  }
  void make_entry() override
  {
    path_length = 0;
  }
  bool is_bottom() const override
  {
    return !path_length.has_value();
  }
  bool is_top() const override
  {
    UNREACHABLE;
    return true;
  }

  bool merge(const instruction_counter_domaint &b, trace_ptrt, trace_ptrt)
  {
    if(b.is_bottom())
      return false;

    if(!path_length.has_value())
      path_length = 0;

    unsigned old_count = *path_length;
    // Max path length to get here:
    *path_length =
      std::max(*path_length, *b.path_length);
    return *path_length != old_count;
  }
};

class instruction_counter_analysist : public ait<instruction_counter_domaint>
{
public:

  static bool is_y_assignment(const goto_programt::instructiont &i)
  {
    if(!i.is_assign())
      return false;
    return i.assign_lhs().id() == ID_symbol &&
           id2string(to_symbol_expr(i.assign_lhs()).get_identifier())
               .find('y') != std::string::npos;
  }

  static bool is_y_assignment_location(locationt l)
  {
    // At assignments to variables with a 'y' in their name, keep the domain.
    // Otherwise let ait decide whether to keep it.
    return is_y_assignment(*l);
  }
};

static code_function_callt make_void_call(const symbol_exprt &function)
{
  return code_function_callt(function, {});
}

SCENARIO(
  "ait general testing", "[core][analyses][ai][general]")
{
  // Make a program like:

  // __CPROVER_start() { f(); }
  //
  // f() {
  //   int x = 10;
  //   int y = 20;
  //   h();
  //   while(x != 0) {
  //     x -= 1;
  //     y -= 1;
  //     g();
  //   }
  //   g(); // To ensure that this later call doesn't overwrite the earlier
  //        // calls from within the loop (i.e. the top of 'g' is respected
  //        // as a merge point)
  // }
  //
  // Called from within loop, so should have a long possible path
  // g() { int gy = 0; }
  //
  // Only called before loop, so should have a short path
  // h() { int hy = 0; }

  register_language(new_ansi_c_language);
  config.ansi_c.set_LP64();

  goto_modelt goto_model;

  // g:

  symbolt gy;
  gy.name = "gy";
  gy.mode = ID_C;
  gy.type = signed_int_type();

  symbolt g;
  g.name = "g";
  g.mode = ID_C;
  g.type = code_typet({}, empty_typet());
  g.value = code_assignt(gy.symbol_expr(), from_integer(0, signed_int_type()));

  // h:

  symbolt hy;
  hy.name = "hy";
  hy.mode = ID_C;
  hy.type = signed_int_type();

  symbolt h;
  h.name = "h";
  h.mode = ID_C;
  h.type = code_typet({}, empty_typet());
  h.value = code_assignt(hy.symbol_expr(), from_integer(0, signed_int_type()));

  goto_model.symbol_table.add(g);
  goto_model.symbol_table.add(gy);
  goto_model.symbol_table.add(h);
  goto_model.symbol_table.add(hy);

  // f:

  symbolt x;
  x.name = "x";
  x.mode = ID_C;
  x.type = signed_int_type();

  symbolt y;
  y.name = "y";
  y.mode = ID_C;
  y.type = signed_int_type();

  goto_model.symbol_table.add(x);
  goto_model.symbol_table.add(y);

  code_blockt f_body;

  f_body.copy_to_operands(code_declt(x.symbol_expr()));
  f_body.copy_to_operands(code_declt(y.symbol_expr()));

  f_body.copy_to_operands(
    code_assignt(x.symbol_expr(), from_integer(10, signed_int_type())));
  f_body.copy_to_operands(
    code_assignt(y.symbol_expr(), from_integer(20, signed_int_type())));

  f_body.copy_to_operands(make_void_call(h.symbol_expr()));

  code_blockt loop_body;
  loop_body.copy_to_operands(
    code_assignt(
      x.symbol_expr(),
      minus_exprt(x.symbol_expr(), from_integer(1, signed_int_type()))));
  loop_body.copy_to_operands(
    code_assignt(
      y.symbol_expr(),
      minus_exprt(y.symbol_expr(), from_integer(1, signed_int_type()))));
  loop_body.copy_to_operands(make_void_call(g.symbol_expr()));

  code_whilet loop(
    notequal_exprt(x.symbol_expr(), from_integer(0, signed_int_type())),
    loop_body);

  f_body.add_to_operands(std::move(loop));

  f_body.copy_to_operands(make_void_call(g.symbol_expr()));

  symbolt f;
  f.name = "f";
  f.mode = ID_C;
  f.type = code_typet({}, empty_typet());
  f.value = f_body;

  goto_model.symbol_table.add(f);

  // __CPROVER_start:

  symbolt start;
  start.name = goto_functionst::entry_point();
  start.base_name = goto_functionst::entry_point();
  start.mode = ID_C;
  start.type = code_typet({}, empty_typet());
  start.value = make_void_call(f.symbol_expr());

  goto_model.symbol_table.add(start);

  goto_convert(goto_model, null_message_handler);

  WHEN("The target program is analysed")
  {
    instruction_counter_analysist example_analysis;
    example_analysis(goto_model);

    THEN("No state should be bottom")
    {
      for(const auto &gf_entry : goto_model.goto_functions.function_map)
      {
        forall_goto_program_instructions(i_it, gf_entry.second.body)
        {
          REQUIRE_FALSE(example_analysis[i_it].is_bottom());
        }
      }
    }

    THEN("The first y-assignment should have a short path; "
         "the second should have a long one")
    {
      const auto &f_instructions =
        goto_model.goto_functions.function_map.at("f").body.instructions;

      std::vector<goto_programt::const_targett> y_assignments;
      for(auto l = f_instructions.begin(); l != f_instructions.end(); ++l)
        if(instruction_counter_analysist::is_y_assignment_location(l))
          y_assignments.push_back(l);

      REQUIRE(y_assignments.size() == 2);
      REQUIRE_FALSE(example_analysis[y_assignments[0]].is_bottom());
      REQUIRE(*(example_analysis[y_assignments[0]].path_length) < 100);
      REQUIRE_FALSE(example_analysis[y_assignments[1]].is_bottom());
      REQUIRE(*(example_analysis[y_assignments[1]].path_length) == 100);
    }

    THEN("The assignment in function 'g' should have a long path")
    {
      const auto &g_instructions =
        goto_model.goto_functions.function_map.at("g").body.instructions;
      REQUIRE(g_instructions.begin()->is_assign());
      REQUIRE_FALSE(example_analysis[g_instructions.begin()].is_bottom());
      REQUIRE(*example_analysis[g_instructions.begin()].path_length == 100);
    }

    THEN("The assignment in function 'h' should have a short path")
    {
      const auto &h_instructions =
        goto_model.goto_functions.function_map.at("h").body.instructions;
      REQUIRE(h_instructions.begin()->is_assign());
      REQUIRE_FALSE(example_analysis[h_instructions.begin()].is_bottom());
      REQUIRE(*example_analysis[h_instructions.begin()].path_length < 100);
    }
  }
}
