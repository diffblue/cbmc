/*******************************************************************\

 Module: Unit tests for selectively retaining particular domains in ait

 Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// Unit tests for selectively retaining particular domains in ait

#include <testing-utils/catch.hpp>

#include <analyses/ai.h>

#include <ansi-c/ansi_c_language.h>

#include <goto-programs/goto_convert_functions.h>

#include <langapi/mode.h>

#include <util/arith_tools.h>
#include <util/config.h>
#include <util/c_types.h>

/// A very simple analysis that counts executed instructions along a particular
/// path, taking the max at merge points and saturating at 100 instructions.
/// It should indicate that instructions not within a loop have a certain path
/// length, and those reachable from a loop have a path length of 100
/// (i.e. potentially infinity)
class instruction_counter_domaint : public ai_domain_baset
{
public:

  std::unique_ptr<int> path_length;
  int used_move_merge;

  instruction_counter_domaint() : used_move_merge(0)
  {
  }

  instruction_counter_domaint(const instruction_counter_domaint &other) :
    used_move_merge(other.used_move_merge)
  {
    if(other.path_length)
      path_length.reset(new int(*other.path_length));
  }

  void transform(locationt, locationt, ai_baset &, const namespacet &) override
  {
    if(*path_length < 100)
      ++*path_length;
  }

  void make_bottom() override
  {
    path_length.reset();
  }
  void make_top() override
  {
    UNREACHABLE;
  }
  void make_entry() override
  {
    path_length.reset(new int);
    *path_length = 0;
  }
  bool is_bottom() const override
  {
    return path_length == nullptr;
  }
  bool is_top() const override
  {
    UNREACHABLE;
    return true;
  }

  bool merge(const instruction_counter_domaint &b, locationt from, locationt to)
  {
    if(b.is_bottom())
      return false;

    if(!path_length)
    {
      path_length.reset(new int);
      *path_length = 0;
    }

    int old_count = *path_length;
    // Max path length to get here:
    *path_length =
      std::max(*path_length, *b.path_length);
    return *path_length != old_count;
  }

  bool merge(instruction_counter_domaint &&b, locationt from, locationt to)
  {
    if(is_bottom() && !b.is_bottom())
    {
      path_length = std::move(b.path_length);
      ++used_move_merge;
      return true;
    }
    else
      return merge((const instruction_counter_domaint &)b, from, to);
  }
};

class instruction_counter_analysist : public ait<instruction_counter_domaint>
{
public:

  static bool is_y_assignment(const goto_programt::instructiont &i)
  {
    if(!i.is_assign())
      return false;
    const code_assignt &assign = to_code_assign(i.code);
    return
      assign.lhs().id() == ID_symbol &&
      id2string(to_symbol_expr(assign.lhs()).get_identifier()).find('y') !=
      std::string::npos;
  }

  static bool is_y_assignment_location(locationt l)
  {
    // At assignments to variables with a 'y' in their name, keep the domain.
    // Otherwise let ait decide whether to keep it.
    return is_y_assignment(*l);
  }

  instruction_counter_analysist(bool optimise_domains) :
    ait<instruction_counter_domaint>(
      optimise_domains ? is_y_assignment_location : nullptr)
  {
  }
};

static code_function_callt make_void_call(const symbol_exprt &function)
{
  code_function_callt ret;
  ret.function() = function;
  return ret;
}

SCENARIO(
  "ait selective domain storage", "[core][analyses][ai][ai_selective_domains]")
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
  g.type = code_typet({}, void_typet());
  g.value = code_assignt(gy.symbol_expr(), from_integer(0, signed_int_type()));

  // h:

  symbolt hy;
  hy.name = "hy";
  hy.mode = ID_C;
  hy.type = signed_int_type();

  symbolt h;
  h.name = "h";
  h.mode = ID_C;
  h.type = code_typet({}, void_typet());
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

  code_whilet loop;

  loop.cond() =
    notequal_exprt(x.symbol_expr(), from_integer(0, signed_int_type()));

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

  loop.body() = loop_body;

  f_body.move_to_operands(loop);

  f_body.copy_to_operands(make_void_call(g.symbol_expr()));

  symbolt f;
  f.name = "f";
  f.mode = ID_C;
  f.type = code_typet({}, void_typet());
  f.value = f_body;

  goto_model.symbol_table.add(f);

  // __CPROVER_start:

  symbolt start;
  start.name = goto_functionst::entry_point();
  start.mode = ID_C;
  start.type = code_typet({}, void_typet());
  start.value = make_void_call(f.symbol_expr());

  goto_model.symbol_table.add(start);

  null_message_handlert nullout;
  goto_convert(goto_model, nullout);

  WHEN("The target program is analysed without optimised domain storage")
  {
    instruction_counter_analysist unopt_analysis(false);
    unopt_analysis(goto_model);

    THEN("No state should be bottom")
    {
      forall_goto_functions(f_it, goto_model.goto_functions)
      {
        forall_goto_program_instructions(i_it, f_it->second.body)
        {
          REQUIRE(!unopt_analysis[i_it].is_bottom());
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
      REQUIRE(!unopt_analysis[y_assignments[0]].is_bottom());
      REQUIRE(*(unopt_analysis[y_assignments[0]].path_length) < 100);
      REQUIRE(!unopt_analysis[y_assignments[1]].is_bottom());
      REQUIRE(*(unopt_analysis[y_assignments[1]].path_length) == 100);
    }

    THEN("The assignment in function 'g' should have a long path")
    {
      const auto &g_instructions =
        goto_model.goto_functions.function_map.at("g").body.instructions;
      REQUIRE(g_instructions.begin()->is_assign());
      REQUIRE(!unopt_analysis[g_instructions.begin()].is_bottom());
      REQUIRE(*unopt_analysis[g_instructions.begin()].path_length == 100);
    }

    THEN("The assignment in function 'h' should have a short path")
    {
      const auto &h_instructions =
        goto_model.goto_functions.function_map.at("h").body.instructions;
      REQUIRE(h_instructions.begin()->is_assign());
      REQUIRE(!unopt_analysis[h_instructions.begin()].is_bottom());
      REQUIRE(*unopt_analysis[h_instructions.begin()].path_length < 100);
    }

    WHEN("The target program is reanalysed with optimised domain storage")
    {
      instruction_counter_analysist opt_analysis(true);
      opt_analysis(goto_model);

      THEN("At every location, the optimised analysis should either agree "
           "with the unoptimised one, or have a BOTTOM state")
      {
        forall_goto_functions(f_it, goto_model.goto_functions)
        {
          forall_goto_program_instructions(i_it, f_it->second.body)
          {
            const auto &unopt_state = unopt_analysis[i_it];
            const auto &opt_state = opt_analysis[i_it];
            if(!opt_state.is_bottom())
            {
              REQUIRE(!unopt_state.is_bottom());
              REQUIRE(*unopt_state.path_length == *opt_state.path_length);
            }
          }
        }
      }

      THEN("The move-merge optimisation should be used more than for the "
           "unoptimised analysis, and less states should be stored")
      {
        // We have surely broken something if we were *never* able to steal
        // a predecessor instruction's state. It's conceivable the test program
        // has no straight-line code so the optimisation is never possible, but
        // in that case we should change the test to exercise this behaviour.

        int total_unopt_moves = 0;
        int total_opt_moves = 0;
        int total_unopt_bottoms = 0;
        int total_opt_bottoms = 0;

        forall_goto_functions(f_it, goto_model.goto_functions)
        {
          forall_goto_program_instructions(i_it, f_it->second.body)
          {
            const auto &unopt_state = unopt_analysis[i_it];
            const auto &opt_state = opt_analysis[i_it];

            total_unopt_moves += unopt_state.used_move_merge;
            total_opt_moves += opt_state.used_move_merge;

            if(unopt_state.is_bottom())
              ++total_unopt_bottoms;
            if(opt_state.is_bottom())
              ++total_opt_bottoms;
          }
        }

        REQUIRE(total_opt_moves > total_unopt_moves);
        REQUIRE(total_opt_bottoms > total_unopt_bottoms);
      }

      THEN("The optimised analysis state should be retained at 'y', 'gy' and "
           "'hy' assignments")
      {
        bool found_any_y_assignment;

        forall_goto_functions(f_it, goto_model.goto_functions)
        {
          forall_goto_program_instructions(i_it, f_it->second.body)
          {
            if(instruction_counter_analysist::is_y_assignment_location(i_it))
            {
              found_any_y_assignment = true;
              REQUIRE(!opt_analysis[i_it].is_bottom());
            }
          }
        }

        REQUIRE(found_any_y_assignment);
      }

      THEN("The optimised analysis state should be retained at any "
           "control-flow merge point")
      {
        forall_goto_functions(f_it, goto_model.goto_functions)
        {
          forall_goto_program_instructions(i_it, f_it->second.body)
          {
            if(i_it->incoming_edges.size() > 1)
              REQUIRE(!opt_analysis[i_it].is_bottom());
          }
        }
      }

      THEN("The optimised analysis state should be retained at the top and "
           "bottom of all functions")
      {
        forall_goto_functions(f_it, goto_model.goto_functions)
        {
          REQUIRE(!f_it->second.body.instructions.empty());
          REQUIRE(
            !opt_analysis[f_it->second.body.instructions.begin()].is_bottom());
          REQUIRE(
            !opt_analysis[f_it->second.body.get_end_function()].is_bottom());
        }
      }
    }
  }
}
