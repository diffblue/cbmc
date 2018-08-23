/*******************************************************************\

Module: Test that compound blocks get a location

Author: Kareem Khazem <karkhaz@karkhaz.com>, 2018

\*******************************************************************/

#include "compound_block_locations.h"

#include <testing-utils/catch.hpp>

#include <fstream>
#include <utility>

#include <ansi-c/ansi_c_language.h>

#include <cbmc/cbmc_parse_options.h>

#include <goto-instrument/goto_program2code.h>

#include <goto-programs/goto_model.h>

#include <langapi/language_ui.h>
#include <langapi/mode.h>

#include <util/cmdline.h>
#include <util/config.h>
#include <util/cout_message.h>
#include <util/options.h>
#include <util/tempfile.h>

SCENARIO("Compound blocks should have a location")
{
  compound_block_locationst checker;

  checker.check(
    "/*  1 */  int main()   \n"
    "/*  2 */  {            \n"
    "/*  3 */    int x;     \n"
    "/*  4 */    if(x)      \n"
    "/*  5 */      x = 1;   \n"
    "/*  6 */  }            \n",
    {{ID_ifthenelse, 4}});

  checker.check(
    "/*  1 */  int main()   \n"
    "/*  2 */  {            \n"
    "/*  3 */    int x;     \n"
    "/*  4 */    if(x)      \n"
    "/*  5 */    {          \n"
    "/*  6 */      x = 1;   \n"
    "/*  7 */      x = 1;   \n"
    "/*  8 */    }          \n"
    "/*  9 */  }            \n",
    {{ID_ifthenelse, 4}});

  checker.check(
    "/*  1 */  int main()   \n"
    "/*  2 */  {            \n"
    "/*  3 */    int x;     \n"
    "/*  4 */    if(x)      \n"
    "/*  5 */      x = 1;   \n"
    "/*  6 */    else       \n"
    "/*  7 */      x = 1;   \n"
    "/*  8 */  }            \n",
    {{ID_ifthenelse, 4}});

  checker.check(
    "/*  1 */  int main()         \n"
    "/*  2 */  {                  \n"
    "/*  3 */    int x;           \n"
    "/*  4 */    if(x)            \n"
    "/*  5 */      x = 1;         \n"
    "/*  6 */    else if(x == 2)  \n"
    "/*  7 */    {                \n"
    "/*  8 */      x = 1;         \n"
    "/*  9 */      x = 1;         \n"
    "/* 10 */    }                \n"
    "/* 11 */    else             \n"
    "/* 12 */      x = 1;         \n"
    "/* 13 */  }                  \n",
    {{ID_ifthenelse, 4}, {ID_ifthenelse, 6}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    while(1)                     \n"
    "/*  4 */    {                            \n"
    "/*  5 */      int x = 2;                 \n"
    "/*  6 */    }                            \n"
    "/*  7 */  }                              \n",
    {{ID_while, 3}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    while(1)                     \n"
    "/*  4 */    {                            \n"
    "/*  5 */      while(1)                   \n"
    "/*  5 */      {                          \n"
    "/*  6 */        int x = 1;               \n"
    "/*  7 */      }                          \n"
    "/*  8 */    }                            \n"
    "/*  9 */  }                              \n",
    {{ID_while, 3}, {ID_while, 5}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    while(1)                     \n"
    "/*  4 */    {                            \n"
    "/*  5 */      int x;                     \n"
    "/*  6 */      if(x)                      \n"
    "/*  7 */        int x = 1;               \n"
    "/*  8 */    }                            \n"
    "/*  9 */  }                              \n",
    {{ID_while, 3}, {ID_ifthenelse, 6}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    int x;                       \n"
    "/*  4 */    if(x)                        \n"
    "/*  5 */    {                            \n"
    "/*  6 */      while(1)                   \n"
    "/*  7 */      {                          \n"
    "/*  8 */        int y = 1;               \n"
    "/*  9 */      }                          \n"
    "/* 10 */    }                            \n"
    "/* 11 */  }                              \n",
    {{ID_ifthenelse, 4}, {ID_while, 6}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    int x;                       \n"
    "/*  4 */    if(x)                        \n"
    "/*  5 */    {                            \n"
    "/*  6 */      while(1)                   \n"
    "/*  7 */      {                          \n"
    "/*  8 */        int y = 1;               \n"
    "/*  9 */      }                          \n"
    "/* 10 */    }                            \n"
    "/* 11 */    else                         \n"
    "/* 12 */    {                            \n"
    "/* 13 */      while(1)                   \n"
    "/* 14 */      {                          \n"
    "/* 15 */        while(1)                 \n"
    "/* 16 */        {                        \n"
    "/* 17 */          int y = 1;             \n"
    "/* 18 */        }                        \n"
    "/* 19 */      }                          \n"
    "/* 20 */    }                            \n"
    "/* 21 */  }                              \n",
    {{ID_ifthenelse, 4}, {ID_while, 6}, {ID_while, 13}, {ID_while, 15}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    for(int i = 0; i < 1; ++i)   \n"
    "/*  4 */    {                            \n"
    "/*  5 */      int x;                     \n"
    "/*  6 */    }                            \n"
    "/*  7 */  }                              \n",
    {{ID_for, 3}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    for(int i = 0; i < 1; ++i)   \n"
    "/*  4 */    {                            \n"
    "/*  5 */      int x;                     \n"
    "/*  6 */      for(int j = 0; j < 3; ++j) \n"
    "/*  7 */      {                          \n"
    "/*  8 */        int y;                   \n"
    "/*  9 */      }                          \n"
    "/* 10 */    }                            \n"
    "/* 11 */  }                              \n",
    {{ID_for, 3}, {ID_for, 6}});

  // In the absence of a better place to put it, the source location of a
  // do-while block is equal to the source location of its first statement.

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    do                           \n"
    "/*  4 */    {                            \n"
    "/*  5 */      int x;                     \n"
    "/*  6 */    } while(1);                  \n"
    "/*  7 */  }                              \n",
    {{ID_dowhile, 5}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    do                           \n"
    "/*  4 */    {                            \n"
    "/*  5 */      int x;                     \n"
    "/*  6 */      int y;                     \n"
    "/*  7 */      int z = x + y;             \n"
    "/*  8 */    } while(1);                  \n"
    "/*  9 */  }                              \n",
    {{ID_dowhile, 5}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    int x;                       \n"
    "/*  4 */    do                           \n"
    "/*  5 */    {                            \n"
    "/*  6 */      int x;                     \n"
    "/*  7 */      int y;                     \n"
    "/*  8 */      int z = x + y;             \n"
    "/*  9 */    } while(x);                  \n"
    "/* 10 */  }                              \n",
    {{ID_dowhile, 6}});

  checker.check(
    "/*  1 */  int main()                     \n"
    "/*  2 */  {                              \n"
    "/*  3 */    int x;                       \n"
    "/*  4 */    if(x)                        \n"
    "/*  5 */    {                            \n"
    "/*  6 */      do                         \n"
    "/*  7 */      {                          \n"
    "/*  8 */        int y;                   \n"
    "/*  9 */      } while(x);                \n"
    "/* 10 */    }                            \n"
    "/* 11 */  }                              \n",
    {{ID_ifthenelse, 4}, {ID_dowhile, 8}});
}

void compound_block_locationst::check(
  const std::string &program,
  const std::list<std::pair<const irep_idt, const unsigned>> &expected)
{
  INFO("Given the following program:\n" + program);
  check_compound_block_locations(program, expected);
}

void compound_block_locationst::check_compound_block_locations(
  const std::string &program,
  const std::list<std::pair<const irep_idt, const unsigned>> &expected)
{
  temporary_filet tmp("compound-block-locations_", ".c");
  std::ofstream of(tmp().c_str());
  REQUIRE(of.is_open());

  of << program << std::endl;
  of.close();

  register_language(new_ansi_c_language);
  cmdlinet cmdline;
  cmdline.args.push_back(tmp());
  config.main = "main";
  config.set(cmdline);

  optionst opts;
  cbmc_parse_optionst::set_default_options(opts);

  ui_message_handlert mh(cmdline, "compound-block-locations");
  mh.set_verbosity(0);
  messaget log(mh);

  goto_modelt gm;
  int ret;
  ret = cbmc_parse_optionst::get_goto_program(gm, opts, cmdline, log, mh);
  REQUIRE(ret == -1);

  const auto found = gm.goto_functions.function_map.find("main");
  REQUIRE(found != gm.goto_functions.function_map.end());

  code_blockt block;
  symbol_tablet st_copy(gm.symbol_table);
  std::list<irep_idt> local_static, type_names;
  std::unordered_set<irep_idt> typedef_names;
  std::set<std::string> system_headers;
  goto_program2codet g2c(
    "main",
    found->second.body,
    st_copy,
    block,
    local_static,
    type_names,
    typedef_names,
    system_headers);
  g2c();

  std::list<std::pair<const irep_idt, const unsigned>> copy(expected);
  recurse_on_block(block, copy);

  std::stringstream ss;
  ss << "Expected but did not observe the following lines to have blocks with "
     << "locations: ";
  for(const auto &pair : copy)
    ss << "'" << types.at(pair.first) << "' at line "
       << std::to_string(pair.second) << ", ";
  INFO(ss.str());
  REQUIRE(copy.empty());
}

void compound_block_locationst::recurse_on_block(
  const exprt &expr,
  std::list<std::pair<const irep_idt, const unsigned>> &expected)
{
  if(expr.id() == ID_code)
  {
    const codet code = to_code(expr);
    for(const auto &pair : types)
    {
      if(code.get_statement() != pair.first)
        continue;
      INFO("Found an instruction of type " + pair.second);
      const auto &top = expected.front();
      REQUIRE(code.get_statement() == top.first);
      const source_locationt &loc = code.source_location();
      REQUIRE(loc.is_not_nil());
      REQUIRE(std::stoul(loc.get_line().c_str()) == top.second);
      expected.pop_front();
      break;
    }
  }

  for(const auto &child : expr.operands())
    recurse_on_block(child, expected);
}
