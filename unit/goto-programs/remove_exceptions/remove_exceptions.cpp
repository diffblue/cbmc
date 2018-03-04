/*******************************************************************\

 Module: Remove-exceptions consistency checks

 Author: DiffBlue Limited. All rights reserved.

\*******************************************************************/

#include <testing-utils/catch.hpp>
#include <testing-utils/load_java_class.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_exceptions.h>

#include <iostream>

static const char *test_classes[] =
{
  "test1",
  "test2",
  "test3",
  "test4",
  "test5",
  "test6",
  "test7"
};

typedef std::unordered_set<irep_idt, irep_id_hash> declared_local_sett;

/// A simple GOTO program interpreter for loop-free programs, which checks that
/// DECL and DEAD statements are well matched on all paths. Note
/// declared_locals, the set of currently-live locals, is passed by value to
/// simplify checking multiple paths.
static void check_all_paths_all_locals_killed(
  const goto_programt::const_targett instruction_pointer,
  declared_local_sett declared_locals)
{
  if(instruction_pointer->is_decl())
  {
    irep_idt id = to_code_decl(instruction_pointer->code).get_identifier();
    REQUIRE(declared_locals.insert(id).second);
  }
  else if(instruction_pointer->is_dead())
  {
    irep_idt id = to_code_dead(instruction_pointer->code).get_identifier();
    // In future we will require this; for now, our model of lexical block
    // structure is limited to try-scopes and is ignorant of code_blockts within
    // them (as they have been removed by the GOTO program stage), which can
    // lead to killing a particular variable more than once on some paths.
    // REQUIRE(declared_locals.erase(id) == 1);
    declared_locals.erase(id);
  }
  else if(instruction_pointer->is_end_function())
  {
    REQUIRE(declared_locals.empty());
    return;
  }

  if(instruction_pointer->targets.empty())
  {
    check_all_paths_all_locals_killed(
      std::next(instruction_pointer), declared_locals);
  }
  else
  {
    for(const auto target : instruction_pointer->targets)
    {
      check_all_paths_all_locals_killed(target, declared_locals);
    }
  }
}

static void check_all_paths_all_locals_killed(
  const goto_programt &goto_program)
{
  declared_local_sett declared_locals;
  check_all_paths_all_locals_killed(
    goto_program.instructions.begin(),
    declared_locals);
}

TEST_CASE("remove_exceptions",
  "[core][goto-programs][remove_exceptions]")
{
  for(const char *test_class : test_classes)
  {
    symbol_tablet new_symbol_table =
      load_java_class(test_class, "./goto-programs/remove_exceptions");

    std::string test_class_prefix = std::string("java::") + test_class;

    stream_message_handlert messages_to_cout(std::cout);
    goto_modelt goto_model;
    goto_model.symbol_table.swap(new_symbol_table);

    goto_convert(goto_model, messages_to_cout);

    remove_exceptions(goto_model);

    for(const auto &name_and_function : goto_model.goto_functions.function_map)
    {
      // Only check functions belonging to the class under test in order to
      // exclude built-in functions that may contain loops.
      if(has_prefix(id2string(name_and_function.first), test_class_prefix))
      {
        check_all_paths_all_locals_killed(name_and_function.second.body);
      }
    }
  }
}
