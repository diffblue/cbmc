/*******************************************************************\

Module: Unit test for allocate_objectst

Author: Diffblue Ltd

\*******************************************************************/

#include <goto-programs/allocate_objects.h>

#include <util/c_types.h>
#include <util/symbol_table.h>

#include <testing-utils/use_catch.h>

TEST_CASE(
  "Tests the absence of a bug that crashed allocate_objects",
  "[core][goto-programs][allocate_objects]")
{
  symbol_tablet symtab{};
  // Because __a_temp will return a const reference to temporary
  // irep_idt, and we stored the reference instead of copying the
  // value ...
  allocate_objectst allocate_object{
    ID_C, source_locationt{}, "__a_temp", symtab};
  // This crashed because it tried to access the invalid reference
  // to the name_prefix irep_idt
  allocate_object.allocate_automatic_local_object(size_type());
}
