/*******************************************************************\

Module: Call graph test utils

Author: Chris Smowton, chris.smowton@diffblue.com

\*******************************************************************/

#ifndef CPROVER_TESTING_UTILS_CALL_GRAPH_TEST_UTILS_H
#define CPROVER_TESTING_UTILS_CALL_GRAPH_TEST_UTILS_H

#include <map>
#include <set>

#include <util/symbol.h>

class codet;

symbolt
create_void_function_symbol(const irep_idt &name, const codet &code);

bool multimap_key_matches(
  const std::multimap<irep_idt, irep_idt> &map,
  const irep_idt &key,
  const std::set<irep_idt> &values);

#endif /* CPROVER_TESTING_UTILS_CALL_GRAPH_TEST_UTILS_HT */
