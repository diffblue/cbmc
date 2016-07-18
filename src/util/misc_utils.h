#ifndef CPROVER_MISC_UTILS_H
#define CPROVER_MISC_UTILS_H

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <util/string2int.h>
#include <util/config.h>
#include <util/namespace.h>

#include <string>
#include <vector>
#include <iostream>

#include "irep.h"

// Strip const qualifier from this
#define ths \
  ((std::remove_const<std::remove_pointer<decltype(this)>::type>::type *)(this))

#define chk(cond, s) \
  if (!(cond)) { \
    std::string to_throw="error"; \
    std::string msg=s; \
    if(!msg.empty()) { to_throw=msg; } \
    throw (">> " + to_throw + \
      "\n>> line: " + std::to_string(__LINE__) + \
      "\n>> file: " + __FILE__ + "\n"); \
  }

#define _assert(cond, s) \
  if (!(cond)) { \
    std::cout << s << std::endl; \
    assert(cond); \
  }

namespace misc
{
  typedef goto_functionst::goto_functiont goto_functiont;

  const irep_idt get_identifier(const exprt &expr);
  const irep_idt get_function_name(goto_programt::const_targett l);

  // only use if we don't need to access the element (use find() then)
  template <typename M, typename K>
  bool has(const M &m, const K &k)
  {
    return m.find(k)!=m.end();
  }

  void output_goto_instruction(
    const goto_functionst &goto_functions,
    const namespacet &ns,
    std::ostream &out,
    goto_programt::const_targett l);

  std::string strip_string(const std::string &s);

  void split_string(
    const std::string &s,
    char delim,
    std::vector<std::string> &result,
    bool strip=false);

  void get_location_number_map(
    const goto_functionst &goto_functions,
    std::map<unsigned, goto_programt::const_targett> &map);

  void get_locations(
    const goto_functionst &goto_functions,
    std::set<goto_programt::const_targett> &set);
}

#endif
