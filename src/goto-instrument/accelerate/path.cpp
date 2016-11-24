#include <iostream>

#include <goto-programs/goto_program.h>

#include "path.h"

void output_path(patht &path, goto_programt &program, namespacet &ns,
    std::ostream &str) {
  for (patht::iterator it = path.begin();
       it != path.end();
       ++it) {
    program.output_instruction(ns, "path", str, it->loc);
  }
}
