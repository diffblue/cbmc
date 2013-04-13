#ifndef PATH_H
#define PATH_H

#include <list>

#include <util/std_expr.h>

#include <goto-programs/goto_program.h>

using namespace std;

class path_nodet {
 public:
  path_nodet(goto_programt::targett &_loc) :
      loc(_loc),
      guard(nil_exprt())
  {
  }

  path_nodet(goto_programt::targett &_loc,
             const exprt &_guard) :
      loc(_loc),
      guard(_guard)
  {
  }

  goto_programt::targett loc;
  const exprt guard;
};

typedef list<path_nodet> patht;
typedef list<patht> pathst;

#endif // PATH_H
