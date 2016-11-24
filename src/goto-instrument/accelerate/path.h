#ifndef PATH_H
#define PATH_H

#include <iosfwd>
#include <list>

#include <util/std_expr.h>
#include <util/namespace.h>

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

  void output(goto_programt &program, std::ostream &str);

  goto_programt::targett loc;
  const exprt guard;
};

typedef list<path_nodet> patht;
typedef list<patht> pathst; 

void output_path(patht &path, goto_programt &program, namespacet &ns, std::ostream &str);

#endif // PATH_H
