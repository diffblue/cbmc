/*******************************************************************\

Module: Concrete Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAM_H
#define CPROVER_GOTO_PROGRAM_H

#include <set>

#include <std_code.h>

#include "goto_program_template.h"

class goto_programt:public goto_program_templatet<codet, exprt>
{
public:
  std::ostream& output_instruction(
    const class namespacet &ns,
    const irep_idt &identifier,
    std::ostream& out,
    instructionst::const_iterator it) const;

  goto_programt() { }
  
  // get the variables in decl statements
  typedef std::set<irep_idt> decl_identifierst;
  void get_decl_identifiers(decl_identifierst &decl_identifiers) const;
};

#define forall_goto_program_instructions(it, program) \
  for(goto_programt::instructionst::const_iterator it=(program).instructions.begin(); \
      it!=(program).instructions.end(); it++)

#define Forall_goto_program_instructions(it, program) \
  for(goto_programt::instructionst::iterator it=(program).instructions.begin(); \
      it!=(program).instructions.end(); it++)
 
extern inline bool operator<(const goto_programt::const_targett i1,
                             const goto_programt::const_targett i2)
{
  return order_const_target<codet, exprt>(i1, i2);
}

std::list<exprt> objects_read(const goto_programt::instructiont &);
std::list<exprt> objects_written(const goto_programt::instructiont &);

std::list<exprt> expressions_read(const goto_programt::instructiont &);
std::list<exprt> expressions_written(const goto_programt::instructiont &);

#endif
