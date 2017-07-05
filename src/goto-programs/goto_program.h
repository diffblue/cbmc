/*******************************************************************\

Module: Concrete Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Concrete Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_H
#define CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_H

#include <set>

#include <util/std_code.h>

#include "goto_program_template.h"

/*! \brief A specialization of goto_program_templatet over
           goto programs in which instructions have codet type.
*/
class goto_programt:public goto_program_templatet<codet, exprt>
{
public:
  std::ostream &output_instruction(
    const class namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out,
    instructionst::const_iterator it) const;

  std::ostream &output_instruction(
    const class namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out,
    const instructiont &instruction) const;

  goto_programt() { }

  // Copying is unavailable as base class copy is deleted
  // MSVC is unable to automatically determine this
  goto_programt(const goto_programt &)=delete;
  goto_programt &operator=(const goto_programt &)=delete;

  // Move operations need to be explicitly enabled as they are deleted with the
  // copy operations
  // default for move operations isn't available on Windows yet, so define
  //  explicitly (see https://msdn.microsoft.com/en-us/library/hh567368.aspx
  //  under "Defaulted and Deleted Functions")

  goto_programt(goto_programt &&other):
    goto_program_templatet(std::move(other))
  {
  }

  goto_programt &operator=(goto_programt &&other)
  {
    goto_program_templatet::operator=(std::move(other));
    return *this;
  }

  // get the variables in decl statements
  typedef std::set<irep_idt> decl_identifierst;
  void get_decl_identifiers(decl_identifierst &decl_identifiers) const;
};

#define forall_goto_program_instructions(it, program) \
  for(goto_programt::instructionst::const_iterator \
      it=(program).instructions.begin(); \
      it!=(program).instructions.end(); it++)

#define Forall_goto_program_instructions(it, program) \
  for(goto_programt::instructionst::iterator \
      it=(program).instructions.begin(); \
      it!=(program).instructions.end(); it++)

inline bool operator<(
  const goto_programt::const_targett i1,
  const goto_programt::const_targett i2)
{
  return order_const_target<codet, exprt>(i1, i2);
}

// NOLINTNEXTLINE(readability/identifiers)
typedef struct const_target_hash_templatet<codet, exprt> const_target_hash;

std::list<exprt> objects_read(const goto_programt::instructiont &);
std::list<exprt> objects_written(const goto_programt::instructiont &);

std::list<exprt> expressions_read(const goto_programt::instructiont &);
std::list<exprt> expressions_written(const goto_programt::instructiont &);

std::string as_string(
  const namespacet &ns,
  const goto_programt::instructiont &);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_H
