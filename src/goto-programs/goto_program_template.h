/*******************************************************************\

Module: Goto Program Template

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_TEMPLATE_H
#define CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_TEMPLATE_H

/*! \defgroup gr_goto_programs Goto programs */

#include <cassert>
#include <iosfwd>
#include <set>
#include <limits>
#include <sstream>
#include <string>

#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/source_location.h>
#include <util/std_expr.h>
#include <util/irep_hash.h>

typedef enum
{
  NO_INSTRUCTION_TYPE=0,
  GOTO=1,           // branch, possibly guarded
  ASSUME=2,         // non-failing guarded self loop
  ASSERT=3,         // assertions
  OTHER=4,          // anything else
  SKIP=5,           // just advance the PC
  START_THREAD=6,   // spawns an asynchronous thread
  END_THREAD=7,     // end the current thread
  LOCATION=8,       // semantically like SKIP
  END_FUNCTION=9,   // exit point of a function
  ATOMIC_BEGIN=10,  // marks a block without interleavings
  ATOMIC_END=11,    // end of a block without interleavings
  RETURN=12,        // set function return value (no control-flow change)
  ASSIGN=13,        // assignment lhs:=rhs
  DECL=14,          // declare a local variable
  DEAD=15,          // marks the end-of-live of a local variable
  FUNCTION_CALL=16, // call a function
  THROW=17,         // throw an exception
  CATCH=18          // catch an exception
} goto_program_instruction_typet;

std::ostream &operator<<(std::ostream &, goto_program_instruction_typet);

/*! \brief A generic container class for a control flow graph
           for one function, in the form of a goto-program
    \ingroup gr_goto_programs
*/
template <class codeT, class guardT>
class goto_program_templatet
{
public:
  /*! \brief copy constructor
      \param[in] src an empty goto program
      \remark Use copy_from to copy non-empty goto-programs
  */
  goto_program_templatet(const goto_program_templatet &src)
  {
    // DO NOT COPY ME! I HAVE POINTERS IN ME!
    assert(src.instructions.empty());
  }

  /*! \brief assignment operator
      \param[in] src an empty goto program
      \remark Use copy_from to copy non-empty goto-programs
  */
  goto_program_templatet &operator=(const goto_program_templatet &src)
  {
    // DO NOT COPY ME! I HAVE POINTERS IN ME!
    assert(src.instructions.empty());
    instructions.clear();
    update();
    return *this;
  }

  /*! \brief Container for an instruction of the goto-program
  */
  class instructiont
  {
  public:
    codeT code;

    //! function this belongs to
    irep_idt function;

    //! the location of the instruction in the source file
    source_locationt source_location;

    //! what kind of instruction?
    goto_program_instruction_typet type;

    //! guard for gotos, assume, assert
    guardT guard;

    // The below will eventually become a single target only.
    //! the target for gotos and for start_thread nodes
    typedef typename std::list<instructiont>::iterator targett;
    typedef typename std::list<instructiont>::const_iterator const_targett;
    typedef std::list<targett> targetst;
    typedef std::list<const_targett> const_targetst;

    targetst targets;

    // for the usual case of a single target
    targett get_target() const
    {
      assert(targets.size()==1);
      return targets.front();
    }

    // for the usual case of a single target
    void set_target(targett t)
    {
      targets.clear();
      targets.push_back(t);
    }

    //! goto target labels
    typedef std::list<irep_idt> labelst;
    labelst labels;

    // will go away
    std::set<targett> incoming_edges;

    //! is this node a branch target?
    bool is_target() const
    { return target_number!=nil_target; }

    //! clear the node
    void clear(goto_program_instruction_typet _type)
    {
      type=_type;
      targets.clear();
      guard=true_exprt();
      code.make_nil();
    }

    void make_goto() { clear(GOTO); }
    void make_return() { clear(RETURN); }
    void make_skip() { clear(SKIP); }
    void make_throw() { clear(THROW); }
    void make_catch() { clear(CATCH); }
    void make_assertion(const guardT &g) { clear(ASSERT); guard=g; }
    void make_assumption(const guardT &g) { clear(ASSUME); guard=g; }
    void make_assignment() { clear(ASSIGN); }
    void make_other(const codeT &_code) { clear(OTHER); code=_code; }
    void make_decl() { clear(DECL); }
    void make_dead() { clear(DEAD); }
    void make_atomic_begin() { clear(ATOMIC_BEGIN); }
    void make_atomic_end() { clear(ATOMIC_END); }

    void make_goto(targett _target)
    {
      make_goto();
      targets.push_back(_target);
    }

    void make_goto(targett _target, const guardT &g)
    {
      make_goto(_target);
      guard=g;
    }

    void make_function_call(const codeT &_code)
    {
      clear(FUNCTION_CALL);
      code=_code;
    }

    bool is_goto         () const { return type==GOTO;          }
    bool is_return       () const { return type==RETURN;        }
    bool is_assign       () const { return type==ASSIGN;        }
    bool is_function_call() const { return type==FUNCTION_CALL; }
    bool is_throw        () const { return type==THROW;         }
    bool is_catch        () const { return type==CATCH;         }
    bool is_skip         () const { return type==SKIP;          }
    bool is_location     () const { return type==LOCATION;      }
    bool is_other        () const { return type==OTHER;         }
    bool is_decl         () const { return type==DECL;          }
    bool is_dead         () const { return type==DEAD;          }
    bool is_assume       () const { return type==ASSUME;        }
    bool is_assert       () const { return type==ASSERT;        }
    bool is_atomic_begin () const { return type==ATOMIC_BEGIN;  }
    bool is_atomic_end   () const { return type==ATOMIC_END;    }
    bool is_start_thread () const { return type==START_THREAD;  }
    bool is_end_thread   () const { return type==END_THREAD;    }
    bool is_end_function () const { return type==END_FUNCTION;  }

    instructiont():
      source_location(static_cast<const source_locationt &>(get_nil_irep())),
      type(NO_INSTRUCTION_TYPE),
      guard(true_exprt()),
      location_number(0),
      target_number(nil_target)
    {
    }

    explicit instructiont(goto_program_instruction_typet _type):
      source_location(static_cast<const source_locationt &>(get_nil_irep())),
      type(_type),
      guard(true_exprt()),
      location_number(0),
      target_number(nil_target)
    {
    }

    //! swap two instructions
    void swap(instructiont &instruction)
    {
      instruction.code.swap(code);
      instruction.source_location.swap(source_location);
      std::swap(instruction.type, type);
      instruction.guard.swap(guard);
      instruction.targets.swap(targets);
      instruction.function.swap(function);
    }

    //! Uniquely identify an invalid target or location
    #if (defined _MSC_VER && _MSC_VER <= 1800)
    // Visual Studio <= 2013 does not support constexpr, making
    // numeric_limits::max() unviable for a static const member
    static const unsigned nil_target=
      static_cast<unsigned>(-1);
    #else
    static const unsigned nil_target=
      std::numeric_limits<unsigned>::max();
    #endif

    //! A globally unique number to identify a program location.
    //! It's guaranteed to be ordered in program order within
    //! one goto_program.
    unsigned location_number;

    //! Number unique per function to identify loops
    unsigned loop_number;

    //! A number to identify branch targets.
    //! This is \ref nil_target if it's not a target.
    unsigned target_number;

    //! Returns true if the instruction is a backwards branch.
    bool is_backwards_goto() const
    {
      if(!is_goto())
        return false;

      for(const auto &t : targets)
        if(t->location_number<=location_number)
          return true;

      return false;
    }

    std::string to_string() const
    {
      std::ostringstream instruction_id_builder;
      instruction_id_builder << type;
      return instruction_id_builder.str();
    }

    std::size_t stable_hash() const
    {
      return hash_combine(code.stable_hash(), guard.stable_hash());
    }
  };

  typedef std::list<instructiont> instructionst;

  typedef typename instructionst::iterator targett;
  typedef typename instructionst::const_iterator const_targett;
  typedef typename std::list<targett> targetst;
  typedef typename std::list<const_targett> const_targetst;

  //! The list of instructions in the goto program
  instructionst instructions;

  // Convert a const_targett to a targett - use with care and avoid
  // whenever possible
  targett const_cast_target(const_targett t)
  {
    return instructions.erase(t, t);
  }

  // Dummy for templates with possible const contexts
  const_targett const_cast_target(const_targett t) const
  {
    return t;
  }

  void get_successors(
    targett target,
    targetst &successors);

  void get_successors(
    const_targett target,
    const_targetst &successors) const;

  void compute_incoming_edges();

  //! Insertion that preserves jumps to "target".
  void insert_before_swap(targett target)
  {
    assert(target!=instructions.end());
    targett next=target;
    next++;
    instructions.insert(next, instructiont())->swap(*target);
  }

  //! Insertion that preserves jumps to "target".
  //! The instruction is destroyed.
  void insert_before_swap(targett target, instructiont &instruction)
  {
    insert_before_swap(target);
    target->swap(instruction);
  }

  //! Insertion that preserves jumps to "target".
  //! The program p is destroyed.
  void insert_before_swap(
    targett target,
    goto_program_templatet<codeT, guardT> &p)
  {
    assert(target!=instructions.end());
    if(p.instructions.empty())
      return;
    insert_before_swap(target, p.instructions.front());
    targett next=target;
    next++;
    p.instructions.erase(p.instructions.begin());
    instructions.splice(next, p.instructions);
  }

  //! Insertion before the given target
  //! \return newly inserted location
  targett insert_before(targett target)
  {
    return instructions.insert(target, instructiont());
  }

  //! Insertion before the given target
  //! \return newly inserted location
  targett insert_before(const_targett target)
  {
    return instructions.insert(target, instructiont());
  }

  //! Insertion after the given target
  //! \return newly inserted location
  targett insert_after(targett target)
  {
    targett t=target;
    t++;
    return instructions.insert(t, instructiont());
  }

  //! Appends the given program, which is destroyed
  void destructive_append(goto_program_templatet<codeT, guardT> &p)
  {
    instructions.splice(instructions.end(),
                        p.instructions);
    // BUG: The iterators to p-instructions are invalidated!
  }

  //! Inserts the given program at the given location.
  //! The program is destroyed.
  void destructive_insert(
    targett target,
    goto_program_templatet<codeT, guardT> &p)
  {
    instructions.splice(target, p.instructions);
    // BUG: The iterators to p-instructions are invalidated!
  }

  //! Inserts the given program at the given location.
  //! The program is destroyed.
  void destructive_insert(
    const_targett target,
    goto_program_templatet<codeT, guardT> &p)
  {
    instructions.splice(target, p.instructions);
    // BUG: The iterators to p-instructions are invalidated!
  }

  //! Adds an instruction at the end.
  //! \return The newly added instruction.
  targett add_instruction()
  {
    instructions.push_back(instructiont());
    return --instructions.end();
  }

  //! Adds an instruction of given type at the end.
  //! \return The newly added instruction.
  targett add_instruction(goto_program_instruction_typet type)
  {
    instructions.push_back(instructiont(type));
    return --instructions.end();
  }

  //! Output goto program to given stream
  std::ostream &output(
    const namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out) const;

  //! Output goto-program to given stream
  std::ostream &output(std::ostream &out) const
  {
    return output(namespacet(symbol_tablet()), "", out);
  }

  //! Output a single instruction
  virtual std::ostream &output_instruction(
    const namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out,
    typename instructionst::const_iterator it) const=0;

  //! Compute the target numbers
  void compute_target_numbers();

  //! Compute location numbers
  void compute_location_numbers(unsigned &nr)
  {
    for(auto &i : instructions)
      i.location_number=nr++;
  }

  //! Compute location numbers
  void compute_location_numbers()
  {
    unsigned nr=0;
    compute_location_numbers(nr);
  }

  //! Compute loop numbers
  void compute_loop_numbers();

  //! Update all indices
  void update();

  //! Human-readable loop name
  static irep_idt loop_id(const_targett target)
  {
    return id2string(target->function)+"."+
           std::to_string(target->loop_number);
  }

  //! Is the program empty?
  bool empty() const
  {
    return instructions.empty();
  }

  //! Constructor
  goto_program_templatet()
  {
  }

  virtual ~goto_program_templatet()
  {
  }

  //! Swap the goto program
  void swap(goto_program_templatet<codeT, guardT> &program)
  {
    program.instructions.swap(instructions);
  }

  //! Clear the goto program
  void clear()
  {
    instructions.clear();
  }

  //! Copy a full goto program, preserving targets
  void copy_from(const goto_program_templatet<codeT, guardT> &src);

  //! Does the goto program have an assertion?
  bool has_assertion() const;
};

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::compute_loop_numbers()
{
  unsigned nr=0;
  for(auto &i : instructions)
    if(i.is_backwards_goto())
      i.loop_number=nr++;
}

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::get_successors(
  targett target,
  targetst &successors)
{
  successors.clear();
  if(target==instructions.end())
    return;

  targett next=target;
  next++;

  const instructiont &i=*target;

  if(i.is_goto())
  {
    for(const auto &t : i.targets)
      successors.push_back(t);

    if(!i.guard.is_true() && next!=instructions.end())
      successors.push_back(next);
  }
  else if(i.is_start_thread())
  {
    for(const auto &t : i.targets)
      successors.push_back(t);

    if(next!=instructions.end())
      successors.push_back(next);
  }
  else if(i.is_end_thread())
  {
    // no successors
  }
  else if(i.is_throw())
  {
    // the successors are non-obvious
  }
  else if(i.is_assume())
  {
    if(!i.guard.is_false() && next!=instructions.end())
      successors.push_back(next);
  }
  else
  {
    if(next!=instructions.end())
      successors.push_back(next);
  }
}

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::get_successors(
  const_targett target,
  const_targetst &successors) const
{
  successors.clear();
  if(target==instructions.end())
    return;

  const_targett next=target;
  next++;

  const instructiont &i=*target;

  if(i.is_goto())
  {
    for(const auto &t : i.targets)
      successors.push_back(t);

    if(!i.guard.is_true() && next!=instructions.end())
      successors.push_back(next);
  }
  else if(i.is_start_thread())
  {
    for(const auto &t : i.targets)
      successors.push_back(t);

    if(next!=instructions.end())
      successors.push_back(next);
  }
  else if(i.is_end_thread())
  {
    // no successors
  }
  else if(i.is_assume())
  {
    if(!i.guard.is_false() && next!=instructions.end())
      successors.push_back(next);
  }
  else
  {
    if(next!=instructions.end())
      successors.push_back(next);
  }
}

#include <langapi/language_util.h>
#include <iomanip>

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::update()
{
  compute_incoming_edges();
  compute_target_numbers();
  compute_location_numbers();
}

template <class codeT, class guardT>
std::ostream &goto_program_templatet<codeT, guardT>::output(
  const namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out) const
{
  // output program

  for(typename instructionst::const_iterator
      it=instructions.begin();
      it!=instructions.end();
      it++)
    output_instruction(ns, identifier, out, it);

  return out;
}

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::compute_target_numbers()
{
  // reset marking

  for(auto &i : instructions)
    i.target_number=instructiont::nil_target;

  // mark the goto targets

  for(const auto &i : instructions)
  {
    for(const auto &t : i.targets)
    {
      if(t!=instructions.end())
        t->target_number=0;
    }
  }

  // number the targets properly
  unsigned cnt=0;

  for(auto &i : instructions)
  {
    if(i.is_target())
    {
      i.target_number=++cnt;
      assert(i.target_number!=0);
    }
  }

  // check the targets!
  // (this is a consistency check only)

  for(const auto &i : instructions)
  {
    for(const auto &t : i.targets)
    {
      if(t!=instructions.end())
      {
        assert(t->target_number!=0);
        assert(t->target_number!=instructiont::nil_target);
      }
    }
  }
}

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::copy_from(
  const goto_program_templatet<codeT, guardT> &src)
{
  // Definitions for mapping between the two programs
  typedef std::map<const_targett, targett> targets_mappingt;
  targets_mappingt targets_mapping;

  clear();

  // Loop over program - 1st time collects targets and copy

  for(typename instructionst::const_iterator
      it=src.instructions.begin();
      it!=src.instructions.end();
      it++)
  {
    targett new_instruction=add_instruction();
    targets_mapping[it]=new_instruction;
    *new_instruction=*it;
  }

  // Loop over program - 2nd time updates targets

  for(auto &i : instructions)
  {
    for(auto &t : i.targets)
    {
      typename targets_mappingt::iterator
        m_target_it=targets_mapping.find(t);

      if(m_target_it==targets_mapping.end())
        throw "copy_from: target not found";

      t=m_target_it->second;
    }
  }

  compute_incoming_edges();
  compute_target_numbers();
}

// number them
template <class codeT, class guardT>
bool goto_program_templatet<codeT, guardT>::has_assertion() const
{
  for(const auto &i : instructions)
    if(i.is_assert() && !i.guard.is_true())
      return true;

  return false;
}

template <class codeT, class guardT>
void goto_program_templatet<codeT, guardT>::compute_incoming_edges()
{
  for(auto &i : instructions)
  {
    i.incoming_edges.clear();
  }

  for(typename instructionst::iterator
      it=instructions.begin();
      it!=instructions.end();
      it++)
  {
    targetst successors;

    get_successors(it, successors);

    for(const auto &s : successors)
    {
      if(s!=instructions.end())
        s->incoming_edges.insert(it);
    }
  }
}

template <class codeT, class guardT>
inline bool order_const_target(
  const typename goto_program_templatet<codeT, guardT>::const_targett i1,
  const typename goto_program_templatet<codeT, guardT>::const_targett i2)
{
  const typename goto_program_templatet<codeT, guardT>::instructiont &_i1=*i1;
  const typename goto_program_templatet<codeT, guardT>::instructiont &_i2=*i2;
  return &_i1<&_i2;
}

template <class codeT, class guardT>
struct const_target_hash_templatet
{
  std::size_t operator()(
    const typename goto_program_templatet<codeT, guardT>::const_targett t) const
  { return t->location_number; }
};

#endif // CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_TEMPLATE_H
