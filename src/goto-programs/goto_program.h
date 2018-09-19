/*******************************************************************\

Module: Concrete Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Concrete Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_H
#define CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_H

#include <iosfwd>
#include <set>
#include <limits>
#include <sstream>
#include <string>

#include <util/invariant.h>
#include <util/namespace.h>
#include <util/symbol_table.h>
#include <util/source_location.h>
#include <util/std_expr.h>
#include <util/std_code.h>

/// The type of an instruction in a GOTO program.
enum goto_program_instruction_typet
{
  NO_INSTRUCTION_TYPE = 0,
  GOTO = 1,            // branch, possibly guarded
  ASSUME = 2,          // non-failing guarded self loop
  ASSERT = 3,          // assertions
  OTHER = 4,           // anything else
  SKIP = 5,            // just advance the PC
  START_THREAD = 6,    // spawns an asynchronous thread
  END_THREAD = 7,      // end the current thread
  LOCATION = 8,        // semantically like SKIP
  END_FUNCTION = 9,    // exit point of a function
  ATOMIC_BEGIN = 10,   // marks a block without interleavings
  ATOMIC_END = 11,     // end of a block without interleavings
  RETURN = 12,         // set function return value (no control-flow change)
  ASSIGN = 13,         // assignment lhs:=rhs
  DECL = 14,           // declare a local variable
  DEAD = 15,           // marks the end-of-live of a local variable
  FUNCTION_CALL = 16,  // call a function
  THROW = 17,          // throw an exception
  CATCH = 18,          // push, pop or enter an exception handler
  INCOMPLETE_GOTO = 19 // goto where target is yet to be determined
};

std::ostream &operator<<(std::ostream &, goto_program_instruction_typet);

/// A generic container class for the GOTO intermediate representation of one
/// function.
///
/// A function is represented by a std::list of instructions. Execution starts
/// in the first instruction of the list. Then, the execution of the i-th
/// instruction is followed by the execution of the (i+1)-th instruction unless
/// instruction i jumps to some other instruction in the list. See the internal
/// class instructiont for additional details
///
/// Although it is straightforward to compute the control flow graph (CFG) of a
/// function from the list of instructions and the goto target locations in
/// instructions, the GOTO intermediate representation is _not_ regarded as the
/// CFG of a function. See instead the class cfg_baset, which is based on grapht
/// and allows for easier implementation of generic graph algorithms (e.g.,
/// dominator analysis).
class goto_programt
{
public:
  /// Copying is deleted as this class contains pointers that cannot be copied
  goto_programt(const goto_programt &)=delete;
  goto_programt &operator=(const goto_programt &)=delete;

  // Move operations need to be explicitly enabled as they are deleted with the
  // copy operations
  // default for move operations isn't available on Windows yet, so define
  //  explicitly (see https://msdn.microsoft.com/en-us/library/hh567368.aspx
  //  under "Defaulted and Deleted Functions")

  goto_programt(goto_programt &&other):
    instructions(std::move(other.instructions))
  {
  }

  goto_programt &operator=(goto_programt &&other)
  {
    instructions=std::move(other.instructions);
    return *this;
  }

  /// This class represents an instruction in the GOTO intermediate
  /// representation.  Three fields are key:
  ///
  /// - type:  an enum value describing the action performed by this instruction
  /// - guard: an (arbitrarily complex) expression (usually an \ref exprt) of
  ///          Boolean type
  /// - code:  a code statement (usually a \ref codet)
  ///
  /// The meaning of an instruction node depends on the `type` field. Different
  /// kinds of instructions make use of the fields `guard` and `code` for
  /// different purposes.  We list below, using a mixture of pseudo code and
  /// plain English, the meaning of different kinds of instructions.
  /// We use `guard`, `code`, and `targets` to mean the value of the
  /// respective fields in this class:
  ///
  /// - GOTO:
  ///     goto `targets` if and only if `guard` is true.
  ///     More than one target is deprecated.  Its semantics was a
  ///     non-deterministic choice.
  /// - RETURN:
  ///     Set the value returned by `code` (which shall be either nil or an
  ///     instance of code_returnt) and then jump to the end of the function.
  ///     Many analysis tools remove these instructions before they start.
  /// - DECL:
  ///     Introduces a symbol denoted by the field `code` (an instance of
  ///     code_declt), the life-time of which is bounded by a corresponding DEAD
  ///     instruction.  Non-static symbols must be DECL'd before they are used.
  /// - DEAD:
  ///     Ends the life of the symbol denoted by the field `code`.
  ///     After a DEAD instruction the symbol must be DECL'd again before use.
  /// - FUNCTION_CALL:
  ///     Invoke the function denoted by field `code` (an instance of
  ///     code_function_callt).
  /// - ASSIGN:
  ///     Update the left-hand side of `code` (an instance of code_assignt) to
  ///     the value of the right-hand side.
  /// - OTHER:
  ///     Execute the `code` (an instance of codet of kind ID_fence, ID_printf,
  ///     ID_array_copy, ID_array_set, ID_input, ID_output, ...).
  /// - ASSUME:
  ///     This thread of execution waits for `guard` to evaluate to true.
  ///     Assume does not "retro-actively" affect the thread or any ASSERTs.
  /// - ASSERT:
  ///     Using ASSERT instructions is the one and only way to express
  ///     properties to be verified.  An assertion is true / safe if `guard`
  ///     is true in all possible executions, otherwise it is false / unsafe.
  ///     The status of the assertion does not affect execution in any way.
  /// - SKIP, LOCATION:
  ///     No-op.
  /// - ATOMIC_BEGIN, ATOMIC_END:
  ///     When a thread executes ATOMIC_BEGIN, no thread other will be able to
  ///     execute any instruction until the same thread executes ATOMIC_END.
  ///     Concurrency is not supported by all analysis tools.
  /// - END_FUNCTION:
  ///     Must occur as the last instruction of the list and nowhere else.
  /// - START_THREAD:
  ///     Create a new thread and run the code of this function starting from
  ///     targets[0]. Quite often the instruction pointed by targets[0] will be
  ///     just a FUNCTION_CALL, followed by an END_THREAD.
  ///     Concurrency is not supported by all analysis tools.
  /// - END_THREAD:
  ///     Terminate the calling thread.
  ///     Concurrency is not supported by all analysis tools.
  /// - THROW:
  ///     throw `exception1`, ..., `exceptionN`
  ///     where the list of exceptions is extracted from the `code` field
  ///     Many analysis tools remove these instructions before they start.
  /// - CATCH, when code.find(ID_exception_list) is non-empty:
  ///     Establishes that from here to the next occurrence of CATCH with an
  ///     empty list (see below) if
  ///     - `exception1` is thrown, then goto `target1`,
  ///     - ...
  ///     - `exceptionN` is thrown, then goto `targetN`.
  ///     The list of exceptions is obtained from the `code` field and the list
  ///     of targets from the `targets` field.
  /// - CATCH, when empty code.find(ID_exception_list) is empty:
  ///     clears all the catch clauses established as per the above in this
  ///     function?
  ///     Many analysis tools remove these instructions before they start.
  /// - INCOMPLETE GOTO:
  ///     goto for which the target is yet to be determined. The target set
  ///     shall be empty
  class instructiont final
  {
  public:
    codet code;

    /// The function this instruction belongs to
    irep_idt function;

    /// The location of the instruction in the source file
    source_locationt source_location;

    /// What kind of instruction?
    goto_program_instruction_typet type;

    /// Guard for gotos, assume, assert
    exprt guard;

    // The below will eventually become a single target only.
    /// The target for gotos and for start_thread nodes
    typedef std::list<instructiont>::iterator targett;
    typedef std::list<instructiont>::const_iterator const_targett;
    typedef std::list<targett> targetst;
    typedef std::list<const_targett> const_targetst;

    /// The list of successor instructions
    targetst targets;

    /// Returns the first (and only) successor for the usual case of a single
    /// target
    targett get_target() const
    {
      PRECONDITION(targets.size()==1);
      return targets.front();
    }

    /// Sets the first (and only) successor for the usual case of a single
    /// target
    void set_target(targett t)
    {
      targets.clear();
      targets.push_back(t);
    }

    bool has_target() const
    {
      return !targets.empty();
    }

    /// Goto target labels
    typedef std::list<irep_idt> labelst;
    labelst labels;

    // will go away
    std::set<targett> incoming_edges;

    /// Is this node a branch target?
    bool is_target() const
    { return target_number!=nil_target; }

    /// Clear the node
    void clear(goto_program_instruction_typet _type)
    {
      type=_type;
      targets.clear();
      guard=true_exprt();
      code.make_nil();
    }

    void make_return() { clear(RETURN); }
    void make_skip() { clear(SKIP); }
    void make_location(const source_locationt &l)
    { clear(LOCATION); source_location=l; }
    void make_throw() { clear(THROW); }
    void make_catch() { clear(CATCH); }
    void make_assertion(const exprt &g) { clear(ASSERT); guard=g; }
    void make_assumption(const exprt &g) { clear(ASSUME); guard=g; }
    void make_assignment() { clear(ASSIGN); }
    void make_other(const codet &_code) { clear(OTHER); code=_code; }
    void make_decl() { clear(DECL); }
    void make_dead() { clear(DEAD); }
    void make_atomic_begin() { clear(ATOMIC_BEGIN); }
    void make_atomic_end() { clear(ATOMIC_END); }
    void make_end_function() { clear(END_FUNCTION); }

    void make_incomplete_goto(const code_gotot &_code)
    {
      clear(INCOMPLETE_GOTO);
      code = _code;
    }

    void make_goto(targett _target)
    {
      clear(GOTO);
      targets.push_back(_target);
    }

    void make_goto(targett _target, const exprt &g)
    {
      make_goto(_target);
      guard=g;
    }

    void complete_goto(targett _target)
    {
      PRECONDITION(type == INCOMPLETE_GOTO);
      targets.push_back(_target);
      type = GOTO;
    }

    void make_assignment(const codet &_code)
    {
      clear(ASSIGN);
      code=_code;
    }

    void make_decl(const codet &_code)
    {
      clear(DECL);
      code=_code;
    }

    void make_function_call(const codet &_code)
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
    bool is_incomplete_goto() const
    {
      return type == INCOMPLETE_GOTO;
    }

    instructiont():
      instructiont(NO_INSTRUCTION_TYPE) // NOLINT(runtime/explicit)
    {
    }

    explicit instructiont(goto_program_instruction_typet _type):
      source_location(static_cast<const source_locationt &>(get_nil_irep())),
      type(_type),
      guard(true_exprt()),
      location_number(0),
      loop_number(0),
      target_number(nil_target)
    {
    }

    /// Swap two instructions
    void swap(instructiont &instruction)
    {
      using std::swap;
      swap(instruction.code, code);
      swap(instruction.source_location, source_location);
      swap(instruction.type, type);
      swap(instruction.guard, guard);
      swap(instruction.targets, targets);
      swap(instruction.function, function);
    }

    #if (defined _MSC_VER && _MSC_VER <= 1800)
    // Visual Studio <= 2013 does not support constexpr, making
    // numeric_limits::max() unviable for a static const member
    static const unsigned nil_target=
      static_cast<unsigned>(-1);
    #else
    /// Uniquely identify an invalid target or location
    static const unsigned nil_target=
      std::numeric_limits<unsigned>::max();
    #endif

    /// A globally unique number to identify a program location.
    /// It's guaranteed to be ordered in program order within
    /// one goto_program.
    unsigned location_number;

    /// Number unique per function to identify loops
    unsigned loop_number;

    /// A number to identify branch targets.
    /// This is \ref nil_target if it's not a target.
    unsigned target_number;

    /// Returns true if the instruction is a backwards branch.
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

    /// Syntactic equality: two instructiont are equal if they have the same
    /// type, code, guard, number of targets, and labels. All other members can
    /// only be evaluated in the context of a goto_programt (see
    /// goto_programt::equals).
    bool equals(const instructiont &other) const;
  };

  // Never try to change this to vector-we mutate the list while iterating
  typedef std::list<instructiont> instructionst;

  typedef instructionst::iterator targett;
  typedef instructionst::const_iterator const_targett;
  typedef std::list<targett> targetst;
  typedef std::list<const_targett> const_targetst;

  /// The list of instructions in the goto program
  instructionst instructions;

  /// Convert a const_targett to a targett - use with care and avoid
  /// whenever possible
  targett const_cast_target(const_targett t)
  {
    return instructions.erase(t, t);
  }

  /// Dummy for templates with possible const contexts
  const_targett const_cast_target(const_targett t) const
  {
    return t;
  }

  /// Get the id of the function that contains the instruction pointed-to by the
  /// given instruction iterator.
  ///
  /// \param l: instruction iterator
  /// \return id of the function that contains the pointed-to goto instruction
  static const irep_idt get_function_id(
    const_targett l)
  {
    // The field `function` of an instruction may not always contain the id of
    // the function it is currently in, due to goto program modifications such
    // as inlining. For example, if an instruction in a function `f` is inlined
    // into a function `g`, the instruction may, depending on the arguments to
    // the inliner, retain the original value of `f` in the function field.
    // However, instructions of type END_FUNCTION are never inlined into other
    // functions, hence they contain the id of the function they are in. Thus,
    // this function takes the END_FUNCTION instruction of the goto program and
    // returns the value of its function field.

    while(!l->is_end_function())
      ++l;

    return l->function;
  }

  /// Get the id of the function that contains the given goto program.
  ///
  /// \param p: the goto program
  /// \return id of the function that contains the goto program
  static const irep_idt get_function_id(
    const goto_programt &p)
  {
    PRECONDITION(!p.empty());

    return get_function_id(--p.instructions.end());
  }

  template <typename Target>
  std::list<Target> get_successors(Target target) const;

  void compute_incoming_edges();

  /// Insertion that preserves jumps to "target".
  void insert_before_swap(targett target)
  {
    PRECONDITION(target!=instructions.end());
    const auto next=std::next(target);
    instructions.insert(next, instructiont())->swap(*target);
  }

  /// Insertion that preserves jumps to "target".
  /// The instruction is destroyed.
  void insert_before_swap(targett target, instructiont &instruction)
  {
    insert_before_swap(target);
    target->swap(instruction);
  }

  /// Insertion that preserves jumps to "target".
  /// The program p is destroyed.
  void insert_before_swap(
    targett target,
    goto_programt &p)
  {
    PRECONDITION(target!=instructions.end());
    if(p.instructions.empty())
      return;
    insert_before_swap(target, p.instructions.front());
    auto next=std::next(target);
    p.instructions.erase(p.instructions.begin());
    instructions.splice(next, p.instructions);
  }

  /// Insertion before the instruction pointed-to by the given instruction
  /// iterator `target`.
  /// \return newly inserted location
  targett insert_before(const_targett target)
  {
    return instructions.insert(target, instructiont());
  }

  /// Insertion after the instruction pointed-to by the given instruction
  /// iterator `target`.
  /// \return newly inserted location
  targett insert_after(const_targett target)
  {
    return instructions.insert(std::next(target), instructiont());
  }

  /// Appends the given program `p` to `*this`. `p` is destroyed.
  void destructive_append(goto_programt &p)
  {
    instructions.splice(instructions.end(),
                        p.instructions);
    // BUG: The iterators to p-instructions are invalidated!
  }

  /// Inserts the given program `p` before `target`.
  /// The program `p` is destroyed.
  void destructive_insert(
    const_targett target,
    goto_programt &p)
  {
    instructions.splice(target, p.instructions);
    // BUG: The iterators to p-instructions are invalidated!
  }

  /// Adds an instruction at the end.
  /// \return The newly added instruction.
  targett add_instruction()
  {
    instructions.push_back(instructiont());
    return --instructions.end();
  }

  /// Adds an instruction of given type at the end.
  /// \return The newly added instruction.
  targett add_instruction(goto_program_instruction_typet type)
  {
    instructions.push_back(instructiont(type));
    return --instructions.end();
  }

  /// Output goto program to given stream
  std::ostream &output(
    const namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out) const;

  /// Output goto-program to given stream
  std::ostream &output(std::ostream &out) const
  {
    return output(namespacet(symbol_tablet()), "", out);
  }

  /// Output a single instruction
  std::ostream &output_instruction(
    const namespacet &ns,
    const irep_idt &identifier,
    std::ostream &out,
    const instructionst::value_type &it) const;

  /// Compute the target numbers
  void compute_target_numbers();

  /// Compute location numbers
  void compute_location_numbers(unsigned &nr)
  {
    for(auto &i : instructions)
    {
      INVARIANT(
        nr != std::numeric_limits<unsigned>::max(),
        "Too many location numbers assigned");
      i.location_number=nr++;
    }
  }

  /// Sets the `function` member of each instruction if not yet set
  /// Note that a goto program need not be a goto function and therefore,
  /// we cannot do this in update(), but only at the level of
  /// of goto_functionst where goto programs are guaranteed to be
  /// named functions.
  void update_instructions_function(const irep_idt &function_id)
  {
    for(auto &instruction : instructions)
    {
      if(instruction.function.empty())
      {
        instruction.function = function_id;
      }
    }
  }

  /// Compute location numbers
  void compute_location_numbers()
  {
    unsigned nr=0;
    compute_location_numbers(nr);
  }

  /// Compute loop numbers
  void compute_loop_numbers();

  /// Update all indices
  void update();

  /// Human-readable loop name
  static irep_idt loop_id(const instructiont &instruction)
  {
    return id2string(instruction.function)+"."+
           std::to_string(instruction.loop_number);
  }

  /// Is the program empty?
  bool empty() const
  {
    return instructions.empty();
  }

  /// Constructor
  goto_programt()
  {
  }

  ~goto_programt()
  {
  }

  /// Swap the goto program
  void swap(goto_programt &program)
  {
    program.instructions.swap(instructions);
  }

  /// Clear the goto program
  void clear()
  {
    instructions.clear();
  }

  /// Get an instruction iterator pointing to the END_FUNCTION instruction of
  /// the goto program
  targett get_end_function()
  {
    PRECONDITION(!instructions.empty());
    const auto end_function=std::prev(instructions.end());
    DATA_INVARIANT(end_function->is_end_function(),
                   "goto program ends on END_FUNCTION");
    return end_function;
  }

  /// Get an instruction iterator pointing to the END_FUNCTION instruction of
  /// the goto program
  const_targett get_end_function() const
  {
    PRECONDITION(!instructions.empty());
    const auto end_function=std::prev(instructions.end());
    DATA_INVARIANT(end_function->is_end_function(),
                   "goto program ends on END_FUNCTION");
    return end_function;
  }

  /// Copy a full goto program, preserving targets
  void copy_from(const goto_programt &src);

  /// Does the goto program have an assertion?
  bool has_assertion() const;

  typedef std::set<irep_idt> decl_identifierst;
  /// get the variables in decl statements
  void get_decl_identifiers(decl_identifierst &decl_identifiers) const;

  /// Syntactic equality: two goto_programt are equal if, and only if, they have
  /// the same number of instructions, each pair of instructions compares equal,
  /// and relative jumps have the same distance.
  bool equals(const goto_programt &other) const;
};

/// Get control-flow successors of a given instruction. The instruction is
/// represented by a pointer `target` of type `Target`. An instruction has
/// either 0, 1, or 2 successors (more than two successors is deprecated). For
/// example, an `ASSUME` instruction with the `guard` being a `false_exprt` has
/// 0 successors, and `ASSIGN` instruction has 1 successor, and a `GOTO`
/// instruction with the `guard` not being a `true_exprt` has 2 successors.
///
/// \tparam Target: type used to represent a pointer to an instruction in a goto
///   program
/// \param target: pointer to the instruction of which to get the successors of
/// \return List of control-flow successors of the pointed-to goto program
///   instruction
template <typename Target>
std::list<Target> goto_programt::get_successors(
  Target target) const
{
  if(target==instructions.end())
    return std::list<Target>();

  const auto next=std::next(target);

  const instructiont &i=*target;

  if(i.is_goto())
  {
    std::list<Target> successors(i.targets.begin(), i.targets.end());

    if(!i.guard.is_true() && next!=instructions.end())
      successors.push_back(next);

    return successors;
  }

  if(i.is_start_thread())
  {
    std::list<Target> successors(i.targets.begin(), i.targets.end());

    if(next!=instructions.end())
      successors.push_back(next);

    return successors;
  }

  if(i.is_end_thread())
  {
    // no successors
    return std::list<Target>();
  }

  if(i.is_throw())
  {
    // the successors are non-obvious
    return std::list<Target>();
  }

  if(i.is_assume())
  {
    return
      !i.guard.is_false() && next!=instructions.end() ?
      std::list<Target>{next} :
      std::list<Target>();
  }

  if(next!=instructions.end())
  {
    return std::list<Target>{next};
  }

  return std::list<Target>();
}

inline bool order_const_target(
  const goto_programt::const_targett i1,
  const goto_programt::const_targett i2)
{
  const goto_programt::instructiont &_i1=*i1;
  const goto_programt::instructiont &_i2=*i2;
  return &_i1<&_i2;
}

// NOLINTNEXTLINE(readability/identifiers)
struct const_target_hash
{
  std::size_t operator()(
    const goto_programt::const_targett t) const
  {
    using hash_typet = decltype(&(*t));
    return std::hash<hash_typet>{}(&(*t));
  }
};

/// Functor to check whether iterators from different collections point at the
/// same object.
struct pointee_address_equalt
{
  template <class A, class B>
  bool operator()(const A &a, const B &b) const
  {
    return &(*a) == &(*b);
  }
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
  const goto_programt::const_targett &i1,
  const goto_programt::const_targett &i2)
{
  return order_const_target(i1, i2);
}

inline bool operator<(
  const goto_programt::targett &i1,
  const goto_programt::targett &i2)
{
  return &(*i1)<&(*i2);
}

std::list<exprt> objects_read(const goto_programt::instructiont &);
std::list<exprt> objects_written(const goto_programt::instructiont &);

std::list<exprt> expressions_read(const goto_programt::instructiont &);
std::list<exprt> expressions_written(const goto_programt::instructiont &);

std::string as_string(
  const namespacet &ns,
  const goto_programt::instructiont &);

#endif // CPROVER_GOTO_PROGRAMS_GOTO_PROGRAM_H
