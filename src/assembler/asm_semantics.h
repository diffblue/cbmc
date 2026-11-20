/*******************************************************************\

Module: Inline assembly: instruction semantics

Author: Michael Tautschnig

\*******************************************************************/

/// \file
/// The interface between the lowering of inline assembly statements and the
/// architecture-specific instruction semantics. See
/// doc/architectural/inline-assembly.md for the design.

#ifndef CPROVER_ASSEMBLER_ASM_SEMANTICS_H
#define CPROVER_ASSEMBLER_ASM_SEMANTICS_H

#include <util/namespace.h>
#include <util/source_location.h>
#include <util/std_expr.h>

#include <goto-programs/goto_program.h>

#include "asm_operands.h" // IWYU pragma: export
#include "asm_template.h" // IWYU pragma: export

#include <list>
#include <map>
#include <memory>
#include <optional>
#include <set>

class symbol_table_baset;
class asm_semanticst;

/// State of the instruction semantics for one statement, for semantics that
/// depend on the statement as a whole (see \ref asm_semanticst::make_state)
class asm_semantics_statet
{
public:
  virtual ~asm_semantics_statet() = default;
};

/// The state of lowering one inline assembly statement: the goto code being
/// built, the storage of register operands, hardware registers and flags, and
/// labels. Architecture semantics use it to emit the effect of instructions.
class asm_lowering_contextt
{
public:
  asm_lowering_contextt(
    symbol_table_baset &symbol_table,
    const irep_idt &function_id,
    const source_locationt &source_location,
    asm_operandst &operands,
    const asm_semanticst &semantics);

  const namespacet ns;
  asm_operandst &operands;
  const asm_semanticst &semantics;

  const source_locationt &source_location() const
  {
    return location;
  }

  /// A description of why lowering failed, for diagnostics
  std::string failure;

  /// Record a failure reason and return false, for use in `return
  /// ctx.fail(...)`.
  bool fail(const std::string &reason)
  {
    if(failure.empty())
      failure = reason;
    return false;
  }

  /// \name Storage
  /// \{

  /// A fresh block-local variable, declared (with a non-deterministic value)
  /// at the start of the statement.
  symbol_exprt temporary(const typet &type, const std::string &suffix);

  /// A hardware register, identified by its canonical (full-width) name. Its
  /// storage is block-local: the value is non-deterministic unless an operand
  /// with a fixed-register constraint initialises it.
  symbol_exprt hardware_register(const std::string &canonical);

  /// A condition flag (Boolean), non-deterministic initially
  symbol_exprt flag(const std::string &name);

  /// The block-local storage of register operand \p index, a bit-vector of
  /// the architecture's register width
  const symbol_exprt &operand_storage(std::size_t index) const;

  /// A pointer to the start of memory operand \p index, evaluated before the
  /// first instruction
  const symbol_exprt &operand_address(std::size_t index) const;

  /// The value of immediate operand \p index
  const exprt &operand_immediate(std::size_t index) const;

  /// The width, in bits, of the C expression of operand \p index; 0 if it is
  /// not a scalar
  std::size_t operand_width(std::size_t index) const;

  /// \}

  /// \name Code
  /// \{
  void assign(const exprt &lhs, const exprt &rhs);
  void assume(const exprt &condition);
  void add(goto_programt::instructiont instruction);

  /// A memory barrier; \p cumulative for barriers that order accesses of all
  /// observers (ARM `dmb`, Power `sync`)
  void fence(bool ww, bool rr, bool rw, bool wr, bool cumulative);

  /// Make the instruction being lowered an atomic section
  void mark_atomic()
  {
    atomic = true;
  }

  /// Start lowering an instruction: code emitted until \ref end_instruction
  /// belongs to it.
  void begin_instruction();

  /// Finish lowering an instruction: if it was marked atomic (see
  /// \ref mark_atomic), wrap its code in an atomic section, and likewise
  /// for an exclusive access region that the instruction ends (see
  /// \ref end_exclusive).
  void end_instruction();

  /// \name Load-exclusive/store-exclusive sequences
  /// A load-exclusive (AArch64 `ldxr`, AArch32 `ldrex`) followed, in the same
  /// statement and without other memory accesses, branches, or labels in
  /// between, by a store-exclusive is modeled as an atomic section that
  /// spans both instructions. The store-exclusive succeeds
  /// nondeterministically (the architecture permits spurious failures).
  /// \{

  /// Start an exclusive access region at the current instruction (a
  /// load-exclusive).
  void begin_exclusive();

  /// \return True iff an exclusive access region is open.
  bool exclusive_open() const
  {
    return exclusive_start.has_value();
  }

  /// End the open exclusive access region with the current instruction (a
  /// store-exclusive), which makes the region an atomic section.
  void end_exclusive();

  /// The exclusive monitor is cleared (by `clrex`, or by a
  /// store-exclusive): a later store-exclusive in this statement fails.
  void clear_exclusive();

  /// \return True iff the exclusive monitor is known to be cleared.
  bool exclusive_cleared() const
  {
    return monitor_cleared;
  }

  /// Record that the code lowered for the current instruction is a
  /// store-exclusive that succeeds iff \p success holds.
  void record_store_exclusive(const symbol_exprt &success);

  /// Lower a backward branch to \p target taken iff \p condition holds.
  /// When the branch closes the retry loop of a store-exclusive, as in
  /// `1: ldxr ...; stxr w1, ...; cbnz w1, 1b`, symbolic execution would have
  /// to unwind the loop, which may retry arbitrarily often. Instead, if
  /// - \p condition implies that the store-exclusive recorded last
  ///   (\ref record_store_exclusive) failed, and
  /// - the code from \p target to the branch is restartable: it has no
  ///   other labels or branches, no calls, no writes to memory other than
  ///   the store-exclusive's, writes the registers and temporaries it writes
  ///   unconditionally, and does not read any of them before writing it,
  /// then an attempt that takes the branch has no effect, and the
  /// executions that retry reach the same states as one that succeeds at
  /// the last attempt. The branch is then replaced by the assumption that it
  /// is not taken. Otherwise, it is lowered as by \ref branch.
  bool retry_branch(const asm_tokent &target, const exprt &condition);
  /// \}

  /// A call to a library function taking `void *` arguments
  void call(const irep_idt &function, const exprt::operandst &arguments);

  /// The functions called via call(), which the caller has to make known
  std::vector<irep_idt> called_functions;

  /// A non-deterministic value of type \p type
  exprt nondet(const typet &type) const;

  /// A memory location of \p width bits at \p address (any pointer or
  /// integer type), as an lvalue of type unsignedbv(width). Records a failure
  /// if \p address may depend on a value that is not modeled (see
  /// \ref depends_on_unknown).
  exprt memory(const exprt &address, std::size_t width);
  /// \}

  /// \name Values that are not modeled
  /// Some values are modeled as nondeterministic: those of hardware registers
  /// that the statement does not initialise (which may hold a register
  /// variable, `register int *p asm("r1")`, that CBMC does not track), of
  /// system registers, and of output operands that are read before they are
  /// written. This over-approximates the value, but CBMC cannot relate a
  /// nondeterministic address to the objects it may point to, so memory
  /// accessed at such an address would not change any object. Hence such
  /// accesses make the lowering fail.
  /// \{

  /// \return True iff \p expr may depend on a value that is not modeled at
  ///   the current position of the statement
  bool depends_on_unknown(const exprt &expr) const;
  /// \}

  /// \name Control flow
  /// \{

  /// Define the local label \p name at the current position
  void define_label(const std::string &name);

  /// Jump to the target named by \p target (a LOCAL_LABEL, C_LABEL, or
  /// IDENTIFIER naming a label of this statement) if \p condition holds.
  /// \return false if the target is not understood
  bool branch(const asm_tokent &target, const exprt &condition);

  /// Start a region of code that only executes if \p condition holds, for
  /// conditionally executed instructions; end it with end_conditional
  goto_programt::targett begin_conditional(const exprt &condition);
  void end_conditional(goto_programt::targett begin);
  /// \}

  /// Initialise operand storage; must be called before lowering
  /// instructions.
  /// \return false if an operand cannot be modelled
  /// Initialise operand storage; must be called before lowering
  /// instructions.
  /// \param instructions: the instructions of the statement, used to decide
  ///   whether an input operand is read above its natural width
  /// \return false if an operand cannot be modelled
  bool prepare(const std::vector<asm_instructiont> &instructions);

  /// Assemble the complete lowering of the statement into \p dest: prologue
  /// (inputs), instructions, epilogue (outputs).
  /// \return false if a branch target could not be resolved
  bool finish(goto_programt &dest);

  /// Symbol holding the label chosen by `asm goto` (0 for fall-through, k+1
  /// for label k), or nil if the statement has no labels
  exprt goto_target;

  /// The state of the semantics for this statement, created by \ref prepare
  /// (see \ref asm_semanticst::make_state); may be nullptr
  std::unique_ptr<asm_semantics_statet> semantics_state;

  /// \name Conversion between C values and bit-vectors
  /// \{

  /// \p value (a C scalar) as unsignedbv(width), truncating or
  /// zero-extending; nil if \p value is not a scalar
  exprt to_bits(const exprt &value, std::size_t width) const;

  /// \p bits (a bit-vector) as a value of C type \p type
  exprt from_bits(const exprt &bits, const typet &type) const;

  /// The width in bits of the scalar type \p type; 0 if not a scalar
  std::size_t width(const typet &type) const;
  /// \}

protected:
  symbol_table_baset &symbol_table;
  irep_idt function_id;
  irep_idt mode;
  /// the location of the statement, for code evaluating C expressions
  source_locationt statement_location;
  /// the location of the statement, with the checks for undefined behaviour of
  /// C disabled, for the code modeling the instructions
  source_locationt location;

  goto_programt prologue, body, epilogue;
  std::list<symbol_exprt> declared;
  bool atomic = false;
  /// the last instruction of body before the current instruction, if any
  std::optional<goto_programt::targett> instruction_start;
  /// for an open exclusive access region: the last instruction of body
  /// before the load-exclusive, if any
  std::optional<std::optional<goto_programt::targett>> exclusive_start;
  /// whether the current instruction ends an exclusive access region
  bool exclusive_ends = false;
  /// where the exclusive access region ended by the current instruction
  /// started
  std::optional<goto_programt::targett> ended_exclusive_start;
  bool monitor_cleared = false;
  /// the canonical names of the hardware registers that are written
  std::set<std::string> written_registers;

  /// the code of the store-exclusive recorded last
  struct store_exclusivet
  {
    goto_programt::targett first, last;
    symbol_exprt success;
  };
  std::optional<store_exclusivet> last_store_exclusive;
  /// the instructions of branches (\ref branch) and of label definitions
  std::set<const goto_programt::instructiont *> branch_instructions,
    label_instructions;
  /// whether the code after \p label is restartable (see
  /// \ref retry_branch)
  bool restartable(goto_programt::targett label) const;
  /// whether \p condition, at the end of the code lowered so far, implies
  /// that the store-exclusive recorded last failed
  bool implies_store_failure(const exprt &condition) const;

  /// The symbols that may hold a value that is not modeled at the current
  /// position, and \ref unknown_memory if memory may hold such a value
  std::set<irep_idt> unknown;
  /// all symbols that held a value that is not modeled at some position
  /// lowered so far, a superset of \ref unknown at any of these positions
  std::set<irep_idt> ever_unknown;
  /// \ref unknown at each label definition
  std::map<const goto_programt::instructiont *, std::set<irep_idt>>
    unknown_at_label;
  /// the number of conditional regions (\ref begin_conditional) that are
  /// open: an assignment in one of them does not make its target known
  std::size_t conditional_depth = 0;
  /// stands for memory in \ref unknown
  static const irep_idt unknown_memory;

  void mark_unknown(const irep_idt &identifier);

  /// Fail if a branch to \p target with \ref unknown being \p at_branch
  /// would make a value unknown at \p target that was taken as known when
  /// lowering the code at \p target.
  bool check_unknown_at_target(
    goto_programt::const_targett target,
    const std::set<irep_idt> &at_branch);

  std::map<std::string, symbol_exprt> registers;
  std::map<std::string, symbol_exprt> flags;
  std::map<std::size_t, symbol_exprt> storage;
  std::map<std::size_t, symbol_exprt> addresses;
  std::map<std::size_t, exprt> immediates;

  /// named and numeric labels: current definition
  std::map<std::string, goto_programt::targett> label_definitions;
  /// all definitions of numeric labels, in order
  std::map<std::string, std::vector<goto_programt::targett>> numeric_labels;
  struct pending_brancht
  {
    goto_programt::targett instruction;
    std::string label;
    /// for numeric labels: the number of definitions of the label that
    /// preceded the branch
    std::size_t definitions_before;
    bool forward;
    bool numeric;
    /// \ref unknown at the branch
    std::set<irep_idt> unknown;
  };
  std::vector<pending_brancht> pending;
  goto_programt::targett exit_label;
  std::vector<goto_programt::targett> exit_branches;
};

/// The instruction semantics of one architecture
class asm_semanticst
{
public:
  virtual ~asm_semanticst() = default;

  /// A name for diagnostics, e.g. "x86"
  virtual std::string name() const = 0;

  /// The lexical conventions of templates
  virtual const asm_syntaxt &syntax() const = 0;

  /// The width of general-purpose registers in bits
  virtual std::size_t register_width() const = 0;

  /// \return The canonical (full-width) name of the register named \p name
  ///   (with or without a leading `%`), as used by
  ///   \ref asm_lowering_contextt::hardware_register, or the empty string if
  ///   \p name is not a general-purpose register.
  virtual std::string canonical_register(const std::string &name) const
  {
    return {};
  }

  /// \return true if a `%`-reference with the given \p modifier reads an
  ///   operand of natural width \p natural_width bits at a wider view, so that
  ///   bits above \p natural_width are observed. For an input operand narrower
  ///   than the register, those bits are unspecified (except where the
  ///   architecture defines them), so when any reference to it widens, its
  ///   register is initialised with non-deterministic upper bits rather than
  ///   zero-extended. When none do, zero-extension is exact and keeps the
  ///   register a constant when the input is one.
  virtual bool
  reference_widens(const std::string &modifier, std::size_t natural_width) const
  {
    // Conservative default (used only where instruction semantics are absent):
    // a bare reference reads the natural width, a modifier may select a wider
    // view.
    return !modifier.empty();
  }

  /// How a constraint letter is interpreted
  enum class constraint_classt
  {
    UNKNOWN,
    REGISTER,
    MEMORY,
    IMMEDIATE,
    /// register, memory, or immediate
    ANY,
    /// a constraint letter that names one register; the name is returned in
    /// the output parameter
    FIXED_REGISTER,
    /// a letter that is not about the operand location (modifiers like `%`)
    IGNORE
  };

  /// Classify an architecture-specific constraint letter.
  /// \param constraint: the constraint string
  /// \param pos: position of the letter in \p constraint; may be advanced
  ///   for multi-letter constraints
  /// \param [out] fixed_register: the register named by the letter
  virtual constraint_classt classify_constraint(
    const std::string &constraint,
    std::size_t &pos,
    std::string &fixed_register) const;

  /// \return true if \p condition is valid in an `=@cc<condition>` output
  virtual bool is_flag_output_condition(const std::string &condition) const
  {
    return false;
  }

  /// The value of the condition \p condition on the current flags, for
  /// `=@cc` outputs; nil if not understood
  virtual exprt
  condition(const std::string &condition, asm_lowering_contextt &ctx) const
  {
    return nil_exprt{};
  }

  /// Lower \p instruction, appending its effect to \p ctx.
  /// \return false if the instruction is not understood; the caller then
  ///   approximates the whole statement
  virtual bool lower(
    const asm_instructiont &instruction,
    asm_lowering_contextt &ctx) const = 0;

  /// \return The state of the semantics for a statement with \p
  ///   instructions, available to \ref lower as
  ///   \ref asm_lowering_contextt::semantics_state, or nullptr if the
  ///   semantics need none
  virtual std::unique_ptr<asm_semantics_statet>
  make_state(const std::vector<asm_instructiont> &instructions) const
  {
    return nullptr;
  }
};

/// \return The instruction semantics for architecture \p arch (as in
///   `config.ansi_c.arch`), or nullptr if there are none.
std::unique_ptr<asm_semanticst> make_asm_semantics(const irep_idt &arch);

#endif // CPROVER_ASSEMBLER_ASM_SEMANTICS_H
