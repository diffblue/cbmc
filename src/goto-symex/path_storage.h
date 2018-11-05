/// \file path_storage.h
/// \brief Storage of symbolic execution paths to resume
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_STORAGE_H
#define CPROVER_GOTO_SYMEX_PATH_STORAGE_H

#include "goto_symex_state.h"
#include "symex_target_equation.h"

#include <goto-instrument/dispatch_loop_detector.h>

#include <goto-symex/goto_symex_state.h>

#include <util/cmdline.h>
#include <util/invariant.h>
#include <util/optional.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <memory>
#include <unordered_set>

/// \brief Storage for symbolic execution paths to be resumed later
///
/// This data structure supports saving partially-executed symbolic
/// execution \ref path_storaget::patht "paths" so that their execution can
/// be halted and resumed later. The choice of which path should be
/// resumed next is implemented by subtypes of this abstract class.
class path_storaget
{
public:
  /// \brief Information saved at a conditional goto to resume execution
  struct patht
  {
    symex_target_equationt equation;
    goto_symex_statet state;

    explicit patht(const symex_target_equationt &e, const goto_symex_statet &s)
      : equation(e), state(s, &equation)
    {
    }

    patht(const patht &other)
      : equation(other.equation), state(other.state, &equation)
    {
    }
  };

  /// \brief Data needed for path_storaget objects to make strategy decisions
  ///
  /// Different path exploration strategies need different information passed to
  /// them when they are constructed in order to decide which paths to resume
  /// next. Simple strategies (LIFO, FIFO etc.) don't need additional
  /// information, while more sophisticated strategies may require arguments
  /// from the command line, a reference to the goto-program, etc.
  ///
  /// This struct collects all this information in one place, so that when a new
  /// strategy needs a new parameter, it can simply be added to this struct. The
  /// alternative is to change the constructor for path_storaget and all of its
  /// subclasses every time we add a new strategy, which obfuscates the git
  /// history.
  struct strategy_contextt
  {
    const goto_functionst &goto_functions;
    const optionst &options;
    messaget &log;

    strategy_contextt(
      const goto_functionst &gf,
      const optionst &opts,
      messaget &log)
      : goto_functions(gf), options(opts), log(log)
    {
    }
  };

  path_storaget()
  {
  }

  virtual ~path_storaget() = default;

  /// \brief Reference to the next path to resume
  patht &peek()
  {
    PRECONDITION(!empty());
    return private_peek();
  }

  /// \brief Clear all saved paths
  ///
  /// This is typically used because we want to terminate symbolic execution
  /// early. It doesn't matter too much in terms of memory usage since CBMC
  /// typically exits soon after we do that, however it's nice to have tests
  /// that check that the worklist is always empty when symex finishes.
  virtual void clear() = 0;

  /// \brief Add paths to resume to the storage
  ///
  /// Symbolic execution is suspended when we reach a conditional goto
  /// instruction with two successors. Thus, we always add a pair of paths to
  /// the path storage.
  ///
  /// \param next_instruction the instruction following the goto instruction
  /// \param jump_target the target instruction of the goto instruction
  virtual void
  push(const patht &next_instruction, const patht &jump_target) = 0;

  /// \brief Remove the next path to resume from the storage
  void pop()
  {
    PRECONDITION(!empty());
    private_pop();
  }

  /// \brief How many paths does this storage contain?
  virtual std::size_t size() const = 0;

  /// \brief Is this storage empty?
  bool empty() const
  {
    return size() == 0;
  };

  /// \brief Should symex notify this path_storage on each executed instruction?
  ///
  /// If this method returns `false`, there is no need for goto_symext to invoke
  /// path_storaget::notify_next_instruction() whenever it is about to execute a
  /// new instruction. This is to avoid needlessly calling an empty function in
  /// the middle of the tight symex loop; goto_symext can initialize a `const`
  /// flag with the return value of this function, and look up the value of the
  /// flag while symexing.
  virtual inline bool wants_instruction_callback() const
  {
    return false;
  }

  /// \brief Notify that an instruction is about to be symbolically executed
  ///
  /// goto_symext can use this method to inform this path_storaget that an
  /// instruction is about to be symbolically executed. Derived types of
  /// path_storaget can use this to dynamically modify their path-resuming
  /// strategy during symbolic execution. This method will not necessarily be
  /// called on this path_storaget if this implementation of
  /// path_storaget::wants_instruction_callback() returns `false`.
  virtual inline void notify_next_instruction(
    const goto_programt::const_targett &,
    goto_symex_statet &)
  {
  }

private:
  // Derived classes should override these methods, allowing the base class to
  // enforce preconditions.
  virtual patht &private_peek() = 0;
  virtual void private_pop() = 0;
};

/// \brief LIFO save queue: depth-first search, try to finish paths
class path_lifot : public path_storaget
{
public:
  explicit path_lifot() : path_storaget()
  {
  }

  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;

protected:
  std::list<path_storaget::patht>::iterator last_peeked;
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief FIFO save queue: paths are resumed in the order that they were saved
class path_fifot : public path_storaget
{
public:
  explicit path_fifot() : path_storaget()
  {
  }

  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;

protected:
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief Save queue for each case of a dispatch loop
class path_dispatch_loopt : public path_storaget
{
public:
  explicit path_dispatch_loopt(const dispatch_loop_detectort &, messaget &log);

  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;
  bool inline wants_instruction_callback() const override
  {
    return true;
  }
  inline void notify_next_instruction(
    const goto_programt::const_targett &,
    goto_symex_statet &) override;

protected:
  class queue_pointert
  {
  protected:
    bool initialized;

  public:
    goto_programt::const_targett originating_branch;
    goto_programt::const_targett branch_target;
    queue_pointert(
      const goto_programt::const_targett &ob,
      const goto_programt::const_targett &bt)
      : initialized(false), originating_branch(ob), branch_target(bt)
    {
    }

    bool is_initialized() const
    {
      return initialized;
    }
    void initialize()
    {
      INVARIANT(!initialized, "Tried to initialize a queue_pointert twice");
      initialized = true;
    }
    bool operator==(const queue_pointert &other) const
    {
      return initialized == other.is_initialized() &&
             originating_branch->location_number ==
               other.originating_branch->location_number &&
             branch_target->location_number ==
               other.branch_target->location_number;
    }
    bool operator!=(const queue_pointert &other) const
    {
      return !(*this == other);
    }
    bool operator<(const queue_pointert &other) const
    {
      return std::tie(initialized, originating_branch, branch_target) <
             std::tie(
               other.initialized,
               other.originating_branch,
               other.branch_target);
    }
    std::string to_string() const;
  };

  const dispatch_loop_detectort::dispatch_loopt dispatch_loop;
  std::list<patht> paths;
  std::list<patht>::iterator last_peeked;
  messaget &log;
  /// \brief The last instruction in the program
  const goto_programt::const_targett last_program_instruction;
  const goto_programt::const_targett init_last_program_instruction() const;

  /// \brief Cache of location numbers in targets in dispatch_loop.cases()
  const std::unordered_set<unsigned> case_locations;
  const std::unordered_set<unsigned> init_case_locations() const;

  typedef std::map<queue_pointert, std::list<patht>> queuest;
  queuest queues;
  std::list<queue_pointert> qq;

  std::map<queue_pointert, goto_programt::const_targett> targets_cache;
  const std::map<queue_pointert, goto_programt::const_targett>
  init_targets_cache() const;

  const goto_programt::const_targett jump_back_instruction;

  bool look_out_for_cases;
  bool should_adjust_qq;

  const queue_pointert invalid;
  const queue_pointert init_invalid() const;
  queue_pointert old_qq_head;

  void print_qq(const std::string &) const;
  void adjust_queue_queues();
  queuest::iterator find_front_queue()
  {
    queuest::iterator ret = queues.find(qq.front());
    INVARIANT(
      ret != queues.end(),
      "There should be a queue headed by the queue pointer " +
        qq.front().to_string());
    return ret;
  }

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief Dummy class for clients who will not use path exploration
class degenerate_path_storaget : public path_storaget
{
public:
  explicit degenerate_path_storaget() : path_storaget()
  {
  }

  void push(const patht &, const patht &) override
  {
    INVARIANT(false, "Cannot push to a degenerate_path_storaget");
  }
  std::size_t size() const override
  {
    INVARIANT(false, "Cannot take the size of a degenerate_path_storaget");
  }
  void clear() override
  {
    INVARIANT(false, "Cannot clear a degenerate_path_storaget");
  }

private:
  patht &private_peek() override
  {
    INVARIANT(false, "Cannot peek at a degenerate_path_storaget");
  }
  void private_pop() override
  {
    INVARIANT(false, "Cannot pop a degenerate_path_storaget");
  }
};

/// \brief Factory and information for path_storaget
class path_strategy_choosert
{
public:
  path_strategy_choosert();

  /// \brief suitable for displaying as a front-end help message
  std::string show_strategies() const;

  /// \brief is there a factory constructor for the named strategy?
  bool is_valid_strategy(const std::string strategy) const
  {
    return strategies.find(strategy) != strategies.end();
  }

  /// \brief Factory for a path_storaget
  ///
  /// Ensure that path_strategy_choosert::is_valid_strategy() returns true for a
  /// particular string before calling this function on that string.
  std::unique_ptr<path_storaget> get(
    const std::string strategy,
    const path_storaget::strategy_contextt &ctx) const
  {
    auto found = strategies.find(strategy);
    INVARIANT(
      found != strategies.end(), "Unknown strategy '" + strategy + "'.");
    return found->second.second(ctx);
  }

  /// \brief add `paths` and `exploration-strategy` option, suitable to be
  /// invoked from front-ends.
  void
  set_path_strategy_options(const cmdlinet &, optionst &, messaget &) const;

  static bool start_symex_with_path_exploration(const std::string &strategy)
  {
    INVARIANT(
      strategy != "",
      "This function should only be called if the strategy is non-empty");
    if(strategy == "dispatch")
      return false;
    return true;
  }

protected:
  std::string default_strategy() const
  {
    return "lifo";
  }

  /// Map from the name of a strategy (to be supplied on the command line), to
  /// the help text for that strategy and a factory thunk returning a pointer to
  /// a derived class of path_storaget that implements that strategy.
  std::map<
    const std::string,
    std::pair<
      const std::string,
      const std::function<std::unique_ptr<path_storaget>(
        const path_storaget::strategy_contextt &ctx)>>>
    strategies;
};

#endif /* CPROVER_GOTO_SYMEX_PATH_STORAGE_H */
