/// \file path_storage.h
/// \brief Storage of symbolic execution paths to resume
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_STORAGE_H
#define CPROVER_GOTO_SYMEX_PATH_STORAGE_H

#include "goto_symex_state.h"
#include "symex_target_equation.h"

#include <util/options.h>
#include <util/cmdline.h>
#include <util/ui_message.h>
#include <util/invariant.h>

#include <memory>

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

    explicit patht(const patht &other)
      : equation(other.equation), state(other.state, &equation)
    {
    }
  };

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
  /// \param next_instruction: the instruction following the goto instruction
  /// \param jump_target: the target instruction of the goto instruction
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
  void push(const patht &, const patht &) override;
  std::size_t size() const override;
  void clear() override;

protected:
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
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
  std::unique_ptr<path_storaget> get(const std::string strategy) const
  {
    auto found = strategies.find(strategy);
    INVARIANT(
      found != strategies.end(), "Unknown strategy '" + strategy + "'.");
    return found->second.second();
  }

  /// \brief add `paths` and `exploration-strategy` option, suitable to be
  /// invoked from front-ends.
  void
  set_path_strategy_options(const cmdlinet &, optionst &, messaget &) const;

protected:
  std::string default_strategy() const
  {
    return "lifo";
  }

  /// Map from the name of a strategy (to be supplied on the command line), to
  /// the help text for that strategy and a factory thunk returning a pointer to
  /// a derived class of path_storaget that implements that strategy.
  std::map<const std::string,
           std::pair<const std::string,
                     const std::function<std::unique_ptr<path_storaget>()>>>
    strategies;
};

#endif /* CPROVER_GOTO_SYMEX_PATH_STORAGE_H */
