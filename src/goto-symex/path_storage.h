/// \file path_storage.h
/// \brief Storage of symbolic execution paths to resume
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_STORAGE_H
#define CPROVER_GOTO_SYMEX_PATH_STORAGE_H

#include <util/cmdline.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/options.h>

#include <analyses/dirty.h>
#include <analyses/local_safe_pointers.h>

#include <memory>

#include "goto_symex_state.h"
#include "symex_target_equation.h"

/// Functor generating fresh nondet symbols
class symex_nondet_generatort
{
public:
  nondet_symbol_exprt operator()(typet type, source_locationt location);

private:
  std::size_t nondet_count = 0;
};

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

    patht(const symex_target_equationt &e, const goto_symex_statet &s)
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

  /// \brief Add a path to resume to the storage
  virtual void push(const patht &) = 0;

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

  /// Counter for nondet objects, which require unique names
  symex_nondet_generatort build_symex_nondet;

  /// Map function identifiers to \ref local_safe_pointerst instances. This is
  /// to identify derferences that are guaranteed to be safe in a given
  /// execution context, thus helping to avoid symex to follow spurious
  /// error-handling paths.
  std::unordered_map<irep_idt, local_safe_pointerst> safe_pointers;

  /// Provide a unique L1 index for a given \p id, starting from
  /// \p minimum_index.
  std::size_t get_unique_l1_index(const irep_idt &id, std::size_t minimum_index)
  {
    return get_unique_index(l1_indices, id, minimum_index);
  }

  std::size_t get_unique_l2_index(const irep_idt &id)
  {
    return get_unique_index(l2_indices, id, 1);
  }

  /// Local variables are considered 'dirty' if they've had an address taken and
  /// therefore may be referred to by a pointer.
  incremental_dirtyt dirty;

  /// Generates a loop analysis for the instructions in goto_programt and
  /// keys it against function ID.
  void add_function_loops(const irep_idt &identifier, const goto_programt &body)
  {
    auto loop_iter = loop_analysis_map.find(identifier);
    if(loop_iter == loop_analysis_map.end())
    {
      loop_analysis_map[identifier] =
        std::make_shared<lexical_loopst>(lexical_loopst(body));
    }
  }

  inline std::shared_ptr<lexical_loopst>
  get_loop_analysis(const irep_idt &function_id)
  {
    return loop_analysis_map.at(function_id);
  }

private:
  std::unordered_map<irep_idt, std::shared_ptr<lexical_loopst>>
    loop_analysis_map;

  // Derived classes should override these methods, allowing the base class to
  // enforce preconditions.
  virtual patht &private_peek() = 0;
  virtual void private_pop() = 0;

  typedef std::unordered_map<irep_idt, std::size_t> name_index_mapt;

  std::size_t get_unique_index(
    name_index_mapt &unique_index_map,
    const irep_idt &id,
    std::size_t minimum_index)
  {
    auto entry = unique_index_map.emplace(id, minimum_index);

    if(!entry.second)
      entry.first->second = std::max(entry.first->second + 1, minimum_index);

    return entry.first->second;
  }

  /// Storage used by \ref get_unique_index.
  name_index_mapt l1_indices;
  name_index_mapt l2_indices;
};

/// \brief LIFO save queue: depth-first search, try to finish paths
class path_lifot : public path_storaget
{
public:
  void push(const patht &) override;
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
  void push(const patht &) override;
  std::size_t size() const override;
  void clear() override;

protected:
  std::list<patht> paths;

private:
  patht &private_peek() override;
  void private_pop() override;
};

/// \brief suitable for displaying as a front-end help message
std::string show_path_strategies();

/// \brief is there a factory constructor for the named strategy?
bool is_valid_path_strategy(const std::string strategy);

/// Ensure that is_valid_strategy() returns true for a
/// particular string before calling this function on that string.
std::unique_ptr<path_storaget> get_path_strategy(const std::string strategy);

/// \brief add `paths` and `exploration-strategy` option, suitable to be
/// invoked from front-ends.
void parse_path_strategy_options(
  const cmdlinet &,
  optionst &,
  message_handlert &);

#endif /* CPROVER_GOTO_SYMEX_PATH_STORAGE_H */
