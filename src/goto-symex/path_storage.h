/// \file path_storage.h
/// \brief Storage of symbolic execution paths to resume
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_GOTO_SYMEX_PATH_STORAGE_H
#define CPROVER_GOTO_SYMEX_PATH_STORAGE_H

#include "goto_symex_state.h"
#include "symex_target_equation.h"

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
  /// \brief Derived types of path_storaget
  enum class disciplinet
  {
    /// path_fifot
    FIFO
  };

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

  /// \brief Factory method for building a subtype of path_storaget
  static std::unique_ptr<path_storaget> make(disciplinet discipline);
  virtual ~path_storaget() = default;

  /// \brief Reference to the next path to resume
  virtual patht &peek() = 0;

  /// \brief Add a path to resume to the storage
  virtual void push(const patht &bp) = 0;

  /// \brief Remove the next path to resume from the storage
  virtual void pop() = 0;

  /// \brief How many paths does this storage contain?
  virtual std::size_t size() const = 0;

  /// \brief Is this storage empty?
  bool empty() const
  {
    return size() == 0;
  };
};

/// \brief FIFO save queue: paths are resumed in the order that they were saved
class path_fifot : public path_storaget
{
public:
  patht &peek() override;
  void push(const patht &bp) override;
  void pop() override;
  std::size_t size() const override;

protected:
  std::list<patht> paths;
};

#endif /* CPROVER_GOTO_SYMEX_PATH_STORAGE_H */
