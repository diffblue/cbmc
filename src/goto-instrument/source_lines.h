/*******************************************************************\

Module: Source Lines

Author: Mark R. Tuttle

\*******************************************************************/

/// \file
/// Set of source code lines contributing to a basic block

/// Existing code coverage instrumentation represents the lines of
/// source code contributing to a basic block as a set of line numbers
/// assuming the lines all come from the same source file.  In fact,
/// the lines contributing to a basic block can come from multiple
/// files due to function inlining, header file inclusion, etc.  This
/// module represents a line of source code with the file, the
/// function, and the line number of the line.

#ifndef CPROVER_GOTO_INSTRUMENT_SOURCE_LINES_H
#define CPROVER_GOTO_INSTRUMENT_SOURCE_LINES_H

#include <util/irep.h>
#include <util/mp_arith.h>

#include <map>
#include <set>
#include <string>

class source_locationt;

class source_linest
{
public:
  /// Constructors
  source_linest() = default;
  explicit source_linest(const source_locationt &loc)
  {
    insert(loc);
  }

  /// Insert a line (a source location) into the set of lines.
  /// \param loc: A source location
  void insert(const source_locationt &loc);

  /// Construct a string representing the set of lines
  ///
  /// \return The set of lines represented as string of the form
  ///   set1;set2;set3 where each set is a string of the form
  ///   file:function:n1,n2,n3,n4 where n1, n2, n3, n4 are line
  ///   numbers (or ranges thereof) from the given function in the given file
  ///   listed in ascending order.
  std::string to_string() const;

  /// Construct an irept representing the set of lines
  ///
  /// \return The set of lines represented as an irept where each file is a
  ///   is a named_sub, each function is a named_sub therein, and line numbers
  ///   (or ranges thereof) are the string value.
  irept to_irep() const;

private:
  /// A set of lines from a single function
  using linest = std::set<mp_integer>;
  /// A set of lines from multiple function
  using function_linest = std::map<std::string, linest>;
  /// A set of lines from multiple files
  using block_linest = std::map<std::string, function_linest>;

  block_linest block_lines;
};

#endif // CPROVER_GOTO_INSTRUMENT_SOURCE_LINES_H
