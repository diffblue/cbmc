/*******************************************************************\

Module: Symbol Analyzer

Author: Malte Mues <mail.mues@gmail.com>
        Daniel Poetzl

\*******************************************************************/

/// \file
/// High-level interface to gdb

#ifndef CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
#define CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H

#include <map>
#include <string>

#include "gdb_api.h"

#include <ansi-c/expr2c_class.h>

#include <util/message.h>
#include <util/namespace.h>
#include <util/pointer_expr.h>
#include <util/std_code.h>
#include <util/symbol_table.h>

#include <goto-programs/allocate_objects.h>

class gdb_apit;
class exprt;
class source_locationt;

/// Interface for extracting values from GDB (building on \ref gdb_apit)
class gdb_value_extractort
{
public:
  gdb_value_extractort(
    const symbol_tablet &symbol_table,
    const std::vector<std::string> &args);

  /// For each input symbol in \p symbols: map its value address to its
  ///   \ref symbol_exprt (via the `values` map) and then call
  ///   \ref analyze_symbol on it.
  /// \param symbols: names of symbols to be analysed
  void analyze_symbols(const std::vector<irep_idt> &symbols);

  /// Get memory snapshot as C code
  /// \return converted block of code with the collected assignments
  std::string get_snapshot_as_c_code();

  /// Get memory snapshot as symbol table
  /// Build a new \ref symbol_tablet and for each `lhs` symbol from collected
  ///   assignments [lhs:=rhs] store a new symbol (with the `rhs` as value)
  ///   there. Also, type symbols are copied from \ref symbol_table.
  /// \return a new symbol table with known symbols having their extracted
  ///   values
  symbol_tablet get_snapshot_as_symbol_table();

  using pointer_valuet = gdb_apit::pointer_valuet;
  using memory_addresst = gdb_apit::memory_addresst;

  void create_gdb_process()
  {
    gdb_api.create_gdb_process();
  }
  bool run_gdb_to_breakpoint(const std::string &breakpoint)
  {
    return gdb_api.run_gdb_to_breakpoint(breakpoint);
  }
  void run_gdb_from_core(const std::string &corefile)
  {
    gdb_api.run_gdb_from_core(corefile);
  }

private:
  gdb_apit gdb_api;

  /// External symbol table -- extracted from \ref read_goto_binary
  /// We only expect to analyse symbols located there.
  symbol_tablet symbol_table;
  const namespacet ns;
  expr2ct c_converter;
  allocate_objectst allocate_objects;

  /// Sequence of assignments collected during \ref analyze_symbols
  std::map<exprt, exprt> assignments;

  /// Mapping pointer expression for which \ref get_non_char_pointer_value
  ///   returned nil expression to memory location (from \ref gdb_apit).
  std::map<exprt, memory_addresst> outstanding_assignments;

  /// Storing pairs <address, symbol> such that at `address` is stored the
  ///   value of `symbol`.
  std::map<memory_addresst, exprt> values;

  struct memory_scopet
  {
  private:
    size_t begin_int;
    mp_integer byte_size;
    irep_idt name;

    /// Convert base-16 memory address to a natural number
    /// \param point: the memory address to be converted
    /// \return base-10 unsigned integer equal in value to \p point
    size_t address2size_t(const memory_addresst &point) const;

    /// Helper function that check if a point in memory points inside this scope
    /// \param point_int: memory point as natural number
    /// \return true if the point is inside this scope
    bool check_containment(const size_t &point_int) const
    {
      return point_int >= begin_int && (begin_int + byte_size) > point_int;
    }

  public:
    memory_scopet(
      const memory_addresst &begin,
      const mp_integer &byte_size,
      const irep_idt &name);

    /// Check if \p point points somewhere in this memory scope
    /// \param point: memory address to be check for presence
    /// \return true if \p point is inside *this
    bool contains(const memory_addresst &point) const
    {
      return check_containment(address2size_t(point));
    }

    /// Compute the distance of \p point from the beginning of this scope
    /// \param point: memory address to have the offset computed
    /// \param member_size: size of one element of this scope in bytes
    /// \return `n' such that \p point is the n-th element of this scope
    mp_integer
    distance(const memory_addresst &point, mp_integer member_size) const;

    /// Getter for the name of this memory scope
    /// \return the name as irep id
    irep_idt id() const
    {
      return name;
    }

    /// Getter for the allocation size of this memory scope
    /// \return the size in bytes
    mp_integer size() const
    {
      return byte_size;
    }
  };

  /// Keep track of the dynamically allocated memory
  std::vector<memory_scopet> dynamically_allocated;

  /// Keep track of the memory location for the analyzed symbols
  std::map<irep_idt, pointer_valuet> memory_map;

  bool has_known_memory_location(const irep_idt &id) const
  {
    return memory_map.count(id) != 0;
  }

  /// Search for a memory scope allocated under \p name
  /// \param name: name of the pointer used during allocation
  /// \return iterator to the right memory scope
  std::vector<memory_scopet>::iterator find_dynamic_allocation(irep_idt name);

  /// Search for a memory scope allocated under \p name
  /// \param point: potentially dynamically allocated memory address
  /// \return iterator to the right memory scope
  std::vector<memory_scopet>::iterator
  find_dynamic_allocation(const memory_addresst &point);

  /// Search for the size of the allocated memory for \p name
  /// \param name: name of the pointer used during allocation
  /// \return the size if have a record of \p name's allocation (1 otherwise)
  mp_integer get_malloc_size(irep_idt name);

  /// Build the pointee string for address \p point assuming it points to a
  ///   dynamic allocation of `n' elements each of size \p member_size. E.g.:
  ///
  ///   int *p = (int*)malloc(sizeof(int)*4);
  ///   int *q = &(p[2]);
  ///
  ///   get_malloc_pointee(get_memory(q), sizeof(int)) -> "p+8"
  ///
  /// \param point: potentially dynamically allocated memory address
  /// \param member_size: size of each allocated element
  /// \return pointee as a string if we have a record of the allocation
  optionalt<std::string>
  get_malloc_pointee(const memory_addresst &point, mp_integer member_size);

  /// Wrapper for call get_offset_pointer_bits
  /// \param type: type to get the size of
  /// \return the size of the type in bytes
  mp_integer get_type_size(const typet &type) const;

  /// Assign the gdb-extracted value for \p symbol_name to its symbol
  ///   expression and then process outstanding assignments that this
  ///   extraction introduced.
  /// \param symbol_name: symbol table name to be analysed
  void analyze_symbol(const irep_idt &symbol_name);

  /// Create assignment \p lhs := \p value (see \ref analyze_symbol)
  /// \param lhs: the left-hand side of the assignment; expected to be a
  ///             \ref symbol_exprt
  /// \param value: the value to be assigned; the result of \ref get_expr_value
  void add_assignment(const exprt &lhs, const exprt &value);

  /// Iterate over \p array and fill its operands with the results of calling
  ///   \ref get_expr_value on index expressions into \p expr.
  /// \param expr: the expression to be analysed
  /// \param array: array with zero-initialised elements
  /// \param location: the source location
  /// return an array of the same type as \p expr filled with values from gdb
  exprt get_array_value(
    const exprt &expr,
    const exprt &array,
    const source_locationt &location);

  /// Case analysis on the \ref typet of \p expr
  /// 1) For integers, booleans, and enums: call \ref gdb_apit::get_value
  ///    directly
  /// 2) For chars: return the \p zero_expr
  /// 3) For structs, arrays, and pointers: call their dedicated functions
  /// \param expr: the expression to be analysed
  /// \param zero_expr: zero of the same type as \p expr
  /// \param location: the source location
  /// \return the value of the expression extracted from \ref gdb_apit
  exprt get_expr_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  /// For each of the members of the struct: call \ref get_expr_value
  /// \param expr: struct expression to be analysed
  /// \param zero_expr: struct with zero-initialised members
  /// \param location: the source location
  /// \return the value of the struct from \ref gdb_apit
  exprt get_struct_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  /// For each of the members of the struct: call \ref get_expr_value
  /// \param expr: struct expression to be analysed
  /// \param zero_expr: struct with zero-initialised members
  /// \param location: the source location
  /// \return the value of the struct from \ref gdb_apit
  exprt get_union_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  /// Call \ref gdb_apit::get_memory on \p expr then split based on the
  ///   points-to type being `char` type or not. These have dedicated functions.
  /// \param expr: the input pointer expression
  /// \param zero_expr: null-pointer (or its equivalent)
  /// \param location: the source location
  /// \return symbol expression associated with the gdb-extracted memory
  ///    location
  exprt get_pointer_value(
    const exprt &expr,
    const exprt &zero_expr,
    const source_locationt &location);

  /// Call \ref get_subexpression_at_offset to get the correct member
  ///   expression.
  /// \param expr: the input pointer expression (needed to get the right type)
  /// \param pointer_value: pointer value with structure name and offset as the
  ///   pointee member
  /// \param location: the source location
  /// \return \ref member_exprt that the \p pointer_value points to
  exprt get_pointer_to_member_value(
    const exprt &expr,
    const pointer_valuet &pointer_value,
    const source_locationt &location);

  /// Similar to \ref get_char_pointer_value. Doesn't re-call
  ///   \ref gdb_apit::get_memory, calls \ref get_expr_value on _dereferenced_
  ///   \p expr (the result of which is assigned to a new symbol).
  /// \param expr: the pointer expression to be analysed
  /// \param value: pointer value from \ref gdb_apit::get_memory
  /// \param location: the source location
  /// \return symbol expression associated with \p memory_location
  exprt get_non_char_pointer_value(
    const exprt &expr,
    const pointer_valuet &value,
    const source_locationt &location);

  /// Extract the function name from \p pointer_value, check it has a symbol and
  ///   return the associated symbol expression
  /// \param expr: the pointer-to-function expression
  /// \param pointer_value: pointer value with the function name as the pointee
  ///   member
  /// \param location: the source location
  /// \return symbol expression for the function pointed at by \p pointer_value
  exprt get_pointer_to_function_value(
    const exprt &expr,
    const pointer_valuet &pointer_value,
    const source_locationt &location);

  /// If \p memory_location is found among \ref values then return the symbol
  ///   expression associated with it.
  /// Otherwise we add the appropriate \ref values mapping:
  /// 1) call \ref gdb_apit::get_memory on the \p expr
  /// 2) allocate new symbol and assign it with the memory string from 1)
  /// 3) fill \ref values (mapping \p memory_location to the new symbol)
  /// \param expr: the pointer expression to be analysed
  /// \param memory_location: pointer value from \ref gdb_apit::get_memory
  /// \param location: the source location
  /// \return symbol expression associated with \p memory_location
  exprt get_char_pointer_value(
    const exprt &expr,
    const memory_addresst &memory_location,
    const source_locationt &location);

  /// Call \ref add_assignment for each pair in \ref outstanding_assignments
  void process_outstanding_assignments();

  /// Extract a stringified value from and c-converted \p expr
  /// \param expr: expression to be extracted
  /// \return the value as a string
  std::string get_gdb_value(const exprt &expr);

  /// Analyzes the \p pointer_value to decide if it point to a struct or a
  ///   union (or array)
  /// \param pointer_value: pointer value to be analyzed
  /// \param expected_type: type of the potential member
  /// \return true if pointing to a member
  bool points_to_member(
    pointer_valuet &pointer_value,
    const pointer_typet &expected_type);
};

#endif // CPROVER_MEMORY_ANALYZER_ANALYZE_SYMBOL_H
