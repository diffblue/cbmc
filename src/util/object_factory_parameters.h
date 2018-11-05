/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_UTIL_OBJECT_FACTORY_PARAMETERS_H

#include <cstdint>
#include <limits>

#include <util/irep.h>

class cmdlinet;
class optionst;

struct object_factory_parameterst
{
  object_factory_parameterst()
  {
  }

  explicit object_factory_parameterst(const optionst &options)
  {
    set(options);
  }

  virtual ~object_factory_parameterst() = default;

  /// Maximum value for the non-deterministically-chosen length of an array.
  size_t max_nondet_array_length = 5;

  /// Maximum value for the non-deterministically-chosen length of a string.
  size_t max_nondet_string_length =
    static_cast<std::size_t>(std::numeric_limits<std::int32_t>::max());

  /// Minimum value for the non-deterministically-chosen length of a string.
  size_t min_nondet_string_length = 0;

  /// Maximum depth of pointer chains (that contain recursion) in the nondet
  /// generated input objects.
  ///
  /// Used to prevent the object factory from looping infinitely during the
  /// generation of code that allocates/initializes recursive data structures
  /// (such as a linked list). The object factory tracks the number of times a
  /// pointer has been dereferenced in a 'depth' counter variable. If a pointer
  /// to be initialized points to an object of a type that already occured on
  /// the current pointer chain, and if 'depth' is larger than
  /// 'max_nondet_tree_depth`, then the pointer is set to null. The parameter
  /// does not affect non-recursive data structures, which are always
  /// initialized to their full depth.
  size_t max_nondet_tree_depth = 5;

  /// To force a certain depth of non-null objects.
  /// The default is that objects are 'maybe null' up to the nondet tree depth.
  /// Examples:
  /// * max_nondet_tree_depth=0, min_null_tree_depth irrelevant
  ///   pointer initialized to null
  /// * max_nondet_tree_depth=n, min_null_tree_depth=0
  ///   pointer and children up to depth n maybe-null, beyond n null
  /// * max_nondet_tree_depth=n >=m, min_null_tree_depth=m
  ///   pointer and children up to depth m initialized to non-null,
  ///   children up to n maybe-null, beyond n null
  size_t min_null_tree_depth = 0;

  /// Force string content to be ASCII printable characters when set to true.
  bool string_printable = false;

  /// Function id, used as a prefix for identifiers of temporaries
  irep_idt function_id;

  /// Assigns the parameters from given options
  void set(const optionst &);
};

void parse_object_factory_options(const cmdlinet &, optionst &);

#endif
