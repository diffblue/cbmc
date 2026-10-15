/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_UTIL_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_UTIL_OBJECT_FACTORY_PARAMETERS_H

#include <list>

#include <util/irep.h>
#include <util/magic.h>

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
  /// Defaults to MAX_CONCRETE_STRING_SIZE - 1 such that even with a null
  /// terminator all strings can be rendered concretely by string-refinement's
  /// `get_array` function, which is used by `--trace` among other C/JBMC
  /// options.
  size_t max_nondet_string_length = MAX_CONCRETE_STRING_SIZE - 1;

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

  /// Maximum total number of dynamic objects the object factory will
  /// allocate on behalf of a single nondet-initialisation root.
  ///
  /// The `max_nondet_tree_depth` cap above only fires when the same
  /// struct tag appears twice on the same pointer chain, which is the
  /// pattern the object factory historically worried about (linked
  /// lists, trees).  Wide-but-non-recursive struct hierarchies, by
  /// contrast, are deep without ever revisiting the same type: a single
  /// pointer transitively reaches many further pointer-to-struct fields,
  /// none of which cycle back, so the depth cap never fires and the
  /// object factory generates an exponentially large init body.
  ///
  /// This hard cap on allocation count provides a belt-and-braces
  /// termination guarantee independent of the depth cap.  When the cap
  /// is hit, further pointers are initialized to NULL rather than to
  /// freshly-allocated sub-structs.  This is an under-approximation: the
  /// non-null branch is dropped, so paths through such pointers are no
  /// longer explored, and the force-NULL applies even below
  /// `min_null_tree_depth` (the termination guard overrides it).
  ///
  /// Note this defaults to a finite value rather than "unlimited", so it
  /// changes the default behaviour of *all* C nondet initialisation that
  /// goes through `c_nondet_symbol_factory` (e.g. `ansi_c_entry_point`,
  /// not just `--generate-function-body`): a root transitively reaching
  /// more than this many dynamic objects is now truncated.  The default
  /// is chosen well above realistic harness needs.  The parameter lives
  /// in this shared base but is only enforced by the C object factory;
  /// JBMC's Java factory and goto-harness's recursive initialisation
  /// neither enforce it nor expose the corresponding CLI option.
  size_t max_dynamic_object_instances = 1000;

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

  /// Force one of finitely many explicitly given input strings
  std::list<std::string> string_input_values;

  /// Function id, used as a prefix for identifiers of temporaries
  irep_idt function_id;

  /// Assigns the parameters from given options
  void set(const optionst &);
};

void parse_object_factory_options(const cmdlinet &, optionst &);

#endif
