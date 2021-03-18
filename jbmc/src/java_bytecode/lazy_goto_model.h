/// Author: Diffblue Ltd.

/// \file
/// Model for lazy loading of functions

#ifndef CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H

#include <langapi/language_file.h>

#include <goto-programs/abstract_goto_model.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_model.h>

#include "lazy_goto_functions_map.h"

class optionst;

/// A GOTO model that produces function bodies on demand. It owns a
/// `language_filest`, which is used to populate symbol-table method bodies.
/// They are then passed through `goto_convert` and any driver-program-supplied
/// post-convert transformations to produce the final GOTO representation of the
/// desired function.
///
/// This can be converted to a conventional `goto_modelt` if desired by calling
/// `process_whole_model_and_freeze`.
///
/// The typical use case looks like:
///
///     lazy_goto_modelt model(...callback parameters...);
///     model.initialize(cmdline.args, options);
///     model.get_goto_function("needed_function1")
///     model.get_goto_function("needed_function2");
///     ...
///     model.get_goto_function("needed_functionN");
///     // optional:
///     std::unique_ptr<goto_modelt> concrete_model =
///       model.process_whole_model_and_freeze();
///
/// See the constructor `lazy_goto_modelt::lazy_goto_modelt` for more detail
/// on the callbacks needed.
class lazy_goto_modelt : public abstract_goto_modelt
{
public:
  /// Callback function that post-processes a GOTO function. The
  /// `goto_model_functiont` passed in has just been produced by `goto_convert`,
  /// and so may contain function pointers, `RETURN` statements and other GOTO
  /// constructs that are conventionally post-processed away.
  /// The `model` parameter can be used to inspect other functions, but the
  /// implementation should be aware that there may be GOTO functions that are
  /// still to be converted, so it is not in its final state at this point.
  typedef std::function<
    void(goto_model_functiont &function, const abstract_goto_modelt &model)>
    post_process_functiont;

  /// Callback function that post-processes a whole GOTO model. The functions
  /// in the model have been produced by `goto_convert` and then passed through
  /// the corresponding `post_process_functiont`. Returns true on error,
  /// in which case `lazy_goto_modelt::process_whole_model_and_freeze` will
  /// return null.
  typedef std::function<bool(goto_modelt &goto_model)> post_process_functionst;

  /// Callback function that determines whether the creator of a
  /// `lazy_goto_modelt` can itself supply a function body for a given name,
  /// whether as a fallback or an override. Only used from
  /// `can_produce_goto_function`, but should only return true for a function
  /// that `generate_function_body` can actually provide a body for, otherwise
  /// the `lazy_goto_modelt` user is likely to end up confused.
  typedef lazy_goto_functions_mapt::can_generate_function_bodyt
    can_generate_function_bodyt;

  /// Callback function that may provide a body for a GOTO function, either as
  /// a fallback (when we don't have source code for a function, often called a
  /// stub function) or as an override (when we do have source code, but want to
  /// e.g. replace a difficult-to-analyse function body with a simpler model,
  /// or outright omission).
  /// Gets parameters:
  ///  `function_name`: a symbol-table symbol name we're asked to populate
  ///  `symbol_table`: symbol table we should add new symbols to, such as
  ///    function local variables.
  ///  `function`: `goto_functiont` that we may populate. That could be done
  ///    directly, or by populating the corresponding symbol in the symbol table
  ///    and calling `goto_convert`.
  ///  `body_available`: true if we have source code for the function body, and
  ///    so the function will be given a body if this callback declines to
  ///    provide one. If you only want to provide fallback (stub) bodies, check
  ///    this is false before proceeding. If it is true and a body is supplied,
  ///    we are overriding the source code definition.
  /// Returns: true if we provided a function body; false otherwise. When true
  ///   is returned our definition is definitive; when false is returned a body
  ///   will be generated from source code where available.
  typedef lazy_goto_functions_mapt::generate_function_bodyt
    generate_function_bodyt;

  /// Construct a lazy GOTO model, supplying callbacks that customise its
  /// behaviour. Consider using `from_handler_object` if the callbacks supplied
  /// would be members of the same class (i.e.
  /// `my_drivert::process_goto_function`,
  /// `my_drivert::generate_function_body` etc). See the documentation of the
  /// parameter types for more precise information on what a given callback
  /// should do.
  /// \param post_process_function: called to post-process a GOTO function after
  ///   it is `goto_convert`ed but before `get_goto_function` returns. This
  ///   usually runs transformations such as `remove_returns` and
  ///   `remove_virtual_functions`. It can be a no-op, in which case GOTO
  ///   programs will be returned exactly as produced by `goto_convert`.
  /// \param post_process_functions: called to post-process the whole model
  ///   before `process_whole_model_and_freeze` returns. This usually runs
  ///   transformations that can only be applied once all functions to be
  ///   converted are known, such as dead global variable elimination.
  /// \param driver_program_can_generate_function_body: boolean predicate to
  ///   indicate whether `driver_program_generate_function_body` can produce
  ///   a body for a given function name. If this returns true for a particular
  ///   function, so will `can_produce_function`.
  /// \param driver_program_generate_function_body: called to give the driver
  ///   program the opportunity to provide a body for a function. It is passed
  ///   a boolean indicating whether a body is available conventionally (i.e.
  ///   generated from source code), so this hook can be used to provide
  ///   fallbacks for missing functions or to override available functions as
  ///   you like.
  /// \param message_handler: used for logging.
  explicit lazy_goto_modelt(
    post_process_functiont post_process_function,
    post_process_functionst post_process_functions,
    can_generate_function_bodyt driver_program_can_generate_function_body,
    generate_function_bodyt driver_program_generate_function_body,
    message_handlert &message_handler);

  lazy_goto_modelt(lazy_goto_modelt &&other);

  lazy_goto_modelt &operator=(lazy_goto_modelt &&other)
  {
    goto_model = std::move(other.goto_model);
    language_files = std::move(other.language_files);
    return *this;
  }

  /// Create a lazy_goto_modelt from a object that defines function/module pass
  /// handlers.
  /// Its members functions will be used to construct the lazy model:
  /// `post_process_function` gets `handler.process_goto_function`
  /// `post_process_functions` gets `handler.process_goto_functions`
  /// `driver_program_can_generate_function_body` gets
  ///   `handler.can_generate_function_body`
  /// `driver_program_generate_function_body` gets
  ///   `handler.generate_function_body`
  /// \param handler: An object that defines the handlers
  /// \param options: The options passed to process_goto_functions
  /// \param message_handler: The message_handler to use for logging
  /// \tparam THandler: a type that defines methods process_goto_function and
  /// process_goto_functions
  template <typename THandler>
  static lazy_goto_modelt from_handler_object(
    THandler &handler,
    const optionst &options,
    message_handlert &message_handler)
  {
    return lazy_goto_modelt(
      [&handler,
       &options](goto_model_functiont &fun, const abstract_goto_modelt &model) {
        handler.process_goto_function(fun, model, options);
      },
      [&handler, &options](goto_modelt &goto_model) -> bool {
        return handler.process_goto_functions(goto_model, options);
      },
      [&handler](const irep_idt &name) -> bool {
        return handler.can_generate_function_body(name);
      },
      [&handler](
        const irep_idt &function_name,
        symbol_table_baset &symbol_table,
        goto_functiont &function,
        bool is_first_chance) {
        return handler.generate_function_body(
          function_name, symbol_table, function, is_first_chance);
      },
      message_handler);
  }

  void
  initialize(const std::vector<std::string> &files, const optionst &options);

  /// Eagerly loads all functions from the symbol table.
  void load_all_functions() const;

  language_filet &add_language_file(const std::string &filename)
  {
    return language_files.add_file(filename);
  }

  /// The model returned here has access to the functions we've already
  /// loaded but is frozen in the sense that, with regard to the facility to
  /// load new functions, it has let it go.
  /// Before freezing the functions all module-level passes are run
  /// \param model: The lazy_goto_modelt to freeze
  /// \return The frozen goto_modelt or an empty optional if freezing fails
  static std::unique_ptr<goto_modelt>
  process_whole_model_and_freeze(lazy_goto_modelt &&model)
  {
    if(model.finalize())
      return nullptr;
    return std::move(model.goto_model);
  }

  // Implement the abstract_goto_modelt interface:

  /// Accessor to retrieve the internal goto_functionst.
  /// Use with care; concurrent use of get_goto_function will have side-effects
  /// on this map which may surprise users, including invalidating any iterators
  /// they have stored.
  const goto_functionst &get_goto_functions() const override
  {
    return goto_model->goto_functions;
  }

  const symbol_tablet &get_symbol_table() const override
  {
    return symbol_table;
  }

  bool can_produce_function(const irep_idt &id) const override;

  /// Get a GOTO function body. `id` must be a valid symbol-table symbol. Its
  /// body is produced by:
  /// 1. If we already have a GOTO function body for `id`, return it.
  /// 2. If the user's `driver_program_generate_function_body` function provides
  ///    a body, pass it through the user's `post_process_function` callback,
  ///    store and return it.
  /// 3. If we already have a `codet` for the function stored in the symbol
  ///    table, `goto_convert` it, pass it through the user's
  ///    `post_process_function` callback, store it and return it.
  /// 4. Otherwise, if some `languaget` claims to be able to produce it (this is
  ///    determined by `languaget::methods_provided`), call its
  ///    `languaget::convert_lazy_method` function. If that results in a `codet`
  ///    representation of the function stored in the symbol table, convert it
  ///    to GOTO and return it as in step (3).
  const goto_functionst::goto_functiont &
  get_goto_function(const irep_idt &id) override
  {
    return goto_functions.at(id);
  }

  /// Check that the goto model is well-formed
  ///
  /// The validation mode indicates whether well-formedness check failures are
  /// reported via DATA_INVARIANT violations or exceptions.
  void validate(
    const validation_modet vm = validation_modet::INVARIANT,
    const goto_model_validation_optionst &goto_model_validation_options =
      goto_model_validation_optionst{}) const override
  {
    goto_model->validate(vm, goto_model_validation_options);
  }

private:
  std::unique_ptr<goto_modelt> goto_model;

public:
  /// Reference to symbol_table in the internal goto_model
  symbol_tablet &symbol_table;

private:
  const lazy_goto_functions_mapt goto_functions;
  language_filest language_files;

  // Function/module processing functions
  const post_process_functiont post_process_function;
  const post_process_functionst post_process_functions;
  const can_generate_function_bodyt driver_program_can_generate_function_body;
  const generate_function_bodyt driver_program_generate_function_body;

  /// Logging helper field
  message_handlert &message_handler;

  bool finalize();
};

#endif // CPROVER_GOTO_PROGRAMS_LAZY_GOTO_MODEL_H
