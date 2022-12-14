// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "api.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/message.h>
#include <util/options.h>
#include <util/ui_message.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/link_to_library.h>
#include <goto-programs/process_goto_program.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/set_properties.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/cprover_library.h>
#include <assembler/remove_asm.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <langapi/mode.h>
#include <pointer-analysis/add_failed_symbols.h>

#include <memory>
#include <string>
#include <vector>

extern configt config;

struct api_session_implementationt
{
  std::unique_ptr<goto_modelt> model;
  std::unique_ptr<message_handlert> message_handler;
  std::unique_ptr<optionst> options;
};

api_sessiont::api_sessiont() : api_sessiont{api_optionst::create()}
{
}

api_sessiont::api_sessiont(const api_optionst &options)
  : implementation{util_make_unique<api_session_implementationt>()}
{
  implementation->message_handler =
    util_make_unique<null_message_handlert>(null_message_handlert{});
  implementation->options = options.to_engine_options();
  // Needed to initialise the language options correctly
  cmdlinet cmdline;
  // config is global in config.cpp
  config.set(cmdline);
  // Initialise C language mode
  register_language(new_ansi_c_language);
}

api_sessiont::~api_sessiont() = default;

struct api_messaget
{
  std::string string;
};

const char *api_message_get_string(const api_messaget &message)
{
  return message.string.c_str();
}

class api_message_handlert : public message_handlert
{
public:
  explicit api_message_handlert(
    api_message_callbackt callback,
    api_call_back_contextt context);

  void print(unsigned level, const std::string &message) override;

  // Unimplemented for now. We may need to implement these as string conversions
  // or something later.
  void print(unsigned level, const xmlt &xml) override{};
  void print(unsigned level, const jsont &json) override{};

  void flush(unsigned) override{};

private:
  api_call_back_contextt context;
  api_message_callbackt callback;
};

api_message_handlert::api_message_handlert(
  api_message_callbackt callback,
  api_call_back_contextt context)
  : message_handlert{}, context{context}, callback{callback}
{
}

void api_message_handlert::print(unsigned level, const std::string &message)
{
  if(!callback)
    return;
  api_messaget api_message{message};
  callback(api_message, context);
}

void api_sessiont::set_message_callback(
  api_message_callbackt callback,
  api_call_back_contextt context)
{
  implementation->message_handler =
    util_make_unique<api_message_handlert>(callback, context);
}

void api_sessiont::load_model_from_files(const std::vector<std::string> &files)
{
  implementation->model = util_make_unique<goto_modelt>(initialize_goto_model(
    files, *implementation->message_handler, *implementation->options));
}

void api_sessiont::verify_model()
{
  PRECONDITION(implementation->model);

  // Remove inline assembler; this needs to happen before adding the library.
  remove_asm(*implementation->model);

  // add the library
  messaget log{*implementation->message_handler};
  log.status() << "Adding CPROVER library (" << config.ansi_c.arch << ")"
               << messaget::eom;
  link_to_library(
    *implementation->model,
    *implementation->message_handler,
    cprover_c_library_factory);

  // Common removal of types and complex constructs
  if(::process_goto_program(
       *implementation->model, *implementation->options, log))
  {
    return;
  }

  // add failed symbols
  // needs to be done before pointer analysis
  add_failed_symbols(implementation->model->symbol_table);

  // label the assertions
  // This must be done after adding assertions and
  // before using the argument of the "property" option.
  // Do not re-label after using the property slicer because
  // this would cause the property identifiers to change.
  label_properties(*implementation->model);

  remove_skip(*implementation->model);

  ui_message_handlert ui_message_handler(*implementation->message_handler);
  all_properties_verifier_with_trace_storaget<multi_path_symex_checkert>
    verifier(
      *implementation->options, ui_message_handler, *implementation->model);
  (void)verifier();
  verifier.report();
}

void api_sessiont::drop_unused_functions()
{
  INVARIANT(
    implementation->model != nullptr,
    "Model has not been loaded. Load it first using "
    "api::load_model_from_files");

  messaget log{*implementation->message_handler};
  log.status() << "Performing instrumentation pass: dropping unused functions"
               << messaget::eom;

  remove_unused_functions(
    *implementation->model, *implementation->message_handler);
}

void api_sessiont::validate_goto_model()
{
  INVARIANT(
    implementation->model != nullptr,
    "Model has not been loaded. Load it first using "
    "api::load_model_from_files");

  messaget log{*implementation->message_handler};
  log.status() << "Validating consistency of goto-model supplied to API session"
               << messaget::eom;

  implementation->model->validate();
}
