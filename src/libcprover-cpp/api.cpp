// Author: Fotis Koutoulakis for Diffblue Ltd.

#include "api.h"

#include <util/cmdline.h>
#include <util/config.h>
#include <util/message.h>
#include <util/options.h>

#include <goto-programs/goto_model.h>
#include <goto-programs/initialize_goto_model.h>

#include <ansi-c/ansi_c_language.h>
#include <langapi/mode.h>

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
