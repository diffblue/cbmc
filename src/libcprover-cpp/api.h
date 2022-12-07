// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifndef CPROVER_LIBCPROVER_CPP_API_H
#define CPROVER_LIBCPROVER_CPP_API_H

#include <memory>
#include <string>
#include <vector>

// Forward declaration of API dependencies
class goto_modelt;
class message_handlert;
class optionst;

#include "options.h"

// An object in the pattern of Session Facade - owning all of the memory
// the API is using and being responsible for the management of that.
struct api_sessiont
{
  // Initialising constructor
  api_sessiont();
  explicit api_sessiont(const api_optionst &options);
  ~api_sessiont(); // default constructed in the .cpp file

  /// Load a goto_model from a given vector of filenames.
  /// \param files: A vector<string> containing the filenames to be loaded
  void load_model_from_files(const std::vector<std::string> &files);

private:
  std::unique_ptr<goto_modelt> model;
  std::unique_ptr<message_handlert> message_handler;
  std::unique_ptr<optionst> options;
};

#endif
