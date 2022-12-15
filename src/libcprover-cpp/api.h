// Author: Fotis Koutoulakis for Diffblue Ltd.

#ifndef CPROVER_LIBCPROVER_CPP_API_H
#define CPROVER_LIBCPROVER_CPP_API_H

#include <memory>
#include <string>
#include <vector>

// Forward declaration of API dependencies
struct api_session_implementationt;

// There has been a design decision to allow users to include all of
// the API headers by just including `api.h`, so we want to have an
// include for all the API headers below. If we get any auxiliary
// development tools complaining about the includes, please use
// a pragma like below to silence the warning (at least as long
// as the design principle is to be followed.)

#include "options.h" // IWYU pragma: keep

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
  std::unique_ptr<api_session_implementationt> implementation;
};

#endif
