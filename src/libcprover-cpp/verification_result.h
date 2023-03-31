// Copyright (c) 2023 Fotis Koutoulakis for Diffblue Ltd.

/// \file
/// Interface for the various verification engines providing results
//  in a structured form.

#ifndef CPROVER_LIBCPROVER_CPP_VERIFICATION_RESULT_H
#define CPROVER_LIBCPROVER_CPP_VERIFICATION_RESULT_H

#include <map>
#include <memory>
#include <string>
#include <vector>

#ifndef USE_STD_STRING
#  define USE_DSTRING
#endif

#ifdef USE_DSTRING
class dstringt;
typedef dstringt irep_idt;
#else
typedef std::string irep_idt;
#endif

struct property_infot;
using propertiest = std::map<irep_idt, property_infot>;
enum class resultt;

// The enumerations here mirror the ones in properties.h.
// The reason we do so is that we want to expose the same information
// to users of the API, without including (and therefore, exposing)
// CBMC internal headers.

enum class prop_statust
{
  /// The property was not checked (also used for initialization)
  NOT_CHECKED,
  /// The checker was unable to determine the status of the property
  UNKNOWN,
  /// The property was proven to be unreachable
  NOT_REACHABLE,
  /// The property was not violated
  PASS,
  /// The property was violated
  FAIL,
  /// An error occurred during goto checking
  ERROR
};

enum class verifier_resultt
{
  UNKNOWN,
  /// No properties were violated
  PASS,
  /// Some properties were violated
  FAIL,
  /// An error occurred during goto checking
  ERROR
};

struct verification_resultt
{
  verification_resultt();
  verification_resultt(const verification_resultt &other);
  ~verification_resultt();
  verification_resultt &operator=(verification_resultt &&);
  verification_resultt &operator=(const verification_resultt &other);

  void set_result(resultt &result);
  void set_properties(propertiest &properties);

  verifier_resultt final_result() const;
  std::vector<std::string> get_property_ids() const;
  std::string get_property_description(const std::string &property_id) const;
  prop_statust get_property_status(const std::string &property_id) const;

private:
  class verification_result_implt;
  std::unique_ptr<verification_result_implt> _impl;
};

#endif // CPROVER_GOTO_CHECKER_VERIFICATION_RESULT_H
