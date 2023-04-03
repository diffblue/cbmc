// Author Fotis Koutoulakis for Diffblue Ltd 2022.

#pragma once

#include <memory>
#include <stdexcept>
#include <string>

// NOLINTNEXTLINE(build/include)
#include "rust/cxx.h"
// NOLINTNEXTLINE(build/include)
#include "include/c_errors.h"

struct api_sessiont;
struct verification_resultt;
enum class verifier_resultt;
enum class prop_statust;

// Helper function
std::vector<std::string> const &
_translate_vector_of_string(rust::Vec<rust::String> elements);

// Exposure of the C++ object oriented API through free-standing functions.
std::unique_ptr<api_sessiont> new_api_session();
std::vector<std::string> const &get_messages();

// Exposure of verification result related functions.
verifier_resultt
get_verification_result(const std::unique_ptr<verification_resultt> &v);
std::vector<std::string> const &
get_property_ids(const std::unique_ptr<verification_resultt> &);
std::string const &get_property_description(
  const std::unique_ptr<verification_resultt> &,
  const std::string &);
prop_statust get_property_status(
  const std::unique_ptr<verification_resultt> &,
  const std::string &);

// NOLINTNEXTLINE(readability/namespace)
namespace rust
{
// NOLINTNEXTLINE(readability/namespace)
namespace behavior
{
template <typename Try, typename Fail>
static void trycatch(Try &&func, Fail &&fail) noexcept
{
  try
  {
    func();
  }
  catch(const cprover_exception_baset &e)
  {
    fail(e.what());
  }
  catch(const invariant_failedt &i)
  {
    fail(i.what());
  }
  catch(const std::out_of_range &our)
  {
    fail(our.what());
  }
  catch(const std::exception &exc)
  {
    // collective catch-all for all exceptions that derive
    // from standard exception class.
    fail(exc.what());
  }
}

} // namespace behavior

} // namespace rust
