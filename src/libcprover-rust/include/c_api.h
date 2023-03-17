// Author Fotis Koutoulakis for Diffblue Ltd 2022.

#pragma once

#include <util/exception_utils.h>

#include <memory>

// NOLINTNEXTLINE(build/include)
#include "rust/cxx.h"

struct api_sessiont;

// Helper function
std::vector<std::string> const &
_translate_vector_of_string(rust::Vec<rust::String> elements);

// Exposure of the C++ object oriented API through free-standing functions.
std::unique_ptr<api_sessiont> new_api_session();
std::vector<std::string> const &get_messages();

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
}

} // namespace behavior

} // namespace rust
