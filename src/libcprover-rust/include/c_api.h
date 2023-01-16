// Author Fotis Koutoulakis for Diffblue Ltd 2022.

#pragma once

#include <memory>

// NOLINTNEXTLINE(build/include)
#include "rust/cxx.h"

struct api_sessiont;

// Helper function
std::vector<std::string> const &
translate_vector_of_string(rust::Vec<rust::String> elements);

// Exposure of the C++ object oriented API through free-standing functions.
std::unique_ptr<api_sessiont> new_api_session();
std::vector<std::string> const &get_messages();
