/// \file
/// \brief Magic numbers used throughout the codebase
/// \author Kareem Khazem <karkhaz@karkhaz.com>

#ifndef CPROVER_UTIL_MAGIC_H
#define CPROVER_UTIL_MAGIC_H

#include <cstddef>

const std::size_t CNF_DUMP_BLOCK_SIZE = 4096;
const std::size_t MAX_FLATTENED_ARRAY_SIZE=1000;
const std::size_t STRING_REFINEMENT_MAX_CHAR_WIDTH = 16;
// Limit the size of strings in traces to 64M chars to avoid memout
const std::size_t MAX_CONCRETE_STRING_SIZE = 1 << 26;

// The top end of the range of integers for which dstrings are precomputed
constexpr std::size_t DSTRING_NUMBERS_MAX = 64;

/// Limit the size of arrays for which field_sensitivity gets applied.
/// Necessary because large constant arrays slow-down the process.
constexpr std::size_t DEFAULT_MAX_FIELD_SENSITIVITY_ARRAY_SIZE = 64;

#endif
