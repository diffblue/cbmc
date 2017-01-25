/*******************************************************************\

Module: Counterexample-Guided Inductive Synthesis

Author: Daniel Kroening, kroening@kroening.com
        Pascal Kesseli, pascal.kesseli@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_CEGIS_CEGIS_UTIL_STRING_HELPER_H
#define CPROVER_CEGIS_CEGIS_UTIL_STRING_HELPER_H

#include <string>

/**
 * @brief
 *
 * @details
 *
 * @param haystack
 * @param needle
 *
 * @return
 */
bool contains(const std::string &haystack, const std::string &needle);

/**
 * @brief
 *
 * @details
 *
 * @param haystack
 * @param prefix
 *
 * @return
 */
bool starts_with(const std::string &haystack, const std::string &prefix);

/**
 * @brief
 *
 * @details
 *
 * @param haystack
 * @param suffix
 *
 * @return
 */
bool ends_with(const std::string &haystack, const std::string &suffix);

/**
 * @brief
 *
 * @details
 *
 * @param haystack
 * @param suffix
 */
void remove_suffix(std::string &haystack, const std::string &suffix);

#endif // CPROVER_CEGIS_CEGIS_UTIL_STRING_HELPER_H
