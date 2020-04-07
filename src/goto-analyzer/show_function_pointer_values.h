// Module: Show function pointer values
// Author: Fotis Koutoulakis, fotis.koutoulakis@diffblue.com
// Copyright: Diffblue Ltd, 2020

#pragma once

#include <string>

class goto_modelt;
class ai_baset;
class optionst;
class message_handlert;

/// Print the values of function pointer call sites as JSON to a file.
/// Requires label_function_pointer_call_sites and the ai to have already
/// run on the goto model to work properly.
void print_function_pointer_values(
    const goto_modelt &goto_model,
    const ai_baset &ai,
    const optionst &options,
    message_handlert &message_handler,
    std::string filename);