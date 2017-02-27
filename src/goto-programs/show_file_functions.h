/*******************************************************************\

Module: Show the functions present in the file

Author: Fotis Koutoulakis

\*******************************************************************/

#pragma once

#define OPT_SHOW_FILE_FUNCTIONS \
  "(show-file-functions)"

#define HELP_SHOW_FILE_FUNCTIONS \
  " --show-file-functions             show only symbols that correspond to functions."

void show_file_functions(std::ostream &, const symbol_tablet &);
