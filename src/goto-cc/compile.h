/*******************************************************************\

Module: Compile and link source and object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Compile and link source and object files.

#ifndef CPROVER_GOTO_CC_COMPILE_H
#define CPROVER_GOTO_CC_COMPILE_H

#include <util/cmdline.h>
#include <util/message.h>
#include <util/rename_symbol.h>

#include <goto-programs/goto_model.h>

class language_filest;

class compilet : public messaget
{
public:
  // compilation results
  namespacet ns;
  goto_modelt goto_model;

  // configuration
  bool echo_file_name;
  std::string working_directory;
  std::string override_language;

  enum { PREPROCESS_ONLY, // gcc -E
         COMPILE_ONLY, // gcc -c
         ASSEMBLE_ONLY, // gcc -S
         LINK_LIBRARY, // ld -r
         COMPILE_LINK, // gcc -shared
         COMPILE_LINK_EXECUTABLE // gcc
       } mode;

  std::list<std::string> library_paths;
  std::list<std::string> source_files;
  std::list<std::string> object_files;
  std::list<std::string> libraries;
  std::list<std::string> tmp_dirs;
  std::list<irep_idt> seen_modes;

  std::string object_file_extension;
  std::string output_file_executable;

  // the two options below are mutually exclusive -- use either or
  std::string output_file_object, output_directory_object;

  compilet(cmdlinet &_cmdline, message_handlert &mh, bool Werror);

  ~compilet();

  bool add_input_file(const std::string &);
  bool find_library(const std::string &);
  bool add_files_from_archive(const std::string &file_name, bool thin_archive);

  bool parse(const std::string &filename, language_filest &);
  bool parse_stdin();
  bool doit();
  bool compile();
  bool link();

  bool parse_source(const std::string &);

  bool write_bin_object_file(const std::string &, const goto_modelt &);

  /// \brief Has this compiler written any object files?
  bool wrote_object_files() const { return wrote_object; }

  /// \brief `__CPROVER_...` macros written to object files and their arities
  ///
  /// \return A mapping from every `__CPROVER` macro that this compiler
  /// wrote to one or more object files, to how many parameters that
  /// `__CPROVER` macro has.
  void cprover_macro_arities(std::map<irep_idt,
                                      std::size_t> &cprover_macros) const
  {
    PRECONDITION(wrote_object);
    for(const auto &pair : written_macros)
      cprover_macros.insert({pair.first,
        to_code_type(pair.second.type).parameters().size()});
  }

protected:
  cmdlinet &cmdline;
  bool warning_is_fatal;

  std::size_t function_body_count(const goto_functionst &) const;

  void add_compiler_specific_defines() const;

  void convert_symbols(goto_functionst &dest);

  bool add_written_cprover_symbols(const symbol_tablet &symbol_table);
  std::map<irep_idt, symbolt> written_macros;

  // clients must only call add_written_cprover_symbols() if an object
  // file has been written. The case where an object file was written
  // but there were no __CPROVER symbols in the goto-program is distinct
  // from the case where the user forgot to write an object file before
  // calling add_written_cprover_symbols().
  bool wrote_object;
};

#endif // CPROVER_GOTO_CC_COMPILE_H
