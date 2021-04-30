/*******************************************************************\

Module: Compile and link source and object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

/// \file
/// Compile and link source and object files.

#ifndef CPROVER_GOTO_CC_COMPILE_H
#define CPROVER_GOTO_CC_COMPILE_H

#include <util/message.h>
#include <util/std_types.h>
#include <util/symbol.h>

#include <map>

class cmdlinet;
class goto_functionst;
class goto_modelt;
class language_filest;
class languaget;
class symbol_tablet;

class compilet
{
public:
  // configuration
  bool echo_file_name;
  bool validate_goto_model = false;

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
  bool parse_stdin(languaget &);
  bool doit();
  optionalt<symbol_tablet> compile();
  bool link(optionalt<symbol_tablet> &&symbol_table);

  optionalt<symbol_tablet> parse_source(const std::string &);

  /// Writes the goto functions of \p src_goto_model to a binary format object
  /// file.
  /// \param file_name: Target file to serialize \p src_goto_model to
  /// \param src_goto_model: goto model to serialize
  /// \param validate_goto_model: enable goto-model validation
  /// \param message_handler: message handler
  /// \return true on error, false otherwise
  static bool write_bin_object_file(
    const std::string &file_name,
    const goto_modelt &src_goto_model,
    bool validate_goto_model,
    message_handlert &message_handler);

  /// \brief Has this compiler written any object files?
  bool wrote_object_files() const { return wrote_object; }

  /// \brief `__CPROVER_...` macros written to object files and their arities
  ///
  /// \param [out] cprover_macros: A mapping from every `__CPROVER` macro that
  ///   this compiler wrote to one or more object files, to how many parameters
  ///   that `__CPROVER` macro has.
  void cprover_macro_arities(std::map<irep_idt,
                                      std::size_t> &cprover_macros) const
  {
    PRECONDITION(wrote_object);
    for(const auto &pair : written_macros)
      cprover_macros.insert({pair.first,
        to_code_type(pair.second.type).parameters().size()});
  }

protected:
  std::string working_directory;
  std::string override_language;

  std::list<std::string> tmp_dirs;
  std::list<irep_idt> seen_modes;

  messaget log;
  cmdlinet &cmdline;
  bool warning_is_fatal;

  /// \brief Whether to keep implementations of file-local symbols
  const bool keep_file_local;

  /// \brief String to include in all mangled names
  const std::string file_local_mangle_suffix;

  static std::size_t function_body_count(const goto_functionst &);

  bool write_bin_object_file(
    const std::string &file_name,
    const goto_modelt &src_goto_model)
  {
    if(write_bin_object_file(
         file_name,
         src_goto_model,
         validate_goto_model,
         log.get_message_handler()))
    {
      return true;
    }

    wrote_object = true;

    return false;
  }

  void add_compiler_specific_defines() const;

  void convert_symbols(goto_modelt &);

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
