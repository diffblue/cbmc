/*******************************************************************\
 
Module: Compile and link source and object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_COMPILE_H
#define GOTO_CC_COMPILE_H

#include <symbol.h>
#include <replace_symbol.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>

class compilet:public language_uit
{
public:
  namespacet ns;
  goto_functionst compiled_functions;
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
  std::string output_file_object, output_file_executable;

  compilet(cmdlinet &_cmdline);
  
  ~compilet();
  
  bool add_input_file(const std::string &);
  bool find_library(const std::string &);
  bool is_elf_file(const std::string &);

  bool parse(const std::string &filename);
  bool parse_stdin();
  bool doit();
  bool compile();
  bool link();

  bool parse_source(const std::string &);
  bool read_object(const std::string &, goto_functionst &);

  bool write_object_file( const std::string &, const symbol_tablet &, 
                          goto_functionst &);
  bool write_bin_object_file( const std::string&, const symbol_tablet &, 
                              goto_functionst& );    

protected:
  cmdlinet &cmdline;
  
  unsigned function_body_count( const goto_functionst &functions );
  
  void add_compiler_specific_defines(class configt &config) const;

  bool link_functions(
    symbol_tablet &dest_symbol_table,
    goto_functionst &dest_functions,
    symbol_tablet &src_symbol_table,
    goto_functionst &src_functions,
    const replace_symbolt &replace_symbol);
  
  void replace_symbols_in_function(
    goto_functionst::goto_functiont &function,
    const replace_symbolt &replace_symbol) const;

  void convert_symbols(goto_functionst &dest);
};

std::string get_base_name(const std::string &);

#endif /*COMPILE_H_*/
