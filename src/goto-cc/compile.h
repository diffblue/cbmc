/*******************************************************************\
 
Module: Compile and link source and object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_COMPILE_H
#define GOTO_CC_COMPILE_H

#include <symbol.h>
#include <replace_symbol.h>
#include <options.h>

#include <langapi/language_ui.h>
#include <goto-programs/goto_functions.h>

class compilet:public language_uit
{
public:
  optionst options;
  namespacet ns;
  goto_functionst compiled_functions;
  bool echo_file_name;
  std::string working_directory;
  
  enum { PREPROCESS_ONLY, // gcc -E
         COMPILE_ONLY, // gcc -c, gcc -S
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
  
  #if 0
  std::string &escape(std::string &);
  static unsigned subgraphscount;

  void write_edge( std::ostream&,
                   const goto_programt::instructiont&,
                   const goto_programt::instructiont&,
                   const std::string&);

  void find_next( const goto_programt::instructionst&,
                  const goto_programt::const_targett&,
                  std::set<goto_programt::const_targett>&,
                  std::set<goto_programt::const_targett>&);
  #endif
                  
  void show_function_table();
  
  #if 0
  std::list<exprt> function_calls;
  std::list<exprt> clusters;
  bool write_dot_header( const std::string&, std::ofstream& );
  void write_dot_subgraph( std::ostream&, 
                           const std::string&, 
                           goto_programt&);
  void do_dot_function_calls( std::ostream & );
  #endif
  
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
