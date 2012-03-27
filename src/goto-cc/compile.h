/*******************************************************************\
 
Module: Compile and link source and object files.
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_COMPILE_H
#define GOTO_CC_COMPILE_H

#include <symbol.h>
#include <xml.h>
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
  bool act_as_ld, only_preprocess, echo_file_name;
  std::string working_directory;

  std::list<std::string> library_paths;
  std::list<std::string> source_files;
  std::list<std::string> object_files;
  std::list<std::string> libraries;
  std::list<std::string> tmp_dirs;
  std::list<irep_idt> seen_modes;

  std::string object_file_extension;
  std::string output_file_object, output_file_executable;
  bool doLink;

  compilet(cmdlinet &_cmdline);
  
  ~compilet();
  
  bool add_input_file(const std::string &);
  bool find_library(const std::string &);
  bool is_xml_file(const std::string &);
  bool is_binary_file(const std::string &);
  bool is_elf_file(const std::string &);

  bool parse(const std::string &filename);
  bool parse_stdin();
  bool doit();
  bool compile();
  bool link();

  bool parse_source(const std::string &);
  bool read_object(const std::string &, goto_functionst &);

  bool write_object_file( const std::string &, const contextt &, 
                          goto_functionst &);
  bool write_xml_object_file( const std::string&, const contextt &, 
                              goto_functionst& );
  bool write_bin_object_file( const std::string&, const contextt &, 
                              goto_functionst& );    

protected:
  cmdlinet &cmdline;
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
                  
  void show_function_table();
  
  std::list<exprt> function_calls;
  std::list<exprt> clusters;
  bool write_dot_header( const std::string&, std::ofstream& );
  void write_dot_subgraph( std::ostream&, 
                           const std::string&, 
                           goto_programt&);
  void do_dot_function_calls( std::ostream & );
  unsigned function_body_count( const goto_functionst &functions );
  
  void add_compiler_specific_defines(configt &config) const;

  bool link_functions(
    contextt &context,
    goto_functionst &functions,
    contextt &temp_context,
    goto_functionst &temp_functions,
    replace_symbolt &replace_symbol);
  
  void replace_symbols_in_function(
    goto_functionst::function_mapt::iterator it,
    replace_symbolt &replace_symbol) const;

  void convert_symbols(goto_functionst &dest);
};

std::string get_base_name(const std::string &);

#endif /*COMPILE_H_*/
