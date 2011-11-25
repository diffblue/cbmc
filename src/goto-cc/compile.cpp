/*******************************************************************\

Module: Compile and link source and object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifdef __linux__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef __FreeBSD_kernel__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef __MACH__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#ifdef __CYGWIN__
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#endif

#include <fstream>
#include <sstream>
#include <cstdlib>
#include <algorithm>

#include <config.h>
#include <tempdir.h>
#include <replace_symbol.h>
#include <base_type.h>
#include <xml.h>
#include <i2string.h>
#include <cmdline.h>

#include <ansi-c/ansi_c_language.h>
#include <ansi-c/c_link_class.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_function_serialization.h>
#include <goto-programs/read_bin_goto_object.h>
#include <goto-programs/write_goto_binary.h>

#include <langapi/mode.h>

#include <irep_serialization.h>
#include <symbol_serialization.h>

#include "xml_binaries/xml_irep_hashing.h"
#include "xml_binaries/xml_symbol_hashing.h"
#include "xml_binaries/xml_goto_function_hashing.h"
#include "xml_binaries/read_goto_object.h"

#include "get_base_name.h"
#include "compile.h"
#include "version.h"

#ifdef _WIN32
#include <io.h>
#include <windows.h>
#include <direct.h>
#include <errno.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#endif

#define DOTGRAPHSETTINGS  "color=black;" \
                          "orientation=portrait;" \
                          "fontsize=20;"\
                          "compound=true;"\
                          "size=\"30,40\";"\
                          "ratio=compress;"

unsigned compilet::subgraphscount;

/*******************************************************************\

Function: compilet::doit

  Inputs: none

 Outputs: true on error, false otherwise

 Purpose: reads and source and object files, compiles and links them
          into goto program objects.

\*******************************************************************/

bool compilet::doit()
{
  std::string error_label;

  options.set_option("bounds-check", !cmdline.isset("no-bounds-check"));
  options.set_option("div-by-zero-check", !cmdline.isset("no-div-by-zero-check"));
  options.set_option("pointer-check", !cmdline.isset("no-pointer-check"));
  options.set_option("assertions", !cmdline.isset("no-assertions"));
  options.set_option("assumptions", !cmdline.isset("no-assumptions"));
  options.set_option("simplify", !cmdline.isset("no-simplify"));
  options.set_option("overflow-check", cmdline.isset("overflow-check"));

  // we do want the assertions
  optionst options;
  options.set_option("assertions", true);
  options.set_option("assumptions", true);
  options.set_option("error-label", error_label);

  compiled_functions.clear();

  add_compiler_specific_defines(config);

  // Parse commandline for source and object file names
  for(unsigned i=0; i<_cmdline.args.size(); i++)
    if(add_input_file(_cmdline.args[i]))
      return true;

  for(std::list<std::string>::const_iterator it = libraries.begin();
      it!=libraries.end();
      it++)
  {
    if(!find_library(*it))
      warning(std::string("Library not found: ") + *it + " (ignoring)");
  }

  // Work through the given source files
  print(8, "No. of source files: " +
    i2string((unsigned long) source_files.size()));

  print(8, "No. of object files: " +
    i2string((unsigned long) object_files.size()));

  if(source_files.size()==0 && object_files.size()==0)
  {
    error("no input files");
    return true;
  }

  if(act_as_ld && source_files.size()>0)
  {
    error("ld cannot link source files");
    return true;
  }

  if(only_preprocess && object_files.size()>0)
  {
    error("cannot preprocess object files");
    return true;
  }

  if(source_files.size()>0)
    if(compile()) return true;

  if(only_preprocess) return false;

  if(doLink)
  {
    if(link()) return true;
  }
  
  return false;
}

/*******************************************************************\

Function: compilet::add_input_file

  Inputs: none

 Outputs: false on success, true on error.

 Purpose: puts input file names into a list and does preprocessing for
          libraries.

\*******************************************************************/

bool compilet::add_input_file(const std::string &file_name)
{
  size_t r=file_name.rfind('.', file_name.length()-1);

  if(r!=std::string::npos)
  {
    std::string ext = file_name.substr(r+1, file_name.length());

    if(ext=="a")
    {
      #ifdef _WIN32
      char td[MAX_PATH];
      #else
      char td[] = "goto-cc.XXXXXX";
      #endif

      std::string tstr = get_temporary_directory(td);

      if(tstr=="")
      {
        error("Cannot create temporary directory.");
        return true;
      }

      tmp_dirs.push_back(tstr);
      std::stringstream cmd("");
      if(chdir(tmp_dirs.back().c_str())!=0)
      {
        error("Cannot switch to temporary directory.");
        return true;
      }
      
      #ifdef _WIN32
      if (file_name[0]!='/' && file_name[1]!=':')
      #else
      if (file_name[0]!='/')
      #endif
      {
        cmd << "ar t " <<
        #ifdef _WIN32
          working_directory << "\\" << file_name;
        #else
          working_directory << "/" << file_name;
        #endif
      }
      else
      {
        cmd << "ar t " << file_name;
      }

      FILE *stream = popen(cmd.str().c_str(), "r");
      if (stream!=NULL)
      {
        std::string line;
        char ch;
        while((ch=fgetc(stream))!=EOF)
        {
          if(ch!='\n' && ch!=EOF)
          {
            line += ch;
          }
          else
          {
            std::string t;
            #ifdef _WIN32
            t = tmp_dirs.back() + '\\' + line;
            #else
            t = tmp_dirs.back() + '/' + line;
            #endif
            object_files.push_back(t);
            line = "";
          }
        }
      }
      pclose(stream);
      cmd.str("");
      #ifdef _WIN32
      if(file_name[0]!='/' && file_name[1]!=':')
      #else
      if(file_name[0]!='/')
      #endif
      {
        cmd << "ar x " <<
        #ifdef _WIN32
          working_directory << "\\" << file_name;
        #else
          working_directory << "/" << file_name;
        #endif
      }
      else
      {
        cmd << "ar x " << file_name;
      }

      stream = popen(cmd.str().c_str(), "r");
      pclose(stream);

      if(chdir(working_directory.c_str())!=0)
        error("Could not change back to working directory.");
    }
    else if(ext=="so")
    {
      if(cmdline.isset("xml"))
      {
        if(is_xml_file(file_name))
          object_files.push_back(file_name);
      }
      else
      {
        if(is_binary_file(file_name))
          object_files.push_back(file_name);
      }
    }
    else if(ext==object_file_extension ||
            ext=="la" || ext=="lo") // Object file recognized
      object_files.push_back(file_name);
    else // assume source file
      source_files.push_back(file_name);
  }
  else
  {
    // don't care about no extensions
    source_files.push_back(file_name);
  }

  return false;
}

/*******************************************************************\

Function: compilet::find_library

  Inputs: library name

 Outputs: true if found, false otherwise

 Purpose: tries to find a library object file that matches the given
          library name.

\*******************************************************************/

bool compilet::find_library(const std::string &name)
{
  std::string tmp;
  for(std::list<std::string>::const_iterator
      it=library_paths.begin();
      it!=library_paths.end();
      it++)
  {
    #ifdef _WIN32
    tmp = *it + "\\lib";
    #else
    tmp = *it + "/lib";
    #endif
    std::ifstream in((tmp+name+".a").c_str());
    if(in.is_open())
      add_input_file(tmp+name+".a");
    else
    {
      std::string libname = tmp+name+".so";

      if(is_elf_file(libname))
          std::cout << "Warning: Cannot read ELF library " << libname << "."
                    << std::endl;

      if(cmdline.isset("xml"))
      {
        if(is_xml_file(libname))
          add_input_file(libname);
        else
          return false;
      }
      else
      {
        if(is_binary_file(libname))
          add_input_file(libname);
        else
          return false;
      }
    }
  }
  
  return true;
}

/*******************************************************************\

Function: compilet::is_xml_file

  Inputs: file name

 Outputs: true if the given file name exists and is an xml file,
          false otherwise

 Purpose: checking if we can load an object file

\*******************************************************************/

bool compilet::is_xml_file(const std::string &file_name)
{
  std::fstream in;
  in.open(file_name.c_str(), std::ios::in);

  if(in.is_open())
  {
    char buf[5];
    for (unsigned i=0; i<5; i++)
      buf[i] = in.get();
    if (buf[0]=='<' && buf[1]=='?' &&
        buf[2]=='x' && buf[3]=='m' && buf[4]=='l')
      return true;
  }

  return false;
}

/*******************************************************************\

Function: compilet::is_binary_file

  Inputs: file name

 Outputs: true if the given file name exists and is a (goto-)binary file,
          false otherwise

 Purpose: checking if we can load an object file

\*******************************************************************/

bool compilet::is_binary_file(const std::string &file_name)
{
  std::fstream in;
  in.open(file_name.c_str(), std::ios::in);

  if(in.is_open())
  {
    char buf[3];
    for (unsigned i=0; i<3; i++)
      buf[i] = in.get();
    if (buf[0]=='G' && buf[1]=='B' && buf[2]=='F')
      return true;
  }
  
  return false;
}

/*******************************************************************\

Function: compilet::is_elf_file

  Inputs: file name

 Outputs: true if the given file name exists and is an ELF file,
          false otherwise

 Purpose: checking if we can load an object file

\*******************************************************************/

bool compilet::is_elf_file(const std::string &file_name)
{
  std::fstream in;

  in.open(file_name.c_str(), std::ios::in);
  if(in.is_open())
  {
    char buf[4];
    for (unsigned i=0; i<4; i++)
      buf[i] = in.get();
    if (buf[0]==0x7f && buf[1]=='E' &&
        buf[2]=='L' && buf[3]=='F')
      return true;
  }

  return false;
}

/*******************************************************************\

Function: compilet::link

  Inputs: none

 Outputs: true on error, false otherwise

 Purpose: parses object files and links them

\*******************************************************************/

bool compilet::link()
{
  // "compile" hitherto uncompiled functions
  print(8, "Compiling functions");
  convert_symbols(compiled_functions);

  if(cmdline.isset("partial-inlining"))
  {
    // inline those functions marked as "inlined"
    // we no longer do partial inlining by default -- can just as
    // well be done in the backend
    print(8, "Partial inlining");
    goto_partial_inline(
      compiled_functions,
      ns,
      get_message_handler());
  }

  // parse object files
  while(object_files.size()>0)
  {
    std::string file_name=object_files.front();
    object_files.pop_front();

    if(parse_object(file_name, compiled_functions))
      return true;
  }

  if(cmdline.isset("show-symbol-table"))
  {
    show_symbol_table();
    return true;
  }

  if(cmdline.isset("show-function-table"))
  {
    show_function_table();
    return true;
  }

  // finalize
  contextt::symbolst::iterator it_main=
    context.symbols.find("c::"+config.main);

  if((!act_as_ld || it_main!=context.symbols.end()) &&
     !cmdline.isset("static") && !cmdline.isset("shared"))
  {
    print(8, "Finalizing");

    forall_symbols(it, context.symbols)
    {
      const symbolt &symbol = it->second;
      if (symbol.mode!="" &&
            find(seen_modes.begin(), seen_modes.end(), symbol.mode)
            == seen_modes.end())
      {
        seen_modes.push_back(symbol.mode);
      }
    }
    
    if(seen_modes.empty())
    {
      if(!source_files.empty())
      {
        error("no modes found!");
        return true;
      }
    }
    else
    {
      // Hackfix for C++
      std::list<irep_idt>::iterator cpp =
        find(seen_modes.begin(), seen_modes.end(), "cpp");

      std::list<irep_idt>::iterator c =
        find(seen_modes.begin(), seen_modes.end(), "C");

      if (c!=seen_modes.end() && cpp!=seen_modes.end())
        seen_modes.erase(c);

      std::list<irep_idt>::iterator it = seen_modes.begin();
      for (; it!=seen_modes.end(); it++)
      {
        languaget *language=get_language_from_mode(*it);
        if (language)
        {
          if (language->final(context, ui_message_handler))
            return true;
        }
        else
        {
          error("unknown language mode '" +id2string(*it)+ "'");
          return true;
        }
      }
    }

    // check for main
    contextt::symbolst::iterator i=
      context.symbols.find("main");

    if(i==context.symbols.end())
    {
      error("'main' symbol not found");
      return true;
    }

    // final may add some more functions.
    convert_symbols(compiled_functions);
  }

  if(write_object_file(output_file_executable, context, compiled_functions))
    return true;

  return false;
}

/*******************************************************************\

Function: compilet::compile

  Inputs: none

 Outputs: true on error, false otherwise

 Purpose: parses source files and writes object files, or keeps the
          symbols in the context depending on the doLink flag.

\*******************************************************************/

bool compilet::compile()
{
  while(!source_files.empty())
  {
    std::string file_name=source_files.front();
    source_files.pop_front();
    
    // Visual Studio always prints the name of the file it's doing
    if(echo_file_name)
      status(file_name);

    bool r=parse_source(file_name); // don't break the program!

    if(!r && !doLink && !only_preprocess)
    {
      // output an object file for every source file

      // "compile" functions
      convert_symbols(compiled_functions);

      if(cmdline.isset("show-symbol-table"))
      {
        show_symbol_table();
        return true;
      }

      if(cmdline.isset("show-function-table"))
      {
        show_function_table();
        return true;
      }

      std::string cfn;
      
      if(output_file_object=="")
      {
        if(cmdline.isset('S')) // compile, but don't assemble
          cfn=get_base_name(file_name) + ".s";
        else
          cfn=get_base_name(file_name) + "." + object_file_extension;
      }
      else
      {
        cfn=output_file_object;
      }

      if(write_object_file(cfn, context, compiled_functions))
        return true;

      context.clear(); // clean symbol table for next source file.
      compiled_functions.clear();
    }
    
    if(r) return true; // parser/typecheck error
  }
  
  return false;
}

/*******************************************************************\

Function: compilet::parse

  Inputs: file_name

 Outputs: true on error, false otherwise

 Purpose: parses a source file (low-level parsing)

\*******************************************************************/

bool compilet::parse(const std::string &file_name)
{
  if(file_name=="-") return parse_stdin();

  std::ifstream infile(file_name.c_str());

  if(!infile)
  {
    error("failed to open input file", file_name);
    return true;
  }

  languaget *languagep=get_language_from_filename(file_name);

  if(languagep==NULL)
  {
    error("failed to figure out type of file", file_name);
    return true;
  }

  languaget &language=*languagep;
  language_filet language_file;

  std::pair<language_filest::filemapt::iterator, bool>
  res=language_files.filemap.insert(
    std::pair<std::string, language_filet>(file_name, language_file));

  language_filet &lf=res.first->second;
  lf.filename=file_name;
  lf.language=languagep;

  print(8, "Parsing: "+file_name);

  if(only_preprocess)
  {
    std::ostream *os = &std::cout;
    std::ofstream ofs;

    if(cmdline.isset('o'))
    {
      ofs.open(cmdline.getval('o'));
      os = &ofs;

      if(!ofs.is_open())
      {
        error(std::string("failed to open output file `")+
              cmdline.getval('o')+"'");
        return true;
      }
    }

    language.preprocess(infile, file_name, *os, get_message_handler());
  }
  else
  {
    if(language.parse(infile, file_name, get_message_handler()))
    {
      if(get_ui()==ui_message_handlert::PLAIN)
        error("PARSING ERROR");
      return true;
    }
  }

  lf.get_modules();
  return false;
}

/*******************************************************************\

Function: compilet::parse_stdin

  Inputs: file_name

 Outputs: true on error, false otherwise

 Purpose: parses a source file (low-level parsing)

\*******************************************************************/

bool compilet::parse_stdin()
{
  ansi_c_languaget language;

  print(8, "Parsing: (stdin)");

  if(only_preprocess)
  {
    std::ostream *os = &std::cout;
    std::ofstream ofs;

    if(cmdline.isset('o'))
    {
      ofs.open(cmdline.getval('o'));
      os = &ofs;

      if(!ofs.is_open())
      {
        error(std::string("failed to open output file `")+
              cmdline.getval('o'));
        return true;
      }
    }

    language.preprocess(std::cin, "", *os, get_message_handler());
  }
  else
  {
    if(language.parse(std::cin, "", get_message_handler()))
    {
      if(get_ui()==ui_message_handlert::PLAIN)
        error("PARSING ERROR");
      return true;
    }
  }

  return false;
}

/*******************************************************************\

Function: compilet::write_object_file

  Inputs: file_name, functions table

 Outputs: true on error, false otherwise

 Purpose: writes the goto functions in the function table to a
          binary format object file.

\*******************************************************************/

bool compilet::write_object_file(
  const std::string &file_name,
  const contextt &lcontext,
  goto_functionst &functions)
{
  if(cmdline.isset("xml"))
    return write_xml_object_file(file_name, lcontext, functions);
  else
    return write_bin_object_file(file_name, lcontext, functions);
}

/*******************************************************************\

Function: compilet::write_bin_object_file

  Inputs: file_name, functions table

 Outputs: true on error, false otherwise

 Purpose: writes the goto functions in the function table to a
          binary format object file.

\*******************************************************************/

bool compilet::write_bin_object_file(
  const std::string &file_name,
  const contextt &lcontext,
  goto_functionst &functions)
{
  print(8, "Writing binary format object `" + file_name + "'");

  // symbols
  print(8, "Symbols in table: "+
           i2string((unsigned long)lcontext.symbols.size()));

  std::ofstream outfile(file_name.c_str(), std::ios::binary);

  if(!outfile.is_open())
  {
    error("Error opening file `"+file_name+"'");
    return true;
  }

  if(write_goto_binary(outfile, lcontext, functions))
    return true;

  unsigned cnt=function_body_count(functions);

  debug("Functions: "+i2string(functions.function_map.size())+"; "+
        i2string(cnt)+" have a body.");

  outfile.close();

  if(cmdline.isset("dot"))
  {
    std::ofstream dgf;
    write_dot_header(file_name, dgf);

    for (goto_functionst::function_mapt::iterator it=
           functions.function_map.begin();
         it!=functions.function_map.end();
         it++)
    {
      if (it->second.body_available)
          write_dot_subgraph(dgf, id2string(it->first), it->second.body);
    }

    do_dot_function_calls(dgf);
    dgf << "}" << std::endl;
    dgf.close();
  }

  return false;
}

/*******************************************************************\

Function: compilet::write_xml_object_file

  Inputs: file_name, functions table

 Outputs: true on error, false otherwise

 Purpose: writes the goto functions in the function table to an xml
          object file

\*******************************************************************/

bool compilet::write_xml_object_file(
  const std::string &file_name,
  const contextt &lcontext,
  goto_functionst &functions)
{
  print(8, "Writing xml format object " + file_name);

  std::ofstream f(file_name.c_str());
  if(!f.is_open())
  {
    error("Error opening file " + file_name);
    return true;
  }

  f << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" << std::endl;
  f << "<goto-object version=\"" << XML_VERSION << "\">" << std::endl;
  f << " <irep_hash_map>" << std::endl;

  xml_irep_convertt::ireps_containert irepc;
  xml_irep_convertt irepconverter(irepc);
  xml_symbol_convertt symbolconverter(irepc);
  xml_goto_function_convertt gfconverter(irepc);

  xmlt syms("symbols");
  print(8, "Symbols in table: " + i2string((unsigned long) lcontext.symbols.size()));
  forall_symbols(it, lcontext.symbols)
  {
    const symbolt &sym = it->second;
    symbolconverter.convert(sym, syms);
  }

  xmlt funs("functions");
  if (verbosity>=9)
  {
    std::cout << "Functions: " << functions.function_map.size() << "; ";
    std::cout << function_body_count(functions) << " have a body." << std::endl;
  }

  std::ofstream dgf;
  if (cmdline.isset("dot"))
    write_dot_header(file_name, dgf);
    for ( goto_functionst::function_mapt::iterator it=functions.function_map.begin();
          it != functions.function_map.end();
          it++)
    {
      if (it->second.body_available)
      {
        xmlt &fun = funs.new_element("function");
        fun.set_attribute("name", id2string(it->first));
        gfconverter.convert(it->second, fun);
        if (dgf.is_open())
          write_dot_subgraph(dgf, id2string(it->first), it->second.body);
      }
    }

  if (dgf.is_open())
  {
    do_dot_function_calls(dgf);
    dgf << "}" << std::endl;
    dgf.close();
  }

  irepconverter.output_map(f, 2);
  f << " </irep_hash_map>" << std::endl;
  syms.output(f, 1);
  funs.output(f, 1);
  f << "</goto-object>";
  f.close();
  return false;
}

/*******************************************************************\

Function: compilet::write_dot_subgraph

  Inputs: output stream, name and goto program

 Outputs: true on error, false otherwise

 Purpose: writes the dot graph that corresponds to the goto program
          to the output stream.

\*******************************************************************/

void compilet::write_dot_subgraph(
  std::ostream &out,
  const std::string &name,
  goto_programt &goto_program)
{
  clusters.push_back(exprt("cluster"));
  clusters.back().set("name", name);
  clusters.back().set("nr", subgraphscount);

  out << "subgraph \"cluster_" << name << "\" {" << std::endl;
  out << "label=\"" << name << "\";" << std::endl;

  const goto_programt::instructionst& instructions =
    goto_program.instructions;  
  
  if (instructions.size()==0)
  {
    out << "Node_" << subgraphscount << "_0 " <<
      "[shape=Mrecord,fontsize=22,label=\"?\"];" << std::endl;
  }
  else
  {
    std::set<goto_programt::const_targett> seen;
    goto_programt::const_targetst worklist;
    worklist.push_back(instructions.begin());
    
    while (!worklist.empty())
    {
      goto_programt::const_targett it=worklist.front();
      worklist.pop_front();
      
      if(it==instructions.end() ||
         seen.find(it)!=seen.end()) continue;
          
      std::stringstream tmp("");
      if(it->is_goto())
      {
        if (it->guard.is_true())
          tmp.str("Goto");
        else
        {
          std::string t = from_expr(ns, "", it->guard);
          while (t[ t.size()-1 ]=='\n')
            t = t.substr(0,t.size()-1);
          tmp << escape(t) << "?";
        }
      }
      else if (it->is_assume())
      {
        std::string t = from_expr(ns, "", it->guard);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp << "Assume\\n(" << escape(t) << ")";
      }
      else if (it->is_assert())
      {
        std::string t = from_expr(ns, "", it->guard);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp << "Assert\\n(" << escape(t) << ")";
      }
      else if (it->is_skip())
        tmp.str("Skip");
      else if (it->is_end_function())            
        tmp.str("End of Function");      
      else if (it->is_location())
        tmp.str("Location");
      else if (it->is_dead())
        tmp.str("Dead");
      else if (it->is_atomic_begin())
        tmp.str("Atomic Begin");
      else if (it->is_atomic_end())
        tmp.str("Atomic End");
      else if (it->is_function_call())
      {
        std::string t = from_expr(ns, "", it->code);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp.str(escape(t));
        
        exprt fc;
        std::stringstream ss;
        ss << "Node_" << subgraphscount << "_" << it->location_number;
        fc.operands().push_back(exprt(ss.str()));
        fc.operands().push_back(it->code.op1());  
        function_calls.push_back(fc);
      }
      else if (it->is_assign() ||
               it->is_return() ||
               it->is_other())      
      {
        std::string t = from_expr(ns, "", it->code);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp.str(escape(t));
      }
      else if (it->is_start_thread())
        tmp.str("Start of Thread");
      else if (it->is_end_thread())
        tmp.str("End of Thread");
      else if (it->is_throw())
        tmp.str("THROW");
      else if (it->is_catch())
        tmp.str("CATCH");
      else
        tmp.str("UNKNOWN");

      out << "Node_" << subgraphscount << "_" << it->location_number;
      out << " [shape="; 
      if (it->is_goto() && !it->guard.is_true() && !it->guard.is_false())
        out << "diamond";
      else
        out <<"Mrecord";
      out << ",fontsize=22,label=\"";
      out << tmp.str();
      out << "\"];" << std::endl;

      std::set<goto_programt::const_targett> tres;
      std::set<goto_programt::const_targett> fres;          
      find_next(instructions, it, tres, fres);

      std::string tlabel="true";
      std::string flabel="false";
      if (fres.size()==0 || tres.size()==0)
      {
        tlabel="";
        flabel="";
      }
            
      typedef std::set<goto_programt::const_targett> t;          
      
      for (t::iterator trit=tres.begin();
           trit!=tres.end();
           trit++)
        write_edge(out, *it, **trit, tlabel);
      for (t::iterator frit=fres.begin();
          frit!=fres.end();
          frit++)
        write_edge(out, *it, **frit, flabel);
    
      seen.insert(it);
      goto_programt::const_targetst temp;
      goto_program.get_successors(it, temp);
      worklist.insert(worklist.end(), temp.begin(), temp.end());
    }
  }
  
  out << "}" << std::endl;
  subgraphscount++;
}

/*******************************************************************\

Function: compilet::do_dot_function_calls

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::do_dot_function_calls(std::ostream &out)
{
  for (std::list<exprt>::const_iterator it=function_calls.begin();
       it!=function_calls.end();
       it++)
  {
    std::list<exprt>::const_iterator cit=clusters.begin();
    for (;cit!=clusters.end();cit++)
      if (cit->get("name")==it->op1().get(ID_identifier))
        break;

    if (cit!=clusters.end())
    {
      out << it->op0().id() <<
        " -> " "Node_" << cit->get("nr") << "_0" <<
        " [lhead=\"cluster_" << it->op1().get(ID_identifier) << "\"," <<
        "color=blue];" << std::endl;
    }
    else
    {
      out << "subgraph \"cluster_" << it->op1().get(ID_identifier) <<
        "\" {" << std::endl;
      out << "rank=sink;"<<std::endl;
      out << "label=\"" << it->op1().get(ID_identifier) << "\";" << std::endl;
      out << "Node_" << subgraphscount << "_0 " <<
        "[shape=Mrecord,fontsize=22,label=\"?\"];"
          << std::endl;
      out << "}" << std::endl;
      clusters.push_back(exprt("cluster"));
      clusters.back().set("name", it->op1().get(ID_identifier));
      clusters.back().set("nr", subgraphscount);
      out << it->op0().id() <<
        " -> " "Node_" << subgraphscount << "_0" <<
        " [lhead=\"cluster_" << it->op1().get("identifier") << "\"," <<
        "color=blue];" << std::endl;
      subgraphscount++;
    }
  }
}

/*******************************************************************\

Function: compilet::find_next

  Inputs: instructions, instruction iterator, true results and
          false results

 Outputs: none

 Purpose: finds an instructions successors (for goto graphs)

\*******************************************************************/

void compilet::find_next(
  const goto_programt::instructionst &instructions,
  const goto_programt::const_targett &it,
  std::set<goto_programt::const_targett> &tres,
  std::set<goto_programt::const_targett> &fres)
{
  if (it->is_goto() && !it->guard.is_false())
  {
    goto_programt::targetst::const_iterator gtit = it->targets.begin();
    for (; gtit!=it->targets.end(); gtit++)
      tres.insert((*gtit));
  }

  if (it->is_goto() && it->guard.is_true())
    return;
  
  goto_programt::const_targett next = it; next++;
  if (next!=instructions.end())
    fres.insert(next);
}

/*******************************************************************\

Function: compilet::write_edge

  Inputs: output stream, from, to and a label

 Outputs: none

 Purpose: writes an edge from the from node to the to node and with
          the given label to the output stream (dot format)

\*******************************************************************/

void compilet::write_edge(
  std::ostream &out,
  const goto_programt::instructiont &from,
  const goto_programt::instructiont &to,
  const std::string &label)
{
  out << "Node_" << subgraphscount << "_" << from.location_number;
  out << " -> ";
  out << "Node_" << subgraphscount << "_" << to.location_number << " ";
  if (label!="")
    {
      out << "[fontsize=20,label=\"" << label << "\"";
      if (from.is_backwards_goto() &&
          from.location_number > to.location_number)
        out << ",color=red";
      out << "]";
    }
  out << ";" << std::endl;
}

/*******************************************************************\

Function: compilet::escape

  Inputs: a string

 Outputs: the escaped string

 Purpose: escapes a string. beware, this might not work for all
          kinds of strings.

\*******************************************************************/

std::string &compilet::escape(std::string &str)
{
  for(unsigned i=0; i<str.size(); i++)
  {
    if(str[i]=='\n')
    {
      str[i] = 'n';
      str.insert(i, "\\");
    }
    else if(str[i]=='\"' ||
            str[i]=='|' ||
            str[i]=='\\' ||
            str[i]=='>' ||
            str[i]=='<' ||
            str[i]=='{' ||
            str[i]=='}')
    {
      str.insert(i, "\\");
      i++;
    }
  }

  return str;
}

/*******************************************************************\

Function: compilet::parse_source

  Inputs: file_name

 Outputs: true on error, false otherwise

 Purpose: parses a source file

\*******************************************************************/

bool compilet::parse_source(const std::string &file_name)
{
  if(parse(file_name))
    return true;
    
  if(typecheck()) // we just want to typecheck this one file here
    return true;
    
  // so we remove it from the list afterwards
  language_files.filemap.erase(file_name);
  return false;
}

/*******************************************************************\

Function: compilet::parse_object

  Inputs: a file_name

 Outputs: true on error, false otherwise

 Purpose: parses an object file

\*******************************************************************/

bool compilet::parse_object(
  const std::string &file_name,
  goto_functionst &functions)
{
  std::ifstream infile;
  if(cmdline.isset("xml"))
    infile.open(file_name.c_str());
  else
    infile.open(file_name.c_str(), std::ios::binary);

  if(!infile)
  {
    error("failed to open input file", file_name);
    return true;
  }

  print(8, "Parsing: " + file_name);

  // we parse to a temporary context
  contextt temp_context;
  goto_functionst temp_functions;
  std::list<irep_idt> seen_modes;

  if(cmdline.isset("xml"))
  {
    if(read_goto_object(infile, file_name, temp_context,
                         temp_functions, *message_handler))
      return true;
  }
  else
  {
    if(read_bin_goto_object(infile, file_name, temp_context,
                             temp_functions, *message_handler))
      return true;
  }

  for(contextt::symbolst::const_iterator
      it=temp_context.symbols.begin();
      it!=temp_context.symbols.end();
      it++)
  {
    if (  it->second.mode!="" &&
          find(  seen_modes.begin(),
                 seen_modes.end(),
                 it->second.mode)
          == seen_modes.end())
     {
        seen_modes.push_back(it->second.mode);
     }
  }

  std::list<irep_idt>::const_iterator cpp =
    find(seen_modes.begin(), seen_modes.end(), "cpp");
  std::list<irep_idt>::iterator c =
    find(seen_modes.begin(), seen_modes.end(), "C");

  if(c!=seen_modes.end() && cpp!=seen_modes.end())
  {
    seen_modes.erase(c);
  }

  if(seen_modes.size()!=1)
  {
    std::cerr << "Multilanguage linking not supported." << std::endl;
    return true;
  }

  // hardwired to C linking

  c_linkt c_link(context, temp_context, ui_message_handler);

  if(c_link.typecheck_main())
    return true;
  
  if(link_functions(context, functions,
                    temp_context, temp_functions,
                    c_link.replace_symbol))
    return true;

  return false;
}

/*******************************************************************\

Function: compilet::show_function_table

  Inputs: none

 Outputs: nothing

 Purpose: prints the function table to stdout

\*******************************************************************/

void compilet::show_function_table()
{
  for(goto_functionst::function_mapt::const_iterator
      i=compiled_functions.function_map.begin();
      i!=compiled_functions.function_map.end();
      i++)
  {
    std::cout << i->first << std::endl;
  }
}

/*******************************************************************\

Function: compilet::compilet

  Inputs: none

 Outputs: nothing

 Purpose: constructor

\*******************************************************************/

compilet::compilet(cmdlinet &_cmdline):
  language_uit("goto-cc " GOTOCC_VERSION, _cmdline),
  ns(context),
  cmdline(_cmdline)
{
  doLink=false;
  act_as_ld=false;
  only_preprocess=false;
  echo_file_name=false;
  subgraphscount=0;

  unsigned bsize=50;
  char *buf = (char*) malloc(sizeof(char)*bsize);
  errno=0;
  while(buf && getcwd(buf, bsize-1)==NULL && errno==ERANGE)
  {
    bsize*=2;
    buf = (char*) realloc(buf, sizeof(char)*bsize);
  }
  working_directory = buf;
  if(buf) free(buf);
}

/*******************************************************************\

Function: compilet::~compilet

  Inputs: none

 Outputs: nothing

 Purpose: cleans up temporary files

\*******************************************************************/

compilet::~compilet()
{
  // clean up temp dirs

  for (std::list<std::string>::const_iterator it = tmp_dirs.begin();
       it!=tmp_dirs.end();
       it++)
  {
    #ifdef _WIN32
    
    std::string pattern=*it+"\\*";
    
    struct _finddata_t info;
    
    intptr_t handle=_findfirst(pattern.c_str(), &info);
    
    if(handle!=-1)
    {
      unlink(info.name);
      
      while(_findnext(handle, &info)!=-1)
        unlink(info.name);
    }
    #else
    DIR *dir=opendir(it->c_str());

    if(dir!=NULL)
    {
      struct dirent *ent;

      while((ent=readdir(dir))!=NULL)
        remove((*it + "/" + ent->d_name).c_str());

      closedir(dir);
    }
    #endif

    rmdir(it->c_str());
  }
}

/*******************************************************************\

Function: compilet::write_dot_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool compilet::write_dot_header(
  const std::string &file_name,
  std::ofstream &dgf)
{
  std::string dgfilename = file_name + ".dot";
  if (verbosity>=9)
    status("Writing dot graph to " + dgfilename);
  dgf.open(dgfilename.c_str());
  if (!dgf.is_open())
  {
    error("Error opening file: " + dgfilename);
    return true;
  }
  dgf << "digraph G {" << std::endl;
  dgf << DOTGRAPHSETTINGS << std::endl;
  return false;
}

/*******************************************************************\

Function: compilet::function_body_count

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned compilet::function_body_count(const goto_functionst &functions)
{
  int fbs = 0;
  for ( goto_functionst::function_mapt::const_iterator it=
          functions.function_map.begin();
        it != functions.function_map.end();
        it++)
    if (it->second.body_available)
      fbs++;

  return fbs;
}

/*******************************************************************\

Function: compilet::link_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool compilet::link_functions(
  contextt &context,
  goto_functionst &functions,
  contextt &temp_context,
  goto_functionst &temp_functions,
  replace_symbolt &replace_symbol)
{
  // merge functions
  Forall_goto_functions(it, temp_functions)
  {
    goto_functionst::function_mapt::iterator fit=
        functions.function_map.find(it->first);

    if(fit==functions.function_map.end()) // fine
    {
      replace_symbols_in_function(it, replace_symbol);
      goto_functionst::goto_functiont &in_context=
          functions.function_map[it->first];

      in_context.body.swap(it->second.body);
      in_context.body_available=it->second.body_available;
      in_context.type=it->second.type;
    }
    else // collision!
    {
      goto_functionst::goto_functiont &in_context=
                                  functions.function_map[it->first];
      goto_functionst::goto_functiont &new_func=it->second;

      if(in_context.body.instructions.size()==0)
      {
        // the one with body wins!
        replace_symbols_in_function(it, replace_symbol);
        in_context.body.swap(new_func.body);
        in_context.body_available=new_func.body_available;
        in_context.type=new_func.type;
      }
      else if(new_func.body.instructions.size()==0)
      {
        // keep the old one
      }
      else if(in_context.type.get_bool("#inlined"))
      {
        // ok
      }
      else if(base_type_eq(in_context.type, new_func.type, ns))
      {
        // keep the one in in_context -- libraries come last!
        std::stringstream str;
        str << "warning: function `" << it->first << "' in module `" <<
          temp_context.symbols.begin()->second.module <<
          "' is shadowed by a definition in module `" <<
          context.symbols.begin()->second.module << "'";
        warning(str.str());
      }
      else
      {
        std::stringstream str;
        str << "error: duplicate definition of function `"
            << it->first
            << "'" << std::endl;
        str << "In module `" <<
            context.symbols.begin()->second.module
            << "' and module `" <<
            temp_context.symbols.begin()->second.module << "'";
        error(str.str());
        return true;
      }
    }
  }

  return false;
}

/*******************************************************************\

Function: compilet::replace_symbols_in_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::replace_symbols_in_function(
  goto_functionst::function_mapt::iterator it,
  replace_symbolt &replace_symbol) const
{
  goto_programt &program = it->second.body;
  replace_symbol.replace(it->second.type);

  Forall_goto_program_instructions(iit, program)
  {
    replace_symbol.replace(iit->code);
    replace_symbol.replace(iit->guard);
  }
}

/*******************************************************************\

Function: compilet::add_compiler_specific_defines

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::add_compiler_specific_defines(configt &config) const
{
  config.ansi_c.defines.push_back("__GOTO_CC_VERSION__=" GOTOCC_VERSION);
}

/*******************************************************************\

Function: compilet::convert_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void compilet::convert_symbols(goto_functionst &dest)
{
  goto_convert_functionst converter(context, options, dest,
                                    ui_message_handler);

  // the compilation may add symbols!

  contextt::symbolst::size_type before=0;
  
  while(before!=context.symbols.size())
  {
    before=context.symbols.size();

    typedef std::set<irep_idt> symbols_sett;
    symbols_sett symbols;
  
    Forall_symbols(it, context.symbols)
      symbols.insert(it->first);

    // the symbol table itertors aren't stable
    for(symbols_sett::const_iterator
        it=symbols.begin();
        it!=symbols.end();
        ++it)
    {
      contextt::symbolst::iterator s_it=context.symbols.find(*it);
      assert(s_it!=context.symbols.end());

      if(s_it->second.type.id()==ID_code &&
          s_it->second.value.id()!="compiled" &&
          s_it->second.value.is_not_nil())
      {
        print(9, "Compiling "+id2string(s_it->first));
        converter.convert_function(s_it->first);
        s_it->second.value=exprt("compiled");
      }
    }
  }
}
