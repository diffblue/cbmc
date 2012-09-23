/*******************************************************************\

Module: Compile and link source and object files.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#include <fstream>
#include <sstream>
#include <cstdlib>
#include <algorithm>

#include <config.h>
#include <tempdir.h>
#include <replace_symbol.h>
#include <base_type.h>
#include <i2string.h>
#include <cmdline.h>
#include <file_util.h>
#include <unicode.h>

#include <ansi-c/ansi_c_language.h>
#include <linking/linking_class.h>
#include <linking/entry_point.h>

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/goto_function_serialization.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/write_goto_binary.h>

#include <langapi/mode.h>

#include <irep_serialization.h>
#include <symbol_serialization.h>

#include "get_base_name.h"
#include "compile.h"
#include "version.h"

#define DOTGRAPHSETTINGS  "color=black;" \
                          "orientation=portrait;" \
                          "fontsize=20;"\
                          "compound=true;"\
                          "size=\"30,40\";"\
                          "ratio=compress;"

unsigned compilet::subgraphscount;

// the following are for chdir

#ifdef __linux__
#include <unistd.h>
#endif

#ifdef __FreeBSD_kernel__
#include <unistd.h>
#endif

#ifdef __MACH__
#include <unistd.h>
#endif

#ifdef __CYGWIN__
#include <unistd.h>
#endif

#ifdef _WIN32
#include <direct.h>
#include <windows.h>
#define chdir _chdir
#define popen _popen
#define pclose _pclose
#endif

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

  if(mode==LINK_LIBRARY && source_files.size()>0)
  {
    error("cannot link source files");
    return true;
  }

  if(mode==PREPROCESS_ONLY && object_files.size()>0)
  {
    error("cannot preprocess object files");
    return true;
  }

  if(source_files.size()>0)
    if(compile()) return true;

  if(mode==PREPROCESS_ONLY)
    return false; // we are done

  if(mode==LINK_LIBRARY ||
     mode==COMPILE_LINK_EXECUTABLE)
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

    if(ext=="c" ||
       ext=="cc" ||
       ext=="cp" ||
       ext=="cpp" ||
       ext=="CPP" ||
       ext=="c++" ||
       ext=="C" ||
       ext=="i" ||
       ext=="ii")
    {
      source_files.push_back(file_name);
    }
    else if(ext=="a")
    {
      #ifdef _WIN32
      char td[MAX_PATH+1];
      #else
      char td[] = "goto-cc.XXXXXX";
      #endif

      std::string tstr=get_temporary_directory(td);

      if(tstr=="")
      {
        error("Cannot create temporary directory");
        return true;
      }

      tmp_dirs.push_back(tstr);
      std::stringstream cmd("");
      if(chdir(tmp_dirs.back().c_str())!=0)
      {
        error("Cannot switch to temporary directory");
        return true;
      }

      // unpack now
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
      
      FILE *stream;

      stream=popen(cmd.str().c_str(), "r");
      pclose(stream);
      
      cmd.clear();
      cmd.str("");
      
      // add the files from "ar t"
      #ifdef _WIN32
      if(file_name[0]!='/' && file_name[1]!=':')
      #else
      if(file_name[0]!='/')
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

      stream=popen(cmd.str().c_str(), "r");
      if(stream!=NULL)
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

            if(is_goto_binary(t))
              object_files.push_back(t);
            line = "";
          }
        }
      }
      pclose(stream);
      cmd.str("");

      if(chdir(working_directory.c_str())!=0)
        error("Could not change back to working directory.");
    }
    else if(is_goto_binary(file_name))
      object_files.push_back(file_name);
    else
    {
      // unknown extension, not a goto binary, will ignore
    }
  }
  else
  {
    // don't care about no extensions
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
      std::string libname=tmp+name+".so";

      if(is_goto_binary(libname))
        add_input_file(libname);
      else if(is_elf_file(libname))
        std::cout << "Warning: Cannot read ELF library " << libname
                  << std::endl;
      else
        return false;
    }
  }
  
  return true;
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
    if(buf[0]==0x7f && buf[1]=='E' &&
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

    if(read_object(file_name, compiled_functions))
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
  
  // produce entry point?
  
  if(mode==COMPILE_LINK_EXECUTABLE)
  {
    if(entry_point(context, "c::main", ui_message_handler))
      return true;

    // entry_point may (should) add some more functions.
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

    if(r) return true; // parser/typecheck error

    if(mode==COMPILE_ONLY)
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

  #ifdef _MSC_VER
  std::ifstream infile(widen(file_name).c_str());
  #else
  std::ifstream infile(file_name.c_str());
  #endif

  if(!infile)
  {
    error("failed to open input file", file_name);
    return true;
  }

  languaget *languagep;
  
  // Using '-x', the type of a file can be overridden;
  // otherwise, it's guessed from the extension.
  
  if(cmdline.isset('x'))
  {
    const std::string language=cmdline.getval('x');
    if(language=="c++" || language=="c++-header")
      languagep=get_language_from_mode("cpp");
    else
      languagep=get_language_from_mode("C");
  }
  else
    languagep=get_language_from_filename(file_name);

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

  if(mode==PREPROCESS_ONLY)
  {
    print(8, "Preprocessing: "+file_name);

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
    print(8, "Parsing: "+file_name);

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

  if(mode==PREPROCESS_ONLY)
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

    for(goto_functionst::function_mapt::iterator
        it=functions.function_map.begin();
        it!=functions.function_map.end();
        it++)
    {
      if(it->second.body_available)
        write_dot_subgraph(dgf, id2string(it->first), it->second.body);
    }

    do_dot_function_calls(dgf);
    dgf << "}" << std::endl;
    dgf.close();
  }

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
  
  if(instructions.size()==0)
  {
    out << "Node_" << subgraphscount << "_0 " <<
      "[shape=Mrecord,fontsize=22,label=\"?\"];" << std::endl;
  }
  else
  {
    std::set<goto_programt::const_targett> seen;
    goto_programt::const_targetst worklist;
    worklist.push_back(instructions.begin());
    
    while(!worklist.empty())
    {
      goto_programt::const_targett it=worklist.front();
      worklist.pop_front();
      
      if(it==instructions.end() ||
         seen.find(it)!=seen.end()) continue;
          
      std::stringstream tmp("");
      if(it->is_goto())
      {
        if(it->guard.is_true())
          tmp.str("Goto");
        else
        {
          std::string t = from_expr(ns, "", it->guard);
          while (t[ t.size()-1 ]=='\n')
            t = t.substr(0,t.size()-1);
          tmp << escape(t) << "?";
        }
      }
      else if(it->is_assume())
      {
        std::string t = from_expr(ns, "", it->guard);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp << "Assume\\n(" << escape(t) << ")";
      }
      else if(it->is_assert())
      {
        std::string t = from_expr(ns, "", it->guard);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp << "Assert\\n(" << escape(t) << ")";
      }
      else if(it->is_skip())
        tmp.str("Skip");
      else if(it->is_end_function())            
        tmp.str("End of Function");      
      else if(it->is_location())
        tmp.str("Location");
      else if(it->is_dead())
        tmp.str("Dead");
      else if(it->is_atomic_begin())
        tmp.str("Atomic Begin");
      else if(it->is_atomic_end())
        tmp.str("Atomic End");
      else if(it->is_function_call())
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
      else if(it->is_assign() ||
               it->is_return() ||
               it->is_other())      
      {
        std::string t = from_expr(ns, "", it->code);
        while (t[ t.size()-1 ]=='\n')
          t = t.substr(0,t.size()-1);
        tmp.str(escape(t));
      }
      else if(it->is_start_thread())
        tmp.str("Start of Thread");
      else if(it->is_end_thread())
        tmp.str("End of Thread");
      else if(it->is_throw())
        tmp.str("THROW");
      else if(it->is_catch())
        tmp.str("CATCH");
      else
        tmp.str("UNKNOWN");

      out << "Node_" << subgraphscount << "_" << it->location_number;
      out << " [shape="; 
      if(it->is_goto() && !it->guard.is_true() && !it->guard.is_false())
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
      if(fres.size()==0 || tres.size()==0)
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
      if(cit->get("name")==it->op1().get(ID_identifier))
        break;

    if(cit!=clusters.end())
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
  if(it->is_goto() && !it->guard.is_false())
  {
    goto_programt::targetst::const_iterator gtit = it->targets.begin();
    for (; gtit!=it->targets.end(); gtit++)
      tres.insert((*gtit));
  }

  if(it->is_goto() && it->guard.is_true())
    return;
  
  goto_programt::const_targett next = it; next++;
  if(next!=instructions.end())
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
  if(label!="")
    {
      out << "[fontsize=20,label=\"" << label << "\"";
      if(from.is_backwards_goto() &&
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

Function: compilet::read_object

  Inputs: a file_name

 Outputs: true on error, false otherwise

 Purpose: reads an object file

\*******************************************************************/

bool compilet::read_object(
  const std::string &file_name,
  goto_functionst &functions)
{
  print(8, "Reading: " + file_name);

  // we read into a temporary context
  contextt temp_context;
  goto_functionst temp_functions;

  if(read_goto_binary(file_name, temp_context, temp_functions, *message_handler))
    return true;
  
  std::set<irep_idt> seen_modes;

  for(contextt::symbolst::const_iterator
      it=temp_context.symbols.begin();
      it!=temp_context.symbols.end();
      it++)
  {
    if(it->second.mode!="")
      seen_modes.insert(it->second.mode);
  }
  
  seen_modes.erase(ID_cpp);
  seen_modes.erase(ID_C);

  if(seen_modes.size()!=0)
  {
    error("Multi-language linking not supported");
    return true;
  }

  // hardwired to C-style linking

  linkingt linking(context, temp_context, ui_message_handler);

  if(linking.typecheck_main())
    return true;
    
  if(link_functions(context, functions,
                    temp_context, temp_functions,
                    linking.replace_symbol))
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
  mode=COMPILE_LINK_EXECUTABLE;
  echo_file_name=false;
  subgraphscount=0;
  working_directory=get_current_working_directory();
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

  for(std::list<std::string>::const_iterator it = tmp_dirs.begin();
      it!=tmp_dirs.end();
      it++)
    delete_directory(*it);
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
  if(verbosity>=9)
    status("Writing dot graph to " + dgfilename);
  dgf.open(dgfilename.c_str());
  if(!dgf.is_open())
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
  int fbs=0;

  for(goto_functionst::function_mapt::const_iterator it=
      functions.function_map.begin();
      it != functions.function_map.end();
      it++)
    if(it->second.body_available)
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
  contextt &dest_context,
  goto_functionst &dest_functions,
  contextt &src_context,
  goto_functionst &src_functions,
  const replace_symbolt &replace_symbol)
{
  // merge functions
  Forall_goto_functions(src_it, src_functions)
  {
    // the function might have been renamed    
    replace_symbolt::expr_mapt::const_iterator e_it=
      replace_symbol.expr_map.find(src_it->first);
    irep_idt final_id=src_it->first;
    if(e_it!=replace_symbol.expr_map.end())
    {
      const exprt &rep_exp=e_it->second;
      if(rep_exp.id()==ID_symbol)
        final_id=rep_exp.get(ID_identifier);
    }
  
    // already there?
    goto_functionst::function_mapt::iterator dest_f_it=
      dest_functions.function_map.find(final_id);

    if(dest_f_it==dest_functions.function_map.end()) // not there yet
    {
      replace_symbols_in_function(src_it->second, replace_symbol);

      goto_functionst::goto_functiont &in_dest_context=
        dest_functions.function_map[final_id];

      in_dest_context.body.swap(src_it->second.body);
      in_dest_context.body_available=src_it->second.body_available;
      in_dest_context.type=src_it->second.type;
    }
    else // collision!
    {
      goto_functionst::goto_functiont &in_dest_context=
        dest_functions.function_map[final_id];

      goto_functionst::goto_functiont &src_func=src_it->second;

      if(in_dest_context.body.instructions.empty())
      {
        // the one with body wins!
        replace_symbols_in_function(src_func, replace_symbol);
        
        in_dest_context.body.swap(src_func.body);
        in_dest_context.body_available=src_func.body_available;
        in_dest_context.type=src_func.type;
      }
      else if(src_func.body.instructions.empty())
      {
        // just keep the old one in dest
      }
      else if(in_dest_context.type.get_bool(ID_C_inlined))
      {
        // ok, we silently ignore
      }
      else if(base_type_eq(in_dest_context.type, src_func.type, ns))
      {
        // keep the one in in_context -- libraries come last!
        std::stringstream str;
        str << "warning: function `" << final_id << "' in module `"
            << src_context.symbols.begin()->second.module
            << "' is shadowed by a definition in module `"
            << context.symbols.begin()->second.module << "'";
        warning(str.str());
      }
      else
      {
        std::stringstream str;
        str << "error: duplicate definition of function `"
            << final_id
            << "'" << std::endl;
        str << "In module `" 
            << context.symbols.begin()->second.module
            << "' and module `"
            << src_context.symbols.begin()->second.module << "'";
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
  goto_functionst::goto_functiont &function,
  const replace_symbolt &replace_symbol) const
{
  goto_programt &program=function.body;
  replace_symbol.replace(function.type);

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
