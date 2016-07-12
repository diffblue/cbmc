/*******************************************************************\

Module: GCC Mode

Author: CM Wintersteiger, 2006

\*******************************************************************/

#ifdef _WIN32
#define EX_OK 0
#define EX_USAGE 64
#define EX_SOFTWARE 70
#else
#include <sysexits.h>
#endif

#include <cstdio>
#include <iostream>
#include <fstream>

#include <util/string2int.h>
#include <util/tempdir.h>
#include <util/config.h>
#include <util/prefix.h>
#include <util/suffix.h>
#include <util/get_base_name.h>
#include <util/run.h>

#include <cbmc/version.h>

#include "compile.h"
#include "gcc_mode.h"

/*******************************************************************\

Function: compiler_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string compiler_name(
  const cmdlinet &cmdline,
  const std::string &base_name)
{
  if(cmdline.isset("native-compiler"))
    return cmdline.get_value("native-compiler");

  if(base_name=="bcc" ||
     base_name.find("goto-bcc")!=std::string::npos)
    return "bcc";

  std::string::size_type pos=base_name.find("goto-gcc");

  if(pos==std::string::npos ||
     base_name=="goto-gcc" ||
     base_name=="goto-ld")
  {
    #ifdef __FreeBSD__
    return "clang";
    #else
    return "gcc";
    #endif
  }

  std::string result=base_name;
  result.replace(pos, 8, "gcc");

  return result;
}

/*******************************************************************\

Function: linker_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static std::string linker_name(
  const cmdlinet &cmdline,
  const std::string &base_name)
{
  if(cmdline.isset("native-linker"))
    return cmdline.get_value("native-linker");

  std::string::size_type pos=base_name.find("goto-ld");

  if(pos==std::string::npos ||
     base_name=="goto-gcc" ||
     base_name=="goto-ld")
    return "ld";

  std::string result=base_name;
  result.replace(pos, 7, "ld");

  return result;
}

/*******************************************************************\

Function: gcc_modet::gcc_modet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

gcc_modet::gcc_modet(
  goto_cc_cmdlinet &_cmdline,
  const std::string &_base_name,
  bool _produce_hybrid_binary):
  goto_cc_modet(_cmdline, _base_name),
  produce_hybrid_binary(_produce_hybrid_binary),
  act_as_ld(base_name=="ld" ||
            base_name.find("goto-ld")!=std::string::npos)
{
}

/*******************************************************************\

Function: gcc_modet::needs_preprocessing

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool gcc_modet::needs_preprocessing(const std::string &file)
{
  if(has_suffix(file, ".c") ||
     has_suffix(file, ".cc") ||
     has_suffix(file, ".cp") ||
     has_suffix(file, ".cpp") ||
     has_suffix(file, ".CPP") ||
     has_suffix(file, ".c++") ||
     has_suffix(file, ".C"))
    return true;
  else
    return false;
}

/*******************************************************************\

Function: gcc_modet::doit

  Inputs:

 Outputs:

 Purpose: does it.

\*******************************************************************/

int gcc_modet::doit()
{
  if(cmdline.isset('?') ||
     cmdline.isset("help"))
  {
    help();
    return EX_OK;
  }

  native_tool_name=
    act_as_ld ?
    linker_name(cmdline, base_name) :
    compiler_name(cmdline, base_name);

  unsigned int verbosity=1;

  bool act_as_bcc=
    base_name=="bcc" ||
    base_name.find("goto-bcc")!=std::string::npos;

  if((cmdline.isset('v') || cmdline.isset("version")) &&
     cmdline.have_infile_arg()) // let the native tool print the version
  {
    // This a) prints the version and b) increases verbosity.
    // Compilation continues, don't exit!

    if(act_as_ld)
      std::cout << "GNU ld version 2.16.91 20050610 (goto-cc " CBMC_VERSION ")\n";
    else if(act_as_bcc)
      std::cout << "bcc: version 0.16.17 (goto-cc " CBMC_VERSION ")\n";
    else
      std::cout << "gcc version 3.4.4 (goto-cc " CBMC_VERSION ")\n";
  }

  if(cmdline.isset("version"))
  {
    std::cout << '\n' <<
      "Copyright (C) 2006-2014 Daniel Kroening, Christoph Wintersteiger\n" <<
      "CBMC version: " CBMC_VERSION << '\n' <<
      "Architecture: " << config.this_architecture() << '\n' <<
      "OS: " << config.this_operating_system() << '\n';

    return EX_OK; // Exit!
  }

  if(cmdline.isset("dumpversion"))
  {
    std::cout << "3.4.4" << std::endl;
    return EX_OK;
  }

  if(cmdline.isset("Wall"))
    verbosity=2;

  if(cmdline.isset("verbosity"))
    verbosity=unsafe_string2unsigned(cmdline.get_value("verbosity"));

  ui_message_handler.set_verbosity(verbosity);

  if(act_as_ld)
  {
    if(produce_hybrid_binary)
      debug() << "LD mode (hybrid)" << eom;
    else
      debug() << "LD mode" << eom;
  }
  else if(act_as_bcc)
  {
    if(produce_hybrid_binary)
      debug() << "BCC mode (hybrid)" << eom;
    else
      debug() << "BCC mode" << eom;
  }
  else
  {
    if(produce_hybrid_binary)
      debug() << "GCC mode (hybrid)" << eom;
    else
      debug() << "GCC mode" << eom;
  }

  // In gcc mode, we have just pass on to gcc to handle the following:
  // * if -M or -MM is given, we do dependencies only
  // * preprocessing (-E)
  // * no input files given

  if(act_as_ld)
  {
  }
  else if(cmdline.isset('M') ||
          cmdline.isset("MM") ||
          cmdline.isset('E') ||
          !cmdline.have_infile_arg())
    return run_gcc(); // exit!

  // get configuration
  config.set(cmdline);

  // Intel-specific
  // in GCC, m16 is 32-bit (!), as documented here:
  // https://gcc.gnu.org/bugzilla/show_bug.cgi?id=59672
  if(cmdline.isset("m16") ||
     cmdline.isset("m32") || cmdline.isset("mx32"))
  {
    config.ansi_c.arch="i386";
    config.ansi_c.set_arch_spec_i386();
  }
  else if(cmdline.isset("m64"))
  {
    config.ansi_c.arch="x86_64";
    config.ansi_c.set_arch_spec_x86_64();
  }

  // ARM-specific
  if(cmdline.isset("mbig-endian") || cmdline.isset("mbig"))
    config.ansi_c.endianness=configt::ansi_ct::endiannesst::IS_BIG_ENDIAN;
  else if(cmdline.isset("little-endian") || cmdline.isset("mlittle"))
    config.ansi_c.endianness=configt::ansi_ct::endiannesst::IS_LITTLE_ENDIAN;

  // -fshort-wchar makes wchar_t "short unsigned int"
  if(cmdline.isset("fshort-wchar"))
  {
    config.ansi_c.wchar_t_width=config.ansi_c.short_int_width;
    config.ansi_c.wchar_t_is_unsigned=true;
  }

  // -fsingle-precision-constant makes floating-point constants "float"
  // instead of double
  if(cmdline.isset("-fsingle-precision-constant"))
    config.ansi_c.single_precision_constant=true;

  // -fshort-double makes double the same as float
  if(cmdline.isset("fshort-double"))
    config.ansi_c.double_width=config.ansi_c.single_width;

  // determine actions to be undertaken
  compilet compiler(cmdline);
  compiler.ui_message_handler.set_verbosity(verbosity);

  if(act_as_ld)
    compiler.mode=compilet::LINK_LIBRARY;
  else if(cmdline.isset('S'))
    compiler.mode=compilet::ASSEMBLE_ONLY;
  else if(cmdline.isset('c'))
    compiler.mode=compilet::COMPILE_ONLY;
  else if(cmdline.isset('E'))
  {
    compiler.mode=compilet::PREPROCESS_ONLY;
    assert(false);
  }
  else if(cmdline.isset("shared") ||
          cmdline.isset('r')) // really not well documented
    compiler.mode=compilet::COMPILE_LINK;
  else
    compiler.mode=compilet::COMPILE_LINK_EXECUTABLE;

  switch(compiler.mode)
  {
  case compilet::LINK_LIBRARY: debug() << "Linking a library only" << eom; break;
  case compilet::COMPILE_ONLY: debug() << "Compiling only" << eom; break;
  case compilet::ASSEMBLE_ONLY: debug() << "Assembling only" << eom; break;
  case compilet::PREPROCESS_ONLY: debug() << "Preprocessing only" << eom; break;
  case compilet::COMPILE_LINK: debug() << "Compiling and linking a library" << eom; break;
  case compilet::COMPILE_LINK_EXECUTABLE: debug() << "Compiling and linking an executable" << eom; break;
  default: assert(false);
  }

  if(cmdline.isset("i386-win32") ||
     cmdline.isset("winx64"))
  {
    // We may wish to reconsider the below.
    config.ansi_c.mode=configt::ansi_ct::flavourt::VISUAL_STUDIO;
    debug() << "Enabling Visual Studio syntax" << eom;
  }
  else if(config.this_operating_system()=="macos")
    config.ansi_c.mode=configt::ansi_ct::flavourt::APPLE;
  else
    config.ansi_c.mode=configt::ansi_ct::flavourt::GCC;

  if(compiler.mode==compilet::ASSEMBLE_ONLY)
    compiler.object_file_extension="s";
  else
    compiler.object_file_extension="o";

  if(cmdline.isset("std"))
  {
    std::string std_string=cmdline.get_value("std");

    if(std_string=="gnu89" || std_string=="c89")
      config.ansi_c.set_c89();

    if(std_string=="gnu99" || std_string=="c99" || std_string=="iso9899:1999" ||
       std_string=="gnu9x" || std_string=="c9x" || std_string=="iso9899:199x")
      config.ansi_c.set_c99();

    if(std_string=="gnu11" || std_string=="c11" ||
       std_string=="gnu1x" || std_string=="c1x")
      config.ansi_c.set_c11();

    if(std_string=="c++11" || std_string=="c++1x" ||
       std_string=="gnu++11" || std_string=="gnu++1x" ||
       std_string=="c++1y" ||
       std_string=="gnu++1y")
      config.cpp.set_cpp11();

    if(std_string=="gnu++14" || std_string=="c++14")
      config.cpp.set_cpp14();
  }

  // gcc's default is 32 bits for wchar_t
  if(cmdline.isset("short-wchar"))
    config.ansi_c.wchar_t_width=16;

  // gcc's default is 64 bits for double
  if(cmdline.isset("short-double"))
    config.ansi_c.double_width=32;

  // gcc's default is signed chars on most architectures
  if(cmdline.isset("funsigned-char"))
    config.ansi_c.char_is_unsigned=true;

  if(cmdline.isset("fsigned-char"))
    config.ansi_c.char_is_unsigned=false;

  if(cmdline.isset('U'))
    config.ansi_c.undefines=cmdline.get_values('U');

  if(cmdline.isset("undef"))
    config.ansi_c.preprocessor_options.push_back("-undef");

  if(cmdline.isset("nostdinc"))
    config.ansi_c.preprocessor_options.push_back("-nostdinc");

  if(cmdline.isset('L'))
    compiler.library_paths=cmdline.get_values('L');
    // Don't add the system paths!

  if(cmdline.isset('l'))
    compiler.libraries=cmdline.get_values('l');

  if(cmdline.isset("static"))
    compiler.libraries.push_back("c");

  if(cmdline.isset("pthread"))
    compiler.libraries.push_back("pthread");

  if(cmdline.isset('o'))
  {
    // given gcc -o file1 -o file2,
    // gcc will output to file2, not file1
    compiler.output_file_object=cmdline.get_values('o').back();
    compiler.output_file_executable=cmdline.get_values('o').back();
  }
  else
  {
    compiler.output_file_object="";
    compiler.output_file_executable="a.out";
  }

  // We now iterate over any input files

  temp_dirt temp_dir("goto-cc-XXXXXX");

  {
    std::string language;

    for(goto_cc_cmdlinet::parsed_argvt::iterator
        arg_it=cmdline.parsed_argv.begin();
        arg_it!=cmdline.parsed_argv.end();
        arg_it++)
    {
      if(arg_it->is_infile_name)
      {
        // do any preprocessing needed

        if(language=="cpp-output" || language=="c++-cpp-output")
        {
          compiler.add_input_file(arg_it->arg);
        }
        else if(language=="c" || language=="c++" ||
                (language=="" && needs_preprocessing(arg_it->arg)))
        {
          std::string new_suffix;

          if(language=="c")
            new_suffix=".i";
          else if(language=="c++")
            new_suffix=".ii";
          else
            new_suffix=has_suffix(arg_it->arg, ".c")?".i":".ii";

          std::string new_name=
            get_base_name(arg_it->arg, true)+new_suffix;
          std::string dest=temp_dir(new_name);

          int exit_code=
            preprocess(language, arg_it->arg, dest, act_as_bcc);

          if(exit_code!=0)
          {
            error() << "preprocessing has failed" << eom;
            return exit_code;
          }

          compiler.add_input_file(dest);
        }
        else
          compiler.add_input_file(arg_it->arg);
      }
      else if(arg_it->arg=="-x")
      {
        arg_it++;
        if(arg_it!=cmdline.parsed_argv.end())
        {
          language=arg_it->arg;
          if(language=="none") language="";
        }
      }
      else if(has_prefix(arg_it->arg, "-x"))
      {
        language=std::string(arg_it->arg, 2, std::string::npos);
        if(language=="none") language="";
      }
    }
  }

  // Revert to gcc in case there is no source to compile
  // and no binary to link.

  if(compiler.source_files.empty() &&
     compiler.object_files.empty())
    return run_gcc(); // exit!

  if(compiler.mode==compilet::ASSEMBLE_ONLY)
    return asm_output(act_as_bcc, compiler.source_files);

  // do all the rest
  if(compiler.doit())
    return 1; // GCC exit code for all kinds of errors

  // We can generate hybrid ELF and Mach-O binaries
  // containing both executable machine code and the goto-binary.
  if(produce_hybrid_binary && !act_as_bcc)
    return gcc_hybrid_binary();

  return EX_OK;
}

/*******************************************************************\

Function: gcc_modet::preprocess

  Inputs:

 Outputs:

 Purpose: call gcc for preprocessing

\*******************************************************************/

int gcc_modet::preprocess(
  const std::string &language,
  const std::string &src,
  const std::string &dest,
  bool act_as_bcc)
{
  // build new argv
  std::vector<std::string> new_argv;

  new_argv.reserve(cmdline.parsed_argv.size());

  bool skip_next=false;

  for(goto_cc_cmdlinet::parsed_argvt::const_iterator
      it=cmdline.parsed_argv.begin();
      it!=cmdline.parsed_argv.end();
      it++)
  {
    if(skip_next)
    {
      // skip
      skip_next=false;
    }
    else if(it->is_infile_name)
    {
      // skip
    }
    else if(it->arg=="-c" || it->arg=="-E" || it->arg=="-S")
    {
      // skip
    }
    else if(it->arg=="-o")
    {
      skip_next=true;
    }
    else if(has_prefix(it->arg, "-o"))
    {
      // ignore
    }
    else if(it->arg=="--function" ||
            it->arg=="--verbosity" ||
            it->arg=="--native-linker" ||
            it->arg=="--print-rejected-preprocessed-source")
    {
      // ignore here
      skip_next=true;
    }
    else if(it->arg=="--native-compiler")
    {
      ++it;
      assert(it!=cmdline.parsed_argv.end());
      compiler=it->arg.c_str();
    }
    else
      new_argv.push_back(it->arg);
  }

  // We just want to preprocess.
  new_argv.push_back("-E");

  // destination file
  std::string stdout_file;
  if(act_as_bcc)
    stdout_file=dest;
  else
  {
    new_argv.push_back("-o");
    new_argv.push_back(dest);
  }

  // language, if given
  if(language!="")
  {
    new_argv.push_back("-x");
    new_argv.push_back(language);
  }

  // source file
  new_argv.push_back(src);

  // overwrite argv[0]
  assert(new_argv.size()>=1);
  new_argv[0]=native_tool_name.c_str();

  #if 0
  std::cout << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif

  return run(new_argv[0], new_argv, cmdline.stdin_file, stdout_file);
}

/*******************************************************************\

Function: gcc_modet::run_gcc

  Inputs:

 Outputs:

 Purpose: run gcc or clang with original command line

\*******************************************************************/

int gcc_modet::run_gcc()
{
  // build new argv
  std::vector<std::string> new_argv(1);

  new_argv.reserve(cmdline.parsed_argv.size());

  // overwrite argv[0]
  new_argv[0]=native_tool_name;

  #if 0
  std::cout << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif

  return run(new_argv[0], new_argv, cmdline.stdin_file, "");
}

/*******************************************************************\

Function: gcc_modet::gcc_hybrid_binary

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int gcc_modet::gcc_hybrid_binary()
{
  {
    bool have_files=false;

    for(goto_cc_cmdlinet::parsed_argvt::const_iterator
        it=cmdline.parsed_argv.begin();
        it!=cmdline.parsed_argv.end();
        it++)
      if(it->is_infile_name)
        have_files=true;

    if(!have_files)
      return EX_OK;
  }

  std::list<std::string> output_files;

  if(cmdline.isset('c'))
  {
    if(cmdline.isset('o'))
    {
      // there should be only one input file
      output_files.push_back(cmdline.get_value('o'));
    }
    else
    {
      for(goto_cc_cmdlinet::parsed_argvt::const_iterator
          i_it=cmdline.parsed_argv.begin();
          i_it!=cmdline.parsed_argv.end();
          i_it++)
        if(i_it->is_infile_name &&
           needs_preprocessing(i_it->arg))
          output_files.push_back(get_base_name(i_it->arg, true)+".o");
    }
  }
  else
  {
    // -c is not given
    if(cmdline.isset('o'))
      output_files.push_back(cmdline.get_value('o'));
    else
      output_files.push_back("a.out");
  }

  if(output_files.empty() ||
     (output_files.size()==1 &&
      output_files.front()=="/dev/null"))
    return EX_OK;

  debug() << "Running " << native_tool_name
          << " to generate hybrid binary" << eom;

  // save the goto-cc output files
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    rename(it->c_str(), (*it+".goto-cc-saved").c_str());
  }

  int result=run_gcc();

  // merge output from gcc with goto-binaries
  // using objcopy, or do cleanup if an earlier call failed
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    debug() << "merging " << *it << eom;
    std::string saved=*it+".goto-cc-saved";

    #ifdef __linux__
    if(result==0 && !cmdline.isset('c'))
    {
      // remove any existing goto-cc section
      std::vector<std::string> objcopy_argv;

      objcopy_argv.push_back("objcopy");
      objcopy_argv.push_back("--remove-section=goto-cc");
      objcopy_argv.push_back(*it);

      result=run(objcopy_argv[0], objcopy_argv, "", "");
    }

    if(result==0)
    {
      // now add goto-binary as goto-cc section
      std::vector<std::string> objcopy_argv;

      objcopy_argv.push_back("objcopy");
      objcopy_argv.push_back("--add-section");
      objcopy_argv.push_back("goto-cc="+saved);
      objcopy_argv.push_back(*it);

      result=run(objcopy_argv[0], objcopy_argv, "", "");
    }

    remove(saved.c_str());
    #elif defined(__APPLE__)
    // Mac
    if(result==0)
    {
      std::vector<std::string> lipo_argv;

      // now add goto-binary as hppa7100LC section
      lipo_argv.push_back("lipo");
      lipo_argv.push_back(*it);
      lipo_argv.push_back("-create");
      lipo_argv.push_back("-arch");
      lipo_argv.push_back("hppa7100LC");
      lipo_argv.push_back(saved);
      lipo_argv.push_back("-output");
      lipo_argv.push_back(*it);

      result=run(lipo_argv[0], lipo_argv, "", "");
    }

    remove(saved.c_str());

    #else
    error() << "binary merging not implemented for this platform" << eom;
    return 1;
    #endif
  }

  return result;
}

/*******************************************************************\

Function: gcc_modet::asm_output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int gcc_modet::asm_output(
  bool act_as_bcc,
  const std::list<std::string> &preprocessed_source_files)
{
  {
    bool have_files=false;

    for(goto_cc_cmdlinet::parsed_argvt::const_iterator
        it=cmdline.parsed_argv.begin();
        it!=cmdline.parsed_argv.end();
        it++)
      if(it->is_infile_name)
        have_files=true;

    if(!have_files)
      return EX_OK;
  }

  if(produce_hybrid_binary)
  {
    debug() << "Running " << native_tool_name
      << " to generate native asm output" << eom;

    int result=run_gcc();
    if(result!=0)
      // native tool failed
      return result;
  }

  std::map<std::string, std::string> output_files;

  if(cmdline.isset('o'))
  {
    // GCC --combine supports more than one source file
    for(const auto &s : preprocessed_source_files)
      output_files.insert(std::make_pair(s, cmdline.get_value('o')));
  }
  else
  {
    for(const std::string &s : preprocessed_source_files)
      output_files.insert(
        std::make_pair(s, get_base_name(s, true)+".s"));
  }

  if(output_files.empty() ||
     (output_files.size()==1 &&
      output_files.begin()->second=="/dev/null"))
    return EX_OK;

  debug()
    << "Appending preprocessed sources to generate hybrid asm output"
    << eom;

  for(const auto &so : output_files)
  {
    std::ifstream is(so.first);
    if(!is.is_open())
    {
      error() << "Failed to open input source " << so.first << eom;
      return 1;
    }

    std::ofstream os(so.second, std::ios::app);
    if(!os.is_open())
    {
      error() << "Failed to open output file " << so.second << eom;
      return 1;
    }

    const char comment=act_as_bcc ? ':' : '#';

    os << comment << comment << " GOTO-CC" << '\n';

    std::string line;

    while(std::getline(is, line))
    {
      os << comment << comment << line << '\n';
    }
  }

  return EX_OK;
}

/*******************************************************************\

Function: gcc_modet::help_mode

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void gcc_modet::help_mode()
{
  if(act_as_ld)
    std::cout << "goto-ld understands the options of ld plus the following.\n\n";
  else
    std::cout << "goto-cc understands the options of gcc plus the following.\n\n";
}
