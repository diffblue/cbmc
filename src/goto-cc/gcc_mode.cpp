/*******************************************************************\

Module: GCC Mode

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <cstdio>
#include <cstdlib> // exit()
#include <iostream>

#include <util/string2int.h>
#include <util/tempdir.h>
#include <util/config.h>
#include <util/prefix.h>
#include <util/suffix.h>

#include <cbmc/version.h>

#include "compile.h"
#include "run.h"

#include "gcc_mode.h"

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

bool gcc_modet::doit()
{
  act_as_ld=
    has_prefix(base_name, "ld") ||
    has_prefix(base_name, "goto-ld");

  if(cmdline.isset('?') ||
     cmdline.isset("help"))
  {
    help();
    return false;
  }

  unsigned int verbosity=1;

  if(cmdline.isset('v'))
  {
    // This a) prints the version and b) increases verbosity.
    // Compilation continues, don't exit!
    
    if(act_as_ld)
      std::cout << "GNU ld version 2.16.91 20050610 (goto-cc " CBMC_VERSION ")\n";
    else
      std::cout << "gcc version 3.4.4 (goto-cc " CBMC_VERSION ")\n";
  }

  if(cmdline.isset("version"))
  {
    if(act_as_ld)
      std::cout << "GNU ld version 2.16.91 20050610 (goto-cc " CBMC_VERSION ")\n";
    else
      std::cout << "gcc (GCC) 3.4.4 (goto-cc " CBMC_VERSION ")\n\n";

    std::cout << 
      "Copyright (C) 2006-2014 Daniel Kroening, Christoph Wintersteiger\n" <<
      "CBMC version: " CBMC_VERSION << '\n' <<
      "Architecture: " << config.this_architecture() << '\n' <<
      "OS: " << config.this_operating_system() << '\n';

    return false; // Exit!
  }

  if(cmdline.isset("dumpversion"))
  {
    std::cout << "3.4.4" << std::endl;
    return false;
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
  else
  {
    if(produce_hybrid_binary)
      debug() << "GCC mode (hybrid)" << eom;
    else
      debug() << "GCC mode" << eom;
  }

  // In gcc mode, we have just pass on to gcc to handle the following:
  // * if -M or -MM is given, we do dependencies only
  // * assembly (-S)
  // * preprocessing (-E).
  // * no input files given
  
  if(act_as_ld)
  {
  }
  else if(cmdline.isset('M') || 
          cmdline.isset("MM") ||
          cmdline.isset('S') ||
          cmdline.isset('E') ||
          !cmdline.have_infile_arg())
  {
    int result;
    result=run_gcc();
    exit(result);
  }
  
  // get configuration
  config.set(cmdline);
  
  if(cmdline.isset("m32") || cmdline.isset("mx32"))
    config.ansi_c.set_32();
  else if(cmdline.isset("m64"))
    config.ansi_c.set_64();
    
  // ARM-specific
  if(cmdline.isset("mbig-endian") || cmdline.isset("mbig"))
    config.ansi_c.endianness=configt::ansi_ct::IS_BIG_ENDIAN;
  else if(cmdline.isset("little-endian") || cmdline.isset("mlittle"))
    config.ansi_c.endianness=configt::ansi_ct::IS_LITTLE_ENDIAN;
    
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
  else if(cmdline.isset('c'))
    compiler.mode=compilet::COMPILE_ONLY;
  else if(cmdline.isset('S'))
  {
    compiler.mode=compilet::ASSEMBLE_ONLY;
    assert(false);
  }
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
    config.ansi_c.mode=configt::ansi_ct::MODE_VISUAL_STUDIO_C_CPP;
    debug() << "Enabling Visual Studio syntax" << eom;
  }
  else
    config.ansi_c.mode=configt::ansi_ct::MODE_GCC_C;

  if(compiler.mode==compilet::ASSEMBLE_ONLY)
    compiler.object_file_extension="s";
  else
    compiler.object_file_extension="o";
  
  if(cmdline.isset("std"))
  {
    std::string std_string=cmdline.get_value("std");

    if(std_string=="gnu99" || std_string=="c99" || std_string=="iso9899:1999" ||
       std_string=="gnu9x" || std_string=="c9x" || std_string=="iso9899:199x" ||
       std_string=="gnu11" || std_string=="c11" ||
       std_string=="gnu1x" || std_string=="c1x")
      config.ansi_c.for_has_scope=true;

    if(std_string=="c++11" || std_string=="c++1x" ||
       std_string=="gnu++11" || std_string=="gnu++1x" || 
       std_string=="c++1y" ||
       std_string=="gnu++1y")
      config.ansi_c.cpp11=true;
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

          std::string new_name=get_base_name(arg_it->arg)+new_suffix;
          std::string dest=temp_dir(new_name);

          int exit_code=preprocess(language, arg_it->arg, dest);

          if(exit_code!=0)
          {
            error() << "preprocessing has failed" << eom;
            return true;
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
  {
    temp_dir.clear();
    int result;
    result=run_gcc();
    exit(result);
  }

  // do all the rest
  bool result=compiler.doit();

  // We can generate hybrid ELF and Mach-O binaries
  // containing both executable machine code and the goto-binary.
  if(produce_hybrid_binary)
  {
    if(gcc_hybrid_binary())
      result=true;
  }
  
  return result;
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
  const std::string &dest)
{
  // build new argv
  std::vector<std::string> new_argv;
  
  new_argv.reserve(cmdline.parsed_argv.size());

  bool skip_next=false;
  
  for(gcc_cmdlinet::parsed_argvt::const_iterator
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
    else if(it->arg=="--function" || it->arg=="--verbosity")
    {
      // ignore here
      skip_next=true;
    }
    else
      new_argv.push_back(it->arg);
  }

  // We just want to preprocess.
  new_argv.push_back("-E");

  // destination file
  new_argv.push_back("-o");
  new_argv.push_back(dest);
  
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
  new_argv[0]=compiler_name();
  
  #if 0
  std::cout << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif
  
  return run(compiler_name(), new_argv);
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
  std::vector<std::string> new_argv;
  
  new_argv.reserve(cmdline.parsed_argv.size());

  for(gcc_cmdlinet::parsed_argvt::const_iterator
      it=cmdline.parsed_argv.begin();
      it!=cmdline.parsed_argv.end();
      it++)
  {
    new_argv.push_back(it->arg);
  }
  
  const char *compiler=compiler_name();

  // overwrite argv[0]
  assert(new_argv.size()>=1);
  new_argv[0]=compiler;
  
  #if 0
  std::cout << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif
  
  return run(compiler, new_argv);
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

    for(gcc_cmdlinet::parsed_argvt::const_iterator
        it=cmdline.parsed_argv.begin();
        it!=cmdline.parsed_argv.end();
        it++)
      if(it->is_infile_name)
        have_files=true;

    if(!have_files)
      return 0;
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
      for(gcc_cmdlinet::parsed_argvt::const_iterator
          i_it=cmdline.parsed_argv.begin();
          i_it!=cmdline.parsed_argv.end();
          i_it++)
        if(i_it->is_infile_name)
        {
          if(needs_preprocessing(i_it->arg))
            output_files.push_back(get_base_name(i_it->arg)+".o");
        }
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

  if(output_files.empty()) return 0;

  if(act_as_ld)
    debug() << "Running ld to generate hybrid binary" << eom;
  else
    debug() << "Running gcc to generate hybrid binary" << eom;
  
  // save the goto-cc output files
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    rename(it->c_str(), (*it+".goto-cc-saved").c_str());
  }

  // build new argv
  std::vector<std::string> new_argv;
  
  new_argv.reserve(cmdline.parsed_argv.size());
  
  bool skip_next=false;

  for(gcc_cmdlinet::parsed_argvt::const_iterator
      it=cmdline.parsed_argv.begin();
      it!=cmdline.parsed_argv.end();
      it++)
  {
    if(skip_next)
    {
      // skip
      skip_next=false;
    }
    else if(it->arg=="--verbosity")
    {
      // ignore here
      skip_next=true;
    }
    else
      new_argv.push_back(it->arg);
  }

  // overwrite argv[0]
  assert(new_argv.size()>=1);
  
  if(act_as_ld)
    new_argv[0]="ld";
  else
    new_argv[0]=compiler_name();
  
  #if 0
  std::cout << "RUN:";
  for(std::size_t i=0; i<new_argv.size(); i++)
    std::cout << " " << new_argv[i];
  std::cout << std::endl;
  #endif
  
  int result=run(new_argv[0], new_argv);
  
  // merge output from gcc with goto-binaries
  // using objcopy
  for(std::list<std::string>::const_iterator
      it=output_files.begin();
      it!=output_files.end();
      it++)
  {
    debug() << "merging " << *it << eom;
    std::string saved=*it+".goto-cc-saved";

    #ifdef __linux__
    if(!cmdline.isset('c'))
    {
      // remove any existing goto-cc section
      std::vector<std::string> objcopy_argv;
    
      objcopy_argv.push_back("objcopy");
      objcopy_argv.push_back("--remove-section=goto-cc");
      objcopy_argv.push_back(*it);
      
      run(objcopy_argv[0], objcopy_argv);
    }

    // now add goto-binary as goto-cc section  
    std::vector<std::string> objcopy_argv;
  
    objcopy_argv.push_back("objcopy");
    objcopy_argv.push_back("--add-section");
    objcopy_argv.push_back("goto-cc="+saved);
    objcopy_argv.push_back(*it);
    
    run(objcopy_argv[0], objcopy_argv);

    remove(saved.c_str());
    #elif defined(__APPLE__)
    // Mac
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
    
    run(lipo_argv[0], lipo_argv);

    remove(saved.c_str());

    #else
    error() << "binary merging not implemented for this platform" << eom;
    return 1;
    #endif
  }
  
  return result!=0;
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

