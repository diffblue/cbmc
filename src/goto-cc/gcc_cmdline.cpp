/*******************************************************************\

Module: A special command line object for the gcc-like options

Author: CM Wintersteiger, 2006

\*******************************************************************/

#include <string.h>

#include <iostream>

#include "gcc_cmdline.h"

/*******************************************************************\
 
Function: gcc_cmdlinet::parse
 
  Inputs: argument count, argument strings
 
 Outputs: none
 
 Purpose: parses the commandline options into a cmdlinet
 
\*******************************************************************/

bool gcc_cmdlinet::parse(int argc, const char **argv)
{
  for(int i=1; i<argc; i++)
  {
    int optnr;
    cmdlinet::optiont option;
    option.isset=true;

    if(strcmp(argv[i], "-")==0 ||
       argv[i][0]!='-')
    {
      args.push_back(argv[i]);
      continue;
    }    

    if(strncmp(argv[i], "--", 2)==0)
    {
      if(strlen(argv[i])==3)
      {
        option.islong=false;
        option.optchar=argv[i][2];
        optnr=getoptnr(option.optchar);
      }
      else
      {
        option.islong=true;
        option.optstring=argv[i]+2;
        option.optchar=0;
        optnr=getoptnr(option.optstring);
      }
    }
    else
    {
      if(strlen(argv[i])==2)
      {
        option.islong=false;
        option.optchar=argv[i][1];
        optnr=getoptnr(option.optchar);
      }
      else
      {
        option.islong=true;
        option.optstring=argv[i]+1;
        option.optchar=0;
        optnr=getoptnr(option.optstring);
      }
    }
    
    // new?
    if(optnr==-1)
    {
      options.push_back(option);
      optnr=options.size()-1;
    }

    options[optnr].isset=true;
    
    if( // options that don't have any arguments
      strcmp(argv[i], "--dot")==0 || // NON-GCC
      strcmp(argv[i], "--show-symbol-table")==0 || // NON-GCC
      strcmp(argv[i], "--show-function-table")==0 || // NON-GCC
      strcmp(argv[i], "--ppc-macos")==0 || // NON-GCC
      strcmp(argv[i], "--i386-linux")==0 || // NON-GCC
      strcmp(argv[i], "--i386-win32")==0 || // NON-GCC
      strcmp(argv[i], "--i386-macos")==0 || // NON-GCC
      strcmp(argv[i], "--winx64")==0 || // NON_GCC
      strcmp(argv[i], "--string-abstraction")==0 || // NON-GCC
      strcmp(argv[i], "--no-library")==0 || // NON-GCC
      strcmp(argv[i], "--16")==0 || // NON-GCC
      strcmp(argv[i], "--32")==0 || // NON-GCC
      strcmp(argv[i], "--64")==0 || // NON-GCC
      strcmp(argv[i], "--little-endian")==0 || // NON-GCC
      strcmp(argv[i], "--big-endian")==0 || // NON-GCC
      strcmp(argv[i], "--unsigned-char")==0 || // NON-GCC
      strcmp(argv[i], "--no-arch")==0 || // NON-GCC            
      strcmp(argv[i], "--xml")==0 || // NON-GCC
      strcmp(argv[i], "--partial-inlining")==0 || // NON-GCC
      strcmp(argv[i], "-h")==0 || strcmp(argv[i], "--help")==0 || // NON-GCC
      strcmp(argv[i], "-?")==0 || // NON-GCC
      strcmp(argv[i], "-r")==0 || // for ld mimicking
      strcmp(argv[i], "-c")==0 || strcmp(argv[i], "-S")==0 ||
      strcmp(argv[i], "-E")==0 || strcmp(argv[i], "-combine")==0 ||
      strcmp(argv[i], "-pipe")==0 || strcmp(argv[i], "-pass-exit-codes")==0 ||
      strcmp(argv[i], "-v")==0 || strcmp(argv[i], "-###")==0 ||
      strcmp(argv[i], "-help")==0 || strcmp(argv[i], "-target-help")==0 ||
      strcmp(argv[i], "--version")==0 || strcmp(argv[i], "-ansi")==0 ||
      strcmp(argv[i], "-trigraphs")==0 ||
      strcmp(argv[i], "-no-integrated-cpp")==0 ||
      strcmp(argv[i], "-traditional")==0 ||
      strcmp(argv[i], "-traditional-cpp")==0 ||
      strcmp(argv[i], "-nostdinc++")==0 || strcmp(argv[i], "-gen-decls")==0 ||
      strcmp(argv[i], "-pedantic")==0 ||
      strcmp(argv[i], "-pedantic-errors")==0 ||
      strcmp(argv[i], "-w")==0 || strcmp(argv[i], "-dumpspecs")==0 ||
      strcmp(argv[i], "-dumpmachine")==0 ||
      strcmp(argv[i], "-dumpversion")==0 || strcmp(argv[i], "-g")==0 ||
      strcmp(argv[i], "-gcoff")==0 || strcmp(argv[i], "-gdwarf-2")==0 ||
      strcmp(argv[i], "-ggdb")==0 || strcmp(argv[i], "-gstabs")==0 ||
      strcmp(argv[i], "-gstabs+")==0 || strcmp(argv[i], "-gvms")==0 ||
      strcmp(argv[i], "-gxcoff")==0 || strcmp(argv[i], "-gxcoff+")==0 ||
      strcmp(argv[i], "-p")==0 || strcmp(argv[i], "-pg")==0 ||
      strcmp(argv[i], "-print-libgcc-file-name")==0 ||
      strcmp(argv[i], "-print-multi-directory")==0 ||
      strcmp(argv[i], "-print-multi-lib")==0 ||
      strcmp(argv[i], "-print-search-dirs")==0 || strcmp(argv[i], "-Q")==0 ||
      strcmp(argv[i], "-save-temps")==0 || strcmp(argv[i], "-time")==0 ||
      strcmp(argv[i], "-O")==0 || strcmp(argv[i], "-O0")==0 ||        
      strcmp(argv[i], "-O1")==0 || strcmp(argv[i], "-O2")==0 ||
      strcmp(argv[i], "-O3")==0 || strcmp(argv[i], "-Os")==0 ||
      strcmp(argv[i], "-C")==0 || strcmp(argv[i], "-E")==0 ||
      strcmp(argv[i], "-H")==0 || strcmp(argv[i], "-M")==0 ||
      strcmp(argv[i], "-MM")==0 || strcmp(argv[i], "-MF")==0 ||
      strcmp(argv[i], "-MG")==0 || strcmp(argv[i], "-MP")==0 ||
      strcmp(argv[i], "-MQ")==0 || strcmp(argv[i], "-MT")==0 ||
      strcmp(argv[i], "-MD")==0 || strcmp(argv[i], "-MMD")==0 ||
      strcmp(argv[i], "-nostdinc")==0 || strcmp(argv[i], "-P")==0 ||
      strcmp(argv[i], "-remap")==0 || strcmp(argv[i], "-undef")==0 ||
      strcmp(argv[i], "-nostdinc")==0 || 
      strcmp(argv[i], "-nostartfiles")==0 ||
      strcmp(argv[i], "-nodefaultlibs")==0 ||
      strcmp(argv[i], "-nostdlib")==0 || strcmp(argv[i], "-pie")==0 ||
      strcmp(argv[i], "-rdynamic")==0 || strcmp(argv[i], "-s")==0 ||
      strcmp(argv[i], "-static")==0 || 
      strcmp(argv[i], "-static-libgcc")==0 || strcmp(argv[i], "-shared")==0 ||
      strcmp(argv[i], "-symbolic")==0 ||
      strcmp(argv[i], "-Bprefix")==0 ||
      strcmp(argv[i], "-iquotedir")==0 ||
      strcmp(argv[i], "-EB")==0 ||
      strcmp(argv[i], "-EL")==0
    )
    {
      // nothing; is added and recognized.
    }
    else if(strncmp(argv[i], "-f", 2)==0) // f-options
    {
    }
    else if(strncmp(argv[i], "-W", 2)==0) // W-options
    {
      // "Wp,..." is s special case
      if(strncmp(argv[i], "-Wp,", 4)==0)
      {
        option.optstring="Wp,";
        option.optchar=0;
        optnr=getoptnr(option.optstring);
        if(optnr==-1)
        {
          options.push_back(option);
          optnr=options.size()-1;
        }
        options[optnr].isset=true;
        options[optnr].values.push_back(argv[i]+4);
      }
    }
    else if(strncmp(argv[i], "-m", 2)==0) // m-options
    {
    }
    else if( // options that have a separated _or_ concatenated argument
        strncmp(argv[i], "-o", 2)==0 ||
        strncmp(argv[i], "-x", 2)==0 ||
        strncmp(argv[i], "-I", 2)==0 ||
        strncmp(argv[i], "-V", 2)==0 ||
        strncmp(argv[i], "-D", 2)==0 ||
        strncmp(argv[i], "-L", 2)==0 ||
        strncmp(argv[i], "-MF", 3)==0
    )
    {
      options[optnr].hasval=true;
      if(strlen(argv[i])==2)
      {
        options[optnr].optstring="";
        options[optnr].optchar=argv[i][1];
        if(i!=argc-1)
        {
          options[optnr].values.push_back(argv[i+1]);
          i++;
        }
        else
          options[optnr].values.push_back("");
      }
      else
      {
        option=options[optnr];
        option.optstring="";
        option.optchar=argv[i][1];
        optnr=getoptnr(option.optchar);
        if(optnr==-1)
        {
          options.push_back(option);
          optnr = options.size()-1;
        }
        options[optnr].isset=true;
        
        options[optnr].values.push_back(argv[i]+2);
      }
    } 
    else if( // options that have a separated argument
        strcmp(argv[i], "--verbosity")==0 || // NON-GCC
        strcmp(argv[i], "--function")==0 || // NON-GCC
        strcmp(argv[i], "-aux-info")==0 ||
        strcmp(argv[i], "--param")==0 ||
        strcmp(argv[i], "-idirafter")==0 ||
        strcmp(argv[i], "-include")==0 ||
        strcmp(argv[i], "-imacros")==0 ||
        strcmp(argv[i], "-iprefix")==0 ||
        strcmp(argv[i], "-iwithprefix")==0 ||
        strcmp(argv[i], "-iwithprefixbefore")==0 ||
        strcmp(argv[i], "-isystem")==0 ||
        strcmp(argv[i], "-isysroot")==0 ||
        strcmp(argv[i], "-Xpreprocessor")==0 ||
        strcmp(argv[i], "-Xassembler")==0 ||
        strcmp(argv[i], "-Xlinker")==0 ||
        strcmp(argv[i], "-u")==0 ||
        strcmp(argv[i], "-V")==0 ||
        strcmp(argv[i], "-b")==0
    )
    {
      options[optnr].hasval=true;

      if(i!=argc-1)
      {
        options[optnr].values.push_back(argv[i+1]);
        i++;
      }
      else
        options[optnr].values.push_back("");
    }
    else if( // options that have a concatonated argument
      strncmp(argv[i], "-d", 2)==0 ||
      strncmp(argv[i], "-g", 2)==0 ||
      strncmp(argv[i], "-A", 2)==0 ||
      strncmp(argv[i], "-U", 2)==0 ||
      strncmp(argv[i], "-l", 2)==0
    )
    {
      option = options[optnr];
      option.optstring = "";  
      option.optchar = argv[i][1];
      optnr=getoptnr(option.optchar);
      if(optnr==-1)
      {
        options.push_back(option);
        optnr = options.size()-1;
      }
      options[optnr].isset=true;
      if(strlen(argv[i])>2)
      {
        options[optnr].hasval = true;
        options[optnr].values.push_back(argv[i]+2);
      }
    }
    else if( // options that have an = argument
      strncmp(argv[i], "-std", 4)==0 ||
      strncmp(argv[i], "-print-file-name", 16)==0 ||
      strncmp(argv[i], "-print-prog-name", 16)==0 ||
      strncmp(argv[i], "-specs", 6)==0 ||
      strncmp(argv[i], "--sysroot", 9)==0
    )
    {
      const char *inx=strchr(argv[i], '=');
      if(inx!=NULL)
      {
        option = options[optnr];
        option.optstring = 
          option.optstring.substr(0, option.optstring.find("=",0)-1);
        optnr=getoptnr(option.optstring);
        if(optnr==-1)
        {
          options.push_back(option);
          optnr = options.size()-1;
        }
        options[optnr].isset=true;
                  
        options[optnr].hasval = true;
        options[optnr].values.push_back(inx+1);
      }
    }
    else
    { // unrecognized option
      std::cout << "Warning: uninterpreted gcc option '" << argv[i] << "'" << std::endl;
    }
  }

  return false;
}
