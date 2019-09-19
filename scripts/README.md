A collection of utility scripts and script applications.

# pretty-printers 

GDB:

Pretty-printers for CBMC that enable easier debugging in IDEs and mitigate
certain crashes due to the way some objects' memory is shared.

Currently it deals with:
* irep_idt
* dstring
* instructiont

To install:

1. Navigate to /pretty-printers/gdb.
2. Run install.py with python 3+.
3. If an exception occurs, create an empty '.gdbinit' file in your home
    folder, and copy/paste the blob of code at the top of the install.py file.
    
The .gdbinit file is used by GDB during start-up to run any initial commands or 
scripts, and the code injects the pretty-printers during that.

Nothing else is required to get the pretty-printers to work, beside using 
GDB to debug the code.

# options

There is an `options.json` file to control any internal options.

List of options.

`clion_pretty_printers`: Some pretty printers work differently if you're
running them in CLion versus baseline GDB, and aren't very pretty if you 
look at them in the alternate view. Set to true if you use CLion, false if
you use commandline GDB. Defaults to true. 
