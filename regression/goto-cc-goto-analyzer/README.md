This subdirectory is for tests where goto-cc is used to produce
a goto binary that is then passed to goto-analyzer. There is also
the option to have a custom script to produce the goto binary
should this require special handling or multiple steps. This
script is run if the root name of the test file has a script with
the same filename. For example, if the desc file specifies 
test.c as the test file then the chain.sh script will check for
the existence of test.sh and if test.sh exists then it will be used
to build the goto binary (assumed to be test.gb).
