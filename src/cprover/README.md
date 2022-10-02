\ingroup module_hidden
\defgroup cprover cprover

# Folder CPROVER

This contains an experimental encoding from C programs into a Constrained
Horn Clause (CHC) system.  The satisfiability of the CHC system implies that
the assertions (as given or generated) hold.  The executable performs the
encoding and the solving of the CHC system.

The formula generated uses custom operators that model program heaps,
including memory allocation, memory deallocation, and pointer dereferencing. 
Owing to these custom operators, standard CHC solvers are not applicable.

To run the encoding and the solver on aws-c-common and coreJSON, first
ensure that the `cprover` binary is in your `PATH`.  Then perform the
following steps.

# aws-c-common

```sh
git clone https://github.com/kroening/aws-c-common
cd aws-c-common
git checkout cprover
cd verification/cprover
./setup
./script
```

# coreJSON

```sh
git clone https://github.com/kroening/coreJSON
cd coreJSON
git checkout cprover
cd test/cprover
./setup
./script
```

