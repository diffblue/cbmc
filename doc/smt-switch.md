\ingroup module_hidden
\page smt_switch SMT Switch

\section compiling_smt_switch Compiling SMT Switch

See [COMPILING.md](https://github.com/diffblue/cbmc/blob/develop/COMPILING.md#Use-SMT-Switch-interface) for details on how to compile the SMT Switch library.

\section using_smt_switch Using the SMT Switch Library.

Having compiled CBMC with appropriate flags, you can add the following `target_lik_libraries` to a `CMakeLists.txt`:

```
if (use_smt_switch)
    target_link_libraries(
            <target>
            smt-switch
            smt-switch-cvc4
    )
endif ()
```

Which will allow you to use the SMT switch API.

There is a compile flag `HAVE_SMT_SWITCH` which can be used to enable code that requires SMT Switch.

See [unit/solvers/smt_switch.cpp](../../unit/solvers/smt_switch.cpp) for an example test that uses the SMT switch API.
