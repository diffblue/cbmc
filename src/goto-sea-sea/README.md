\ingroup module_hidden
\defgroup goto-sea-sea goto-sea-sea

# Folder goto-sea-sea

\author Martin Brain

`goto-sea-sea` is a compiler replacement that just performs the first step of
the process; converting C or C++ programs to goto-binaries. It is
intended to be dropped in to an existing build procedure in place of the
compiler, thus it emulates flags that would affect the semantics of the
code produced. Which set of flags are emulated depends on the naming of
the `goto-sea-sea/` binary. If it is called `goto-sea-sea` then it emulates GCC
flags, `goto-armcc` emulates the ARM compiler, `goto-cl` emulates VCC
and `goto-cw` emulates the Code Warrior compiler. The output of this
tool can then be used with `cbmc` or `goto-inkstrument`.
