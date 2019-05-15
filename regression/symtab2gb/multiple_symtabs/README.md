The `*.json_symtab` in this directory was created from the Ada source
files `*.adb` using the
[gnat2goto](https://github.com/diffblue/gnat2goto) compiler.

```
gnat2goto user.adb # produces user.json_symtab

# produces library.json_symtab
# and user.json_symtab
# the --no-cprover-start option is to prevent
# emitting a __CPROVER_start function for these modules,
# as there can only be one of those in a program

gnat2goto --no-cprover-start library.adb
gnat2goto --no-cprover-start user.adb
```

Note that as of now, this requires the patch found in
[this PR](https://github.com/diffblue/gnat2goto/pull/212)
