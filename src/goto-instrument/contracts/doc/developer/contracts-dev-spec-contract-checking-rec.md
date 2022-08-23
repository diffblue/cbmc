# Checking a Contract Against a Recursive Function {#contracts-dev-spec-contract-checking-rec}

Back to top @ref contracts-dev-spec

@tableofcontents


If the function to be checked is potentially recursive, we generate the wrapper
function body such that the first call triggers the contract checking logic
described in @ref contracts-dev-spec-contract-checking, and any subsequent call
triggers the contract replacement logic described in
@ref contracts-dev-spec-contract-replacement :


```c
static bool foo_check_started = false;
static bool foo_check_completed = false;

ret_t foo(foo_params, write_set_t caller_write_set) {
  assert(!foo_check_completed, "foo can only be called once from the harness");

   // first call, check the contract
  if(!foo_check_started) {
    // non-recursive contract checking instructions go here
    // ...
   return retval;
  } else {
    // contract replacement instructions
    // ...
    return retval;
  }
}
```

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-contract-checking-rec | @ref contracts-dev-spec-contract-replacement