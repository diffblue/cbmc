# Checking a Contract Against a Function {#contracts-dev-spec-contract-checking}

Back to top @ref contracts-dev-spec

@tableofcontents

## Swapping-and-Wrapping Functions

The first operation one can do with contracts is to check if a function satisfies
a contract.

Let us consider a contract `c`, a function `foo` and a proof harness `main`.

```c
// A contract
int c(int *a, int *b)
__CPROVER_requires(R)
__CPROVER_ensures(E)
__CPROVER_assigns(A)
__CPROVER_frees(F)
;

// A function
int foo(int *a, int *b)
{
  // does something with a and b
}

// A proof harness for foo
void main()
{
  // allocate non-deterministic parameters
  int *a = ...;
  int *b = ...;

  // call the function under verification
  foo(a, b);
}
```

In order to check the contract `c` against `foo` in the context set up by the
harness `main`, we apply a _swap-and-wrap_ transformation to the function `foo`:

The **swapping step** consists in creating a fresh function `foo_swapped` with the
same interface as `foo` and swapping the body of `foo` into `foo_swapped`,
while instrumenting it for [frame condition checking](@ref contracts-dev-spec-dfcc)
against A and F.

```c
// The old foo function
int foo_swapped(int *a, int *b)
{
  // does something with a and b (now checked against A and F)
}
```

The **wrapping step** consists in creating a new body for `foo`
where the swapped function gets called between precondition and postcondition
checking instructions generated from the contract:

```c
// The old foo function
int foo(int *a, int *b)
{
  // preconditions code goes here
  // ...

  int reval = foo_swapped(a, b);

  // postconditions code code goes here
  // ...
  return retval;
}
```

After the *swap-and-wrap* transformation is applied, the `main` function calls
the contract-checking wrapper. Analysing this model with CBMC will effectively
check that the initial `foo` (now `foo_swapped`), under the assumption that the
contract preconditions hold, satisfies the postconditions and the frame
conditions of the contract.

```c
// add these static variables to the model
static bool foo_check_started = false;
static bool foo_check_completed = false;

ret_t foo(foo-parameters, write_set_t caller_write_set) {

  assert(!foo_check_started, "recursive calls to foo not allowed");
  assert(!foo_check_completed, "foo can only be called once from the harness");
  foo_check_started = true;

  // create an empty write set to check for side effects in requires clauses
  __CPROVER_contracts_write_set_t __requires_write_set;
  __CPROVER_contracts_write_set_ptr_t requires_write_set = & __requires_write_set;
  __CPROVER_contracts_write_set_create(requires_write_set, 0, 0);

  // assume requires clauses
  assume(contract::requires(foo_params, requires_write_set));
  assume(contract::requires_contract(foo_params, requires_write_set));

  // check that requires clause do not allocate or deallocate dynamic memory
  assert(__CPROVER_contracts_write_set_allocated_deallocated_is_empty(requires_write_set));
  __CPROVER_contracts_write_set_release(requires_write_set);

  // snapshot history variables
  hist1_t hist1 = ...;
  hist2_t hist2 = ...;

  // populate the contract write set
  __CPROVER_contracts_write_set_t __contract_write_set;
  __CPROVER_contracts_write_set_ptr_t contract_write_set = &__contract_write_set;

  // allocate and populate the contract write set
  __CPROVER_contracts_write_set_create(contract_write_set, assigns_clause_size(c), frees_clause_size(c));
  contract::assigns(contract_write_set, empty_write_set);
  contract::frees(contract_write_set, empty_write_set);

  // call the function
  ret_t retval;
  retval = foo_swapped(foo_params, contact_write_set);
  __CPROVER_contracts_write_set_release(contract_write_set);

  // create an empty write set to check for side effects in requires clauses
  __CPROVER_contracts_write_set_t __ensures_write_set;
  __CPROVER_contracts_write_set_ptr_t ensures_write_set = & __ensures_write_set;
  __CPROVER_contracts_write_set_create(ensures_write_set, 0, 0);

  // check post conditions
  assert(contract::ensures(foo_params, ensures_write_set));
  assert(contract::ensures_contract(foo_params, ensures_write_set));

  // check that requires clause do not allocate or deallocate dynamic memory
  assert(__CPROVER_contracts_write_set_allocated_deallocated_is_empty(ensures_write_set));
  __CPROVER_contracts_write_set_release(ensures_write_set);

  foo_check_completed = true;

  return retval;
}
```

## Wrapping Recursive Functions

If the function to be checked is potentially recursive, we generate the wrapper
function body such that the first call trigger the contract checking, and any
subsequent call triggers the contract replacement logic as described in
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
 @ref contracts-dev-spec-harness | @ref contracts-dev-spec-contract-replacement