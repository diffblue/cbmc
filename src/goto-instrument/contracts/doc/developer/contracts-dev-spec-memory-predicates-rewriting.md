# Rewriting User-Defined Memory Predicates {#contracts-dev-spec-memory-predicates-rewriting}

Back to top @ref contracts-dev-spec

@tableofcontents

The C extensions for contract specification provide three pointer-related memory
predicates:

```c
// Holds iff ptr is pointing to an object distinct to all objects pointed to by
// other __CPROVER_is_fresh occurrences in the contract's pre and post conditions
__CPROVER_bool __CPROVER_is_fresh(void *ptr, size_t size);

// Holds iff the function pointer \p fptr points to a function satisfying
// \p contract.
__CPROVER_bool __CPROVER_obeys_contract(void (*fptr)(void), void (*contract)(void));
```

Users are free to call these predicates from requires and ensures clauses.
Users can also define their own functions in terms of these predicates, and call
them from requires and ensures clauses, but not from the program under analysis.

For instance, one could write a predicate defining linked lists of at most `len`
elements as follows:

```c
typedef struct list_t
{
  int value;
  struct list_t *next;
} list_t;

// true iff list of len nodes with values in [-10,10]
bool is_list(list_t *l, size_t len)
{
  if(len == 0)
    return l == NULL;
  else
    return __CPROVER_is_fresh(l, sizeof(*l)) && -10 <= l->value &&
           l->value <= 10 && is_list(l->next, len - 1);
}
```

One can also simply describe finite nested structures:

```c
typedef struct buffer_t
{
  size_t size;
  char *arr;
  char *cursor;
} buffer_t;

typedef struct double_buffer_t
{
  buffer_t *first;
  buffer_t *second;
} double_buffer_t;

bool is_sized_array(char *arr, size_t size)
{
  return __CPROVER_is_fresh(arr, size);
}

bool is_buffer(buffer_t *b)
{
  return __CPROVER_is_fresh(b, sizeof(*b)) && (0 < b->size && b->size <= 10) &&
         is_sized_array(b->arr, b->size);
}

bool is_double_buffer(double_buffer_t *b)
{
  return __CPROVER_is_fresh(b, sizeof(*b)) && is_buffer(b->first) &&
         is_buffer(b->second);
}
```

By rewriting such user-defined predicate we achieve two things:
1. in assumption contexts, evaluating the predicate allocates the data stucture
  specified by the predicate;
2. in assertion contexts, evaluating the predicate checks that a given pointer
  satisfies the predicate definition;

To achieve point 1., we apply an instrumentation pass to transform the
user-defined functions into functions that take their pointer arguments by
reference instead of by value, so that enforcing the assumption described by the
predicate can be done by updating the pointer in place using a side effect.

## Collecting user-defined memory predicates {#contracts-dev-spec-memory-predicate-collect}

We first run a pass that collects all user-defined functions that are defined
in terms of one of the three core memory predicates using this fixpoint
algorithm:

```
predicates = {};
updated = true;
while(updated)
{
  updated = false;
  for(function : goto_model.goto_functions.function_map)
  {
    if(!predicates.contains(function) &&
      (calls_core_predicate(function) ||
        calls_one_of(function, predicates)))
    {
      predicates.insert(function);
      updated = true;
    }
  }
}
```

## Rewriting user-defined memory predicates {#contracts-dev-spec-memory-predicate-rewrite}

We only support sets of predicates that are non-recursive or self-recursive
(i.e. predicates that call themselves directly).
We build a graph representing the P-calls-Q relation, omitting edges for
self-recursion, and try to sort it topologically. If the sort succeeds we
rewrite the predicates in topological order, so that when instrumenting P any
other predicate Q it calls is already instrumented and we know which parameters
of Q have been lifted. If the topological sort fails, then it means the predicate
are mutually recursive and we abort instrumentation.

Rewriting a user-defined memory predicate P consists in:
- Identifying the subset of parameters of P which get passed to a core predicate
  or a user-defined predicate in a lifted position;
- In the signature of P, lift all such parameters to pointer-to-pointer types;
- In the body of P, rewrite all occurences of a lifted parameter `p` into `*p`
  (this brings back type coherence in the body of P);
- For calls to memory predicates Q, add an `address_of` operator to arguments
  passed on a lifted parameter of Q;

Once these transformations are applied, the body of the predicate is well typed
and the predicate now takes the pointers on which it operates by reference
instead of by value. By doing so, the P gains the capability to update in place
the memory location hold the pointer value subject to the predicate definition.

The last step of the rewriting is to apply the normal DFCC instrumentation
which adds a write set parameter to the function, instruments it for side
effect checking, and maps core memory predicates to their implementations.

On our previous list example, this yields the following result:

```c
bool is_list(list_t **l, size_t len,
  __CPROVER_contracts_write_set_ptr_t write_set)
{
  if(len == 0)
    return (*l) == NULL;
  else
    return __CPROVER_contracts_is_fresh(&(*l), sizeof(*(*l)), write_set) &&
      -10 <= (*l)->value && (*l)->value <= 10 &&
      is_list(&((*l)->next), len-1, write_set);
}
```

On the nested structs example, it gives the following result:

```c
bool is_sized_array(char **arr, size_t size,
  __CPROVER_contracts_write_set_ptr_t write_set)
{
  return __CPROVER_contracts_is_fresh(&(*arr), size, write_set);
}

bool is_buffer(buffer_t **b,
  __CPROVER_contracts_write_set_ptr_t write_set)
{
  return __CPROVER_contracts_is_fresh(&(*b), sizeof(*(*b)), write_set) &&
    (0 < (*b)->size && (*b)->size <= 10) &&
    is_sized_array(&(*b)->arr, (*b)->size, write_set);
}

bool is_double_buffer(double_buffer_t **b,
  __CPROVER_contracts_write_set_ptr_t write_set)
{
  return __CPROVER_contracts_is_fresh(&(*b), sizeof(*(*b)), write_set) &&
      is_buffer(&((*b)->first), write_set) &&
      is_buffer(&((*b)->second), write_set);
}
```

The write_set parameter carries assumption/assertion context flags, so that the
implementation of the core-predicates know when to update the pointers in place
using malloc and assignments to make the predicates hold.

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-spec-rewriting | @ref contracts-dev-spec-dfcc