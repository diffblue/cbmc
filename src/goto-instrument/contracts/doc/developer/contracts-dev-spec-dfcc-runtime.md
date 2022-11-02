# Write Set Representation {#contracts-dev-spec-dfcc-runtime}

Back to @ref contracts-dev-spec-dfcc

@tableofcontents

## Write Set Data Structure {#contracts-dev-spec-dfcc-runtime-data}

The write set type and its basic operations are implemented in the file
@ref cprover_contracts.c.

Assignable ranges of bytes specified in assigns clauses are represented by
the @ref __CPROVER_contracts_car_t :

```c
// A conditionally writable range of bytes.
typedef struct __CPROVER_contracts_car_t
{
  // True iff __CPROVER_w_ok(lb, size) holds at creation
  __CPROVER_bool is_writable;

  //Size of the range in bytes
  __CPROVER_size_t size;

  //Lower bound address of the range
  void *lb;

  //Upper bound address of the range
  void *ub;
} __CPROVER_contracts_car_t;
```

Sets of @ref __CPROVER_contracts_car_t are represented as dynamic arrays
@ref __CPROVER_contracts_car_set_t, allocated by the
@ref __CPROVER_contracts_car_set_create function.

```c
typedef struct __CPROVER_contracts_car_set_t
{
  __CPROVER_size_t max_elems;
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;
```
The allocated size of a set is determined by the maximum number of targets
found in the assigns clause of the contract of interest.

Objects for which all bytes are assignable (or freeable) do not need to be
represented as @ref __CPROVER_contracts_car_t. They can be tracked using a
single pointer or object identifier.

Such sets of pointers are represented by the @ref __CPROVER_contracts_obj_set_t
data type.

```c
// A set of pointers.
typedef struct __CPROVER_contracts_obj_set_t
{
  // Maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;

  // next usable index in elems if less than max_elems
  /// (1 + greatest used index in elems)
  __CPROVER_size_t watermark;

  // Number of elements currently in the elems array
  __CPROVER_size_t nof_elems;

  // True iff nof_elems is 0
  __CPROVER_bool is_empty;

  // True iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;

  // Array of void *pointers, indexed by their object ID or some arbitrary order
  void **elems;
} __CPROVER_contracts_obj_set_t;
```

The `void **elem` array can be used in two distinct modes, controlled by
the field `indexed_by_object_id`:
1. When `indexed_by_object_id` is true, the container works in _indexed mode_.
   The `elems` array is allocated to a size `2^OBJECT_BITS`, and adding a
   pointer `p` to the set stores it at `elems[__CPROVER_POINTER_OBJECT(p)]`.
   This mode allows for efficient insertions and lookups but results in a sparse
   array;
2. When `indexed_by_object_id` is false, the container works in _append mode_.
   `elems` is allocated to a manually specified size, and adding pointer `p`
   stores it at `elems[watermark]` and increments `watermark` by one.
   This mode densely packs all pointers at the beginning of the array and allows
   for iteration over the stored pointers.


Last, actual write sets are represented by the type
@ref __CPROVER_contracts_write_set_t :

```c
// Runtime representation of a write set.
typedef struct __CPROVER_contracts_write_set_t
{
  // Set of car derived from the contract
  __CPROVER_contracts_car_set_t contract_assigns;

  // Set of freeable pointers derived from the contract (indexed mode)
  __CPROVER_contracts_obj_set_t contract_frees;

  // Set of freeable pointers derived from the contract (append mode)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;

  // Set of objects allocated by the function under analysis (indexed mode)
  __CPROVER_contracts_obj_set_t allocated;

  // Set of objects deallocated by the function under analysis (indexed mode)
  __CPROVER_contracts_obj_set_t deallocated;

  // Object set supporting the is_fresh predicate checks (indexed mode)
  __CPROVER_contracts_obj_set_ptr_t linked_is_fresh;

  // Object set recording the is_fresh allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;

  // Object set recording the deallocations (used by predicate was_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;

  // True iff this write set is used for contract replacement
  __CPROVER_bool replacement;

  // True iff the write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;

  // True iff the write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;

  // True iff the write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;

  // True iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;
```

## Write Set Operations {#contracts-dev-spec-dfcc-runtime-ops}

Direct links to @ref __CPROVER_contracts_write_set_t operations documentation
(full documentation available at @ref cprover_contracts.c) :
- @ref __CPROVER_contracts_write_set_create
- @ref __CPROVER_contracts_write_set_release
- @ref __CPROVER_contracts_write_set_insert_assignable
- @ref __CPROVER_contracts_write_set_insert_object_whole
- @ref __CPROVER_contracts_write_set_insert_object_from
- @ref __CPROVER_contracts_write_set_insert_object_upto
- @ref __CPROVER_contracts_write_set_add_freeable
- @ref __CPROVER_contracts_write_set_add_allocated
- @ref __CPROVER_contracts_write_set_record_dead
- @ref __CPROVER_contracts_write_set_record_deallocated
- @ref __CPROVER_contracts_write_set_check_allocated_deallocated_is_empty
- @ref __CPROVER_contracts_write_set_check_assignment
- @ref __CPROVER_contracts_write_set_check_array_set
- @ref __CPROVER_contracts_write_set_check_array_copy
- @ref __CPROVER_contracts_write_set_check_array_replace
- @ref __CPROVER_contracts_write_set_check_havoc_object
- @ref __CPROVER_contracts_write_set_check_deallocate
- @ref __CPROVER_contracts_write_set_check_assigns_clause_inclusion
- @ref __CPROVER_contracts_write_set_check_frees_clause_inclusion
- @ref __CPROVER_contracts_write_set_deallocate_freeable
- @ref __CPROVER_contracts_link_allocated
- @ref __CPROVER_contracts_link_deallocated
- @ref __CPROVER_contracts_is_fresh
- @ref __CPROVER_contracts_write_set_havoc_get_assignable_target
- @ref __CPROVER_contracts_write_set_havoc_object_whole
- @ref __CPROVER_contracts_write_set_havoc_slice
- @ref __CPROVER_contracts_is_freeable
- @ref __CPROVER_contracts_was_freed
- @ref __CPROVER_contracts_check_replace_ensures_was_freed_preconditions

---
 Prev | Next
:-----|:------
 @ref contracts-dev-spec-dfcc | @ref contracts-dev-spec-dfcc-instrument