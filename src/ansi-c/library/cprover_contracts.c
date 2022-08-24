/* FUNCTION: __CPROVER_contracts_car_create */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_contracts_car_t
__CPROVER_contracts_car_create(void *ptr, __CPROVER_size_t size)
{
__CPROVER_HIDE:;
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "pointer-primitive"
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check disable "signed-overflow"
#pragma CPROVER check disable "undefined-shift"
#pragma CPROVER check disable "conversion"
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");
  __CPROVER_contracts_car_t car = {0};
  car.is_writable = ptr != 0;
  car.size = size;
  car.lb = ptr;
  __CPROVER_assert(
    size < __CPROVER_max_malloc_size,
    "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_ssize_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(
    !(offset > 0) |
      ((__CPROVER_size_t)offset + size < __CPROVER_max_malloc_size),
    "no offset bits overflow on CAR upper bound computation");
  car.ub = (void *)((char *)ptr + size);
#pragma CPROVER check pop
  return car;
}

/* FUNCTION: __CPROVER_contracts_car_set_create */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_car_set_create(
  __CPROVER_contracts_car_set_ptr_t set,
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_car_set_t)),
    "set writable");
#endif
  set->max_elems = max_elems;
  set->elems =
    __CPROVER_allocate(max_elems * sizeof(__CPROVER_contracts_car_t), 1);
}

/* FUNCTION: __CPROVER_contracts_car_set_insert */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

extern __CPROVER_size_t __CPROVER_max_malloc_size;

inline void __CPROVER_contracts_car_set_insert(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "pointer-overflow"
#pragma CPROVER check disable "pointer-primitive"
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check disable "signed-overflow"
#pragma CPROVER check disable "undefined-shift"
#pragma CPROVER check disable "conversion"
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert((set != 0) & (idx < set->max_elems), "no OOB access");
#endif
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");
  __CPROVER_contracts_car_t *elem = set->elems + idx;
  elem->is_writable = ptr != 0;
  elem->size = size;
  elem->lb = ptr;
  __CPROVER_assert(
    size < __CPROVER_max_malloc_size,
    "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_ssize_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(
    !(offset > 0) |
      ((__CPROVER_size_t)offset + size < __CPROVER_max_malloc_size),
    "no offset bits overflow on CAR upper bound computation");
  elem->ub = (void *)((char *)ptr + size);
#pragma CPROVER check pop
}

/* FUNCTION: __CPROVER_contracts_car_set_remove */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_car_set_remove(
  __CPROVER_contracts_car_set_ptr_t set,
  void *ptr)
{
  __CPROVER_HIDE:;
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  __CPROVER_size_t idx = set->max_elems;
  __CPROVER_contracts_car_t *elem = set->elems;
CAR_SET_REMOVE_LOOP:
  while(idx != 0)
  {
    if(object_id == __CPROVER_POINTER_OBJECT(elem->lb))
      elem->is_writable = 0;
    ++elem;
    --idx;
  }
}

/* FUNCTION: __CPROVER_contracts_car_set_contains */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_car_set_contains(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_contracts_car_t candidate)
{
__CPROVER_HIDE:;
  __CPROVER_bool incl = 0;
  __CPROVER_size_t idx = set->max_elems;
  __CPROVER_contracts_car_t *elem = set->elems;
CAR_SET_CONTAINS_LOOP:
  while(idx != 0)
  {
    incl |= candidate.is_writable & elem->is_writable &
            __CPROVER_same_object(elem->lb, candidate.lb) &
            (__CPROVER_POINTER_OFFSET(elem->lb) <=
             __CPROVER_POINTER_OFFSET(candidate.lb)) &
            (__CPROVER_POINTER_OFFSET(candidate.ub) <=
             __CPROVER_POINTER_OFFSET(elem->ub));
    ++elem;
    --idx;
  }

  return incl;
}

/* FUNCTION: __CPROVER_contracts_obj_set_create_indexed_by_object_id */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

extern __CPROVER_size_t __CPROVER_max_malloc_size;

int __builtin_clzll(unsigned long long);

inline void __CPROVER_contracts_obj_set_create_indexed_by_object_id(
  __CPROVER_contracts_obj_set_ptr_t set)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_obj_set_t)),
    "set writable");
#endif
  // compute the maximum number of objects that can exist in the
  // symex state from the number of object_bits/offset_bits
  // the number of object bits is determined by counting the number of leading
  // zeroes of the built-in constant __CPROVER_max_malloc_size;
  __CPROVER_size_t object_bits = __builtin_clzll(__CPROVER_max_malloc_size);
  __CPROVER_size_t nof_objects = 1UL << object_bits;
  set->max_elems = nof_objects;
  set->watermark = 0;
  set->nof_elems = 0;
  set->is_empty = 1;
  set->indexed_by_object_id = 1;
  set->elems = __CPROVER_allocate(nof_objects * sizeof(*(set->elems)), 1);
}

/* FUNCTION: __CPROVER_contracts_obj_set_create_append */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_obj_set_create_append(
  __CPROVER_contracts_obj_set_ptr_t set,
  __CPROVER_size_t max_elems)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_obj_set_t)),
    "set writable");
#endif
  set->max_elems = max_elems;
  set->watermark = 0;
  set->nof_elems = 0;
  set->is_empty = 1;
  set->indexed_by_object_id = 0;
  set->elems = __CPROVER_allocate(set->max_elems * sizeof(*(set->elems)), 1);
}

/* FUNCTION: __CPROVER_contracts_obj_set_add */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_obj_set_add(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(ptr) < set->max_elems, "no OOB access");
#endif
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->nof_elems =
    (set->elems[object_id] != 0) ? set->nof_elems : set->nof_elems + 1;
  set->elems[object_id] = ptr;
  set->is_empty = 0;
}

/* FUNCTION: __CPROVER_contracts_obj_set_append */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_obj_set_append(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(!(set->indexed_by_object_id), "not indexed by object id");
  __CPROVER_assert(set->watermark < set->max_elems, "no OOB access");
#endif
  set->nof_elems = set->watermark;
  set->elems[set->watermark] = ptr;
  set->watermark += 1;
  set->is_empty = 0;
}

/* FUNCTION: __CPROVER_contracts_obj_set_remove */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_obj_set_remove(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(ptr) < set->max_elems, "no OOB access");
#endif
  __CPROVER_size_t object_id = __CPROVER_POINTER_OBJECT(ptr);
  set->nof_elems = set->elems[object_id] ? set->nof_elems - 1 : set->nof_elems;
  set->is_empty = set->nof_elems == 0;
  set->elems[object_id] = 0;
}

/* FUNCTION: __CPROVER_contracts_obj_set_contains */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_obj_set_contains(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(ptr) < set->max_elems, "no OOB access");
#endif
  return set->elems[__CPROVER_POINTER_OBJECT(ptr)] != 0;
}

/* FUNCTION: __CPROVER_contracts_obj_set_contains_exact */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_obj_set_contains_exact(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->indexed_by_object_id, "indexed by object id");
  __CPROVER_assert(
    __CPROVER_POINTER_OBJECT(ptr) < set->max_elems, "no OOB access");
#endif
  return set->elems[__CPROVER_POINTER_OBJECT(ptr)] == ptr;
}

/* FUNCTION: __CPROVER_contracts_write_set_create */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_car_set_create(
  __CPROVER_contracts_car_set_ptr_t,
  __CPROVER_size_t);

inline void __CPROVER_contracts_obj_set_create_indexed_by_object_id(
  __CPROVER_contracts_obj_set_ptr_t);

inline void __CPROVER_contracts_obj_set_create_append(
  __CPROVER_contracts_obj_set_ptr_t,
  __CPROVER_size_t);

void __CPROVER_contracts_write_set_create(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t contract_assigns_size,
  __CPROVER_size_t contract_frees_size,
  __CPROVER_bool replacement,
  __CPROVER_bool assume_requires_ctx,
  __CPROVER_bool assert_requires_ctx,
  __CPROVER_bool assume_ensures_ctx,
  __CPROVER_bool assert_ensures_ctx)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    __CPROVER_w_ok(set, sizeof(__CPROVER_contracts_write_set_t)),
    "set writable");
#endif
  __CPROVER_contracts_car_set_create(
    &(set->contract_assigns), contract_assigns_size);
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(
    &(set->contract_frees));
  set->replacement = replacement;
  if(replacement)
  {
    __CPROVER_contracts_obj_set_create_append(
      &(set->contract_frees_replacement), contract_frees_size);
  }
  else
  {
    set->contract_frees_replacement.elems = 0;
  }
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(&(set->allocated));
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(&(set->deallocated));
  __CPROVER_contracts_obj_set_create_indexed_by_object_id(
    &(set->is_freshr_seen));
  set->linked_allocated = 0;
  set->assume_requires_ctx = assume_requires_ctx;
  set->assert_requires_ctx = assert_requires_ctx;
  set->assume_ensures_ctx = assume_ensures_ctx;
  set->assert_ensures_ctx = assert_ensures_ctx;
}

/* FUNCTION: __CPROVER_contracts_write_set_release */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_write_set_release(
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_write_set_t)),
    "set readable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->contract_assigns.elems), 0),
    "contract_assigns writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->contract_frees.elems), 0),
    "contract_frees writable");
  __CPROVER_assert(
    (set->replacement == 0) ||
      __CPROVER_rw_ok(&(set->contract_frees_replacement.elems), 0),
    "contract_frees_replacement writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->allocated.elems), 0), "allocated writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->deallocated.elems), 0), "deallocated writable");
  __CPROVER_assert(
    __CPROVER_rw_ok(&(set->deallocated.elems), 0), "is_freshr_seen writable");
#endif
  __CPROVER_deallocate(set->contract_assigns.elems);
  __CPROVER_deallocate(set->contract_frees.elems);
  if(set->replacement != 0)
  {
    __CPROVER_deallocate(set->contract_frees_replacement.elems);
  }
  __CPROVER_deallocate(set->allocated.elems);
  __CPROVER_deallocate(set->deallocated.elems);
  __CPROVER_deallocate(set->is_freshr_seen.elems);
  // do not free set->deallocated_linked->elems
  // since it is owned by another write_set instance
}

/* FUNCTION: __CPROVER_contracts_write_set_insert_assignable */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_car_set_insert(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size);

void __CPROVER_contracts_write_set_insert_assignable(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_insert(&(set->contract_assigns), idx, ptr, size);
}

/* FUNCTION: __CPROVER_contracts_write_set_insert_whole_object */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_car_set_insert(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size);

void __CPROVER_contracts_write_set_insert_whole_object(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_insert(
    &(set->contract_assigns),
    idx,
    ((char *)ptr) - __CPROVER_POINTER_OFFSET(ptr),
    __CPROVER_OBJECT_SIZE(ptr));
}

/* FUNCTION: __CPROVER_contracts_write_set_insert_object_from */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_car_set_insert(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size);

void __CPROVER_contracts_write_set_insert_object_from(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr)
{
  __CPROVER_contracts_car_set_insert(
    &(set->contract_assigns),
    idx,
    ptr,
    __CPROVER_OBJECT_SIZE(ptr) - __CPROVER_POINTER_OFFSET(ptr));
}

/* FUNCTION: __CPROVER_contracts_write_set_insert_object_upto */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline void __CPROVER_contracts_car_set_insert(
  __CPROVER_contracts_car_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size);

void __CPROVER_contracts_write_set_insert_object_upto(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_car_set_insert(&(set->contract_assigns), idx, ptr, size);
}

/* FUNCTION: __CPROVER_contracts_write_set_add_freeable */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_obj_set_add(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr);

void __CPROVER_contracts_obj_set_append(
  __CPROVER_contracts_obj_set_ptr_t set,
  void *ptr);

void __CPROVER_contracts_write_set_add_freeable(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  // we don't check yet that the pointer satisfies
  // the __CPROVER_contracts_is_freeable as precondition.
  // preconditions will be checked if there is an actual attempt
  // to free the pointer.

  // store pointer
  __CPROVER_contracts_obj_set_add(&(set->contract_frees), ptr);

  // append pointer if available
  if(set->replacement)
    __CPROVER_contracts_obj_set_append(&(set->contract_frees_replacement), ptr);
}

/* FUNCTION: __CPROVER_contracts_write_set_add_allocated */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_obj_set_add(__CPROVER_contracts_obj_set_ptr_t, void *);

void __CPROVER_contracts_write_set_add_allocated(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_obj_set_add(&(set->allocated), ptr);
}

/* FUNCTION: __CPROVER_contracts_write_set_record_dead */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_obj_set_remove(
  __CPROVER_contracts_obj_set_ptr_t,
  void *);

void __CPROVER_contracts_write_set_record_dead(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  __CPROVER_contracts_obj_set_remove(&(set->allocated), ptr);
}

/* FUNCTION: __CPROVER_contracts_write_set_record_deallocated */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

#if 0
inline void
__CPROVER_contracts_car_set_remove(__CPROVER_contracts_car_set_ptr_t, void *);

inline void
__CPROVER_contracts_obj_set_remove(__CPROVER_contracts_obj_set_ptr_t, void *);

inline void
__CPROVER_contracts_obj_set_add(__CPROVER_contracts_obj_set_ptr_t, void *);
#endif

void __CPROVER_contracts_write_set_record_deallocated(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->replacement == 0, "!replacement");
#endif
  // we need to record the deallocation to evaluate post conditions
  __CPROVER_contracts_obj_set_add(&(set->deallocated), ptr);
#if 0
  // We do not need to invalidate the object in all sets, because
  // the built-in CBMC checks already allow do detect accesses to DEAD
  // or deallocated memory
  __CPROVER_contracts_car_set_remove(&(set->contract_assigns), ptr);
  __CPROVER_contracts_obj_set_remove(&(set->contract_frees), ptr);
  __CPROVER_contracts_obj_set_remove(&(set->allocated), ptr);
#endif
}

/* FUNCTION: __CPROVER_contracts_write_set_check_allocated_deallocated_is_empty */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool
__CPROVER_contracts_write_set_check_allocated_deallocated_is_empty(
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
  return set->allocated.is_empty & set->deallocated.is_empty;
}

/* FUNCTION: __CPROVER_contracts_write_set_check_assignment */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_contracts_car_t
__CPROVER_contracts_car_create(void *, __CPROVER_size_t);

inline __CPROVER_bool __CPROVER_contracts_car_set_contains(
  __CPROVER_contracts_car_set_ptr_t,
  __CPROVER_contracts_car_t);

#if 0
inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
#  ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->replacement == 0, "!replacement");
#  endif
  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");

  __CPROVER_assert(
    (ptr == 0) | (__CPROVER_POINTER_OBJECT(ptr) < set->allocated.max_elems),
    "no OOB access");

  __CPROVER_contracts_car_t car = __CPROVER_contracts_car_create(ptr, size);
  if(!car.is_writable)
    return 0;

  if(set->allocated.elems[__CPROVER_POINTER_OBJECT(ptr)] != 0)
    return 1;

  return __CPROVER_contracts_car_set_contains(&(set->contract_assigns), car);
}
#else

// manually inlined/optimised
inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr,
  __CPROVER_size_t size)
{
__CPROVER_HIDE:;
#  ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->replacement == 0, "!replacement");
#  endif

#  pragma CPROVER check push
#  pragma CPROVER check disable "pointer"
#  pragma CPROVER check disable "pointer-primitive"
#  pragma CPROVER check disable "unsigned-overflow"
#  pragma CPROVER check disable "signed-overflow"
#  pragma CPROVER check disable "undefined-shift"
#  pragma CPROVER check disable "conversion"

  __CPROVER_assert(
    (ptr == 0) | (__CPROVER_POINTER_OBJECT(ptr) < set->allocated.max_elems),
    "no OOB access");

  __CPROVER_assert(
    ((ptr == 0) | __CPROVER_rw_ok(ptr, size)),
    "ptr NULL or writable up to size");

  // the range is not writable
  if(ptr == 0)
    return 0;

  // is ptr pointing to a locally allocated object ?
  if(set->allocated.elems[__CPROVER_POINTER_OBJECT(ptr)] != 0)
    return 1;

  // Compute the upper bound, perform inclusion check against contract-assigns
  __CPROVER_assert(
    size < __CPROVER_max_malloc_size,
    "CAR size is less than __CPROVER_max_malloc_size");
  __CPROVER_ssize_t offset = __CPROVER_POINTER_OFFSET(ptr);
  __CPROVER_assert(
    !(offset > 0) |
      ((__CPROVER_size_t)offset + size < __CPROVER_max_malloc_size),
    "no offset bits overflow on CAR upper bound computation");
  void *ub = (void *)((char *)ptr + size);
  __CPROVER_contracts_car_t *elem = set->contract_assigns.elems;
  __CPROVER_size_t idx = set->contract_assigns.max_elems;
  __CPROVER_bool incl = 0;

SET_CHECK_ASSIGNMENT_LOOP:
  while(idx != 0)
  {
    incl |=
      elem->is_writable & __CPROVER_same_object(elem->lb, ptr) &
      (__CPROVER_POINTER_OFFSET(elem->lb) <= __CPROVER_POINTER_OFFSET(ptr)) &
      (__CPROVER_POINTER_OFFSET(ub) <= __CPROVER_POINTER_OFFSET(elem->ub));
    ++elem;
    --idx;
  }
  return incl;
#  pragma CPROVER check pop
}
#endif

/* FUNCTION: __CPROVER_contracts_write_set_check_array_set */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t,
  void *,
  __CPROVER_size_t);

// Checks if the destination of an array_set operation assignable
// range = until the end of the object from dest
__CPROVER_bool __CPROVER_contracts_write_set_check_array_set(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest)
{
__CPROVER_HIDE:;
  return __CPROVER_contracts_write_set_check_assignment(
    set, dest, __CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest));
}

/* FUNCTION: __CPROVER_contracts_write_set_check_array_copy */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t,
  void *,
  __CPROVER_size_t);

// Checks if the destination of an array_copy operation is assignable.
// array_copy overwrites all of *dest (possibly using nondet values), even
// when *src is smaller.
__CPROVER_bool __CPROVER_contracts_write_set_check_array_copy(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest)
{
__CPROVER_HIDE:;
  return __CPROVER_contracts_write_set_check_assignment(
    set, dest, __CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest));
}

/* FUNCTION: __CPROVER_contracts_write_set_check_array_replace */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t,
  void *,
  __CPROVER_size_t);

// Checks if the destination of an array_replace operation is assignable.
// array_replace replaces at most size-of-*src bytes in *dest.
__CPROVER_bool __CPROVER_contracts_write_set_check_array_replace(
  __CPROVER_contracts_write_set_ptr_t set,
  void *dest,
  void *src)
{
__CPROVER_HIDE:;
  __CPROVER_size_t src_size =
    __CPROVER_OBJECT_SIZE(src) - __CPROVER_POINTER_OFFSET(src);
  __CPROVER_size_t dest_size =
    __CPROVER_OBJECT_SIZE(dest) - __CPROVER_POINTER_OFFSET(dest);
  __CPROVER_size_t size = dest_size < src_size ? dest_size : src_size;
  return __CPROVER_contracts_write_set_check_assignment(set, dest, size);
}

/* FUNCTION: __CPROVER_contracts_write_set_check_havoc_object */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool __CPROVER_contracts_write_set_check_assignment(
  __CPROVER_contracts_write_set_ptr_t,
  void *,
  __CPROVER_size_t);

__CPROVER_bool __CPROVER_contracts_write_set_check_havoc_object(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
  return __CPROVER_contracts_write_set_check_assignment(
    set,
    (char *)ptr - __CPROVER_POINTER_OFFSET(ptr),
    __CPROVER_OBJECT_SIZE(ptr));
}

/* FUNCTION: __CPROVER_contracts_write_set_check_deallocate */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

__CPROVER_bool
__CPROVER_contracts_obj_set_contains(__CPROVER_contracts_obj_set_ptr_t, void *);

__CPROVER_bool __CPROVER_contracts_write_set_check_deallocate(
  __CPROVER_contracts_write_set_ptr_t set,
  void *ptr)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->replacement == 0, "!replacement");
#endif
  // NULL pointers can always be passed to free
  if(!ptr)
    return 1;

  // is this one of the recorded pointers ?
  return __CPROVER_contracts_obj_set_contains_exact(
           &(set->contract_frees), ptr) ||
         __CPROVER_contracts_obj_set_contains_exact(&(set->allocated), ptr);
}

/* FUNCTION: __CPROVER_contracts_write_set_check_assigns_clause_inclusion */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool
__CPROVER_contracts_write_set_check_assigns_clause_inclusion(
  __CPROVER_contracts_write_set_ptr_t reference,
  __CPROVER_contracts_write_set_ptr_t candidate)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    reference->replacement == 0, "reference set in !replacement");
  __CPROVER_assert(candidate->replacement != 0, "candidate set in replacement");
#endif
  __CPROVER_bool incl = 1;
  __CPROVER_contracts_car_t *current = candidate->contract_assigns.elems;
  __CPROVER_size_t idx = candidate->contract_assigns.max_elems;
SET_CHECK_ASSIGNS_CLAUSE_INCLUSION_LOOP:
  while(idx != 0)
  {
    if(current->is_writable)
    {
      incl &= __CPROVER_contracts_write_set_check_assignment(
        reference, current->lb, current->size);
    }
    --idx;
    ++current;
  }
  return incl;
}

/* FUNCTION: __CPROVER_contracts_write_set_check_frees_clause_inclusion */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

inline __CPROVER_bool
__CPROVER_contracts_write_set_check_frees_clause_inclusion(
  __CPROVER_contracts_write_set_ptr_t reference,
  __CPROVER_contracts_write_set_ptr_t candidate)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    reference->replacement == 0, "reference set in !replacement");
  __CPROVER_assert(candidate->replacement != 0, "candidate set in replacement");
#endif
  __CPROVER_bool all_incl = 1;
  void **current = candidate->contract_frees_replacement.elems;
  __CPROVER_size_t idx = candidate->contract_frees_replacement.max_elems;
SET_CHECK_FREES_CLAUSE_INCLUSION_LOOP:
  while(idx != 0)
  {
    void *ptr = *current;
    all_incl &=
      __CPROVER_contracts_obj_set_contains(&(reference->contract_frees), ptr) ||
      __CPROVER_contracts_obj_set_contains(&(reference->allocated), ptr);
    --idx;
    ++current;
  }

  return all_incl;
}

/* FUNCTION: __CPROVER_contracts_write_set_deallocate_freeable */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

__CPROVER_bool nondet_CPROVER_bool();

// This function will be later remapped to the instrumented version of the
// free function provided by the CPROVER_library or any other implementation
// found in the goto model
__CPROVER_bool
__CPROVER_contracts_free(void *, __CPROVER_contracts_write_set_ptr_t);

void __CPROVER_contracts_write_set_record_deallocated(
  __CPROVER_contracts_write_set_ptr_t,
  void *);

void __CPROVER_contracts_write_set_deallocate_freeable(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_contracts_write_set_ptr_t target)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(set->replacement == 1, "set is in replacement");
  __CPROVER_assert(
    (target == 0) | (target->replacement == 0), "target is in !replacement");
#endif
  void **current = set->contract_frees_replacement.elems;
  __CPROVER_size_t idx = set->contract_frees_replacement.max_elems;
SET_DEALLOCATE_FREEABLE_LOOP:
  while(idx != 0)
  {
    void *ptr = *current;

    // call free only iff the pointer is valid preconditions are met
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "pointer-primitive"
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check disable "signed-overflow"
#pragma CPROVER check disable "undefined-shift"
#pragma CPROVER check disable "conversion"
    // avoid pointer-primitive checks on r_ok, dynobject and offset
    __CPROVER_bool preconditions =
      (ptr == 0) | (__CPROVER_r_ok(ptr, 0) & __CPROVER_DYNAMIC_OBJECT(ptr) &
                    (__CPROVER_POINTER_OFFSET(ptr) == 0));
#pragma CPROVER check pop
    // TODO make sure not to deallocate the same pointer twice
    if((ptr != 0) & preconditions & nondet_CPROVER_bool())
    {
      __CPROVER_contracts_free(ptr, 0);
      __CPROVER_contracts_write_set_record_deallocated(set, ptr);
      // also record effects in the caller write set
      if(target != 0)
        __CPROVER_contracts_write_set_record_deallocated(target, ptr);
    }
    --idx;
    ++current;
  }
}

/* FUNCTION: __CPROVER_contracts_link_is_freshr_allocated */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_link_is_freshr_allocated(
  __CPROVER_contracts_write_set_ptr_t write_set_postconditions,
  __CPROVER_contracts_write_set_ptr_t write_set_to_link)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    write_set_postconditions != 0, "write_set_postconditions not NULL");
#endif
  if((write_set_to_link != 0))
  {
    write_set_postconditions->linked_allocated =
      &(write_set_to_link->allocated);
  }
  else
  {
    write_set_postconditions->linked_allocated = 0;
  }
}

/* FUNCTION: __CPROVER_contracts_link_deallocated */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_link_deallocated(
  __CPROVER_contracts_write_set_ptr_t write_set_postconditions,
  __CPROVER_contracts_write_set_ptr_t write_set_to_link)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    write_set_postconditions != 0, "write_set_postconditions not NULL");
#endif
  if((write_set_to_link != 0))
  {
    write_set_postconditions->linked_deallocated =
      &(write_set_to_link->deallocated);
  }
  else
  {
    write_set_postconditions->linked_deallocated = 0;
  }
}

/* FUNCTION: __CPROVER_contracts_is_freshr */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void *malloc(__CPROVER_size_t);

void *__CPROVER_contracts_malloc(
  __CPROVER_size_t,
  __CPROVER_contracts_write_set_ptr_t);

void __CPROVER_contracts_obj_set_add(__CPROVER_contracts_obj_set_ptr_t, void *);

__CPROVER_bool
__CPROVER_contracts_obj_set_contains(__CPROVER_contracts_obj_set_ptr_t, void *);

__CPROVER_bool __CPROVER_contracts_is_freshr(
  void **elem,
  __CPROVER_size_t size,
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(
    __CPROVER_rw_ok(set, sizeof(__CPROVER_contracts_write_set_t)),
    "set readable");
#endif
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
#pragma CPROVER check disable "pointer-primitive"
#pragma CPROVER check disable "pointer-overflow"
#pragma CPROVER check disable "signed-overflow"
#pragma CPROVER check disable "unsigned-overflow"
#pragma CPROVER check disable "conversion"
  if(set->assume_requires_ctx)
  {
    __CPROVER_assert(
      (set->assert_requires_ctx == 0) & (set->assume_ensures_ctx == 0) &
        (set->assert_ensures_ctx == 0),
      "only one context flag at a time");
    // pass a null pointer to malloc si that the object does not get tracked
    // as assignable in the requires clause scope
    void *ptr = __CPROVER_contracts_malloc(size, 0);
    *elem = ptr;
    if(!ptr)
      return 0;
    // record fresh object in the map
    __CPROVER_contracts_obj_set_add(&(set->is_freshr_seen), ptr);
    return 1;
  }
  else if(set->assert_requires_ctx)
  {
    __CPROVER_assert(
      (set->assume_requires_ctx == 0) & (set->assume_ensures_ctx == 0) &
        (set->assert_ensures_ctx == 0),
      "only one context flag at a time");
    // check separation
    __CPROVER_contracts_obj_set_ptr_t seen = &(set->is_freshr_seen);
    __CPROVER_bool contains = __CPROVER_contracts_obj_set_contains(seen, *elem);
    __CPROVER_bool not_r_ok = !__CPROVER_r_ok(*elem, size);
    if(contains | not_r_ok)
      return 0;
    // record object
    __CPROVER_contracts_obj_set_add(seen, *elem);
    return 1;
  }
  else if(set->assert_ensures_ctx)
  {
    __CPROVER_assert(
      (set->assume_requires_ctx == 0) & (set->assume_ensures_ctx == 0) &
        (set->assert_requires_ctx == 0),
      "only one context flag at a time");
    __CPROVER_contracts_obj_set_ptr_t seen = &(set->is_freshr_seen);
    // check separation
    __CPROVER_bool not_contains =
      !__CPROVER_contracts_obj_set_contains(seen, *elem);
    __CPROVER_bool r_ok = __CPROVER_r_ok(*elem, size);
    __CPROVER_bool ok = not_contains & r_ok;
    // record object
    __CPROVER_contracts_obj_set_add(seen, *elem);
    return ok;
  }
  else if(set->assume_ensures_ctx)
  {
    __CPROVER_assert(
      (set->assume_requires_ctx == 0) & (set->assert_requires_ctx == 0) &
        (set->assert_ensures_ctx == 0),
      "only one context flag at a time");
    void *ptr = __CPROVER_contracts_malloc(size, 0);
    // record new object in linked allocated set
    __CPROVER_contracts_obj_set_add(set->linked_allocated, ptr);
    *elem = ptr;
    return (ptr != 0);
  }
  else
  {
    __CPROVER_assert(
      0, "__CPROVER_is_freshr is only called in requires or ensures clauses");
    __CPROVER_assume(0);
    return 0; // just to silence libcheck
  }
#pragma CPROVER check pop
}

/* FUNCTION: __CPROVER_contracts_write_set_havoc_get_assignable_target */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void *__CPROVER_contracts_write_set_havoc_get_assignable_target(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(idx < set->contract_assigns.max_elems, "no OOB access");
#endif
  __CPROVER_contracts_car_t car = set->contract_assigns.elems[idx];
  if(car.is_writable)
    return car.lb;
  else
    return (void *)0;
}

/* FUNCTION: __CPROVER_contracts_write_set_havoc_whole_object */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

void __CPROVER_contracts_write_set_havoc_whole_object(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(idx < set->contract_assigns.max_elems, "no OOB access");
#endif
  __CPROVER_contracts_car_t car = set->contract_assigns.elems[idx];
  if(car.is_writable)
    __CPROVER_havoc_object(car.lb);
}

/* FUNCTION: __CPROVER_contracts_write_set_havoc_object_from */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

char __VERIFIER_nondet_char();

void __CPROVER_contracts_write_set_havoc_object_from(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(idx < set->contract_assigns.max_elems, "no OOB access");
#endif
  __CPROVER_contracts_car_t car = set->contract_assigns.elems[idx];
  if(car.is_writable)
  {
    // TODO use __CPROVER_havoc_slice(car.lb, car.size);
    // when array_replace performance gets fixed
    char *target = car.lb;
    __CPROVER_size_t i = car.size;
    while(i != 0)
    {
      *(target) = __VERIFIER_nondet_char();
      target++;
      i--;
    }
  }
}

/* FUNCTION: __CPROVER_contracts_write_set_havoc_object_upto */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

char __VERIFIER_nondet_char();

void __CPROVER_contracts_write_set_havoc_object_upto(
  __CPROVER_contracts_write_set_ptr_t set,
  __CPROVER_size_t idx)
{
__CPROVER_HIDE:;
#ifdef DFCC_SELF_CHECK
  __CPROVER_assert(idx < set->contract_assigns.max_elems, "no OOB access");
#endif
  __CPROVER_contracts_car_t car = set->contract_assigns.elems[idx];
  if(car.is_writable)
  {
    // TODO use __CPROVER_havoc_slice(car.lb, car.size);
    // when array_replace gets fixed
    char *target = car.lb;
    __CPROVER_size_t i = car.size;
    while(i != 0)
    {
      *(target) = __VERIFIER_nondet_char();
      target++;
      i--;
    }
  }
}

/* FUNCTION: __CPROVER_contracts_is_freeable */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

extern void *__CPROVER_alloca_object;
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_new_object;
extern __CPROVER_bool __CPROVER_malloc_is_new_array;

__CPROVER_bool __CPROVER_contracts_is_freeable(
  void *ptr,
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
  __CPROVER_assert(
    (set != 0) &
      ((set->assume_requires_ctx == 1) | (set->assert_requires_ctx == 1) |
       (set->assume_ensures_ctx == 1) | (set->assert_ensures_ctx == 1)),
    "__CPROVER_is_freeable is used only in requires or ensures clauses");

  // These are all the preconditions checked by `free` of the CPROVER library
  __CPROVER_bool is_dynamic_object = (ptr == 0) | __CPROVER_DYNAMIC_OBJECT(ptr);
  __CPROVER_bool has_offset_zero =
    (ptr == 0) | (__CPROVER_POINTER_OFFSET(ptr) == 0);

  if((set->assume_requires_ctx == 1) || (set->assume_ensures_ctx == 1))
    return is_dynamic_object & has_offset_zero;

  // these conditions cannot be used in assumptions since they involve
  // demonic non-determinism
  __CPROVER_bool is_null_or_valid_pointer = (ptr == 0) | __CPROVER_r_ok(ptr, 0);
  __CPROVER_bool is_not_deallocated =
    (ptr == 0) | (__CPROVER_deallocated != ptr);
  __CPROVER_bool is_not_alloca = (ptr == 0) | (__CPROVER_alloca_object != ptr);
  __CPROVER_bool is_not_array = (ptr == 0) | (__CPROVER_new_object != ptr) |
                                (!__CPROVER_malloc_is_new_array);
  return is_null_or_valid_pointer & is_dynamic_object & has_offset_zero &
         is_not_deallocated & is_not_alloca & is_not_array;
}

/* FUNCTION: __CPROVER_contracts_is_freed */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

__CPROVER_bool
__CPROVER_contracts_obj_set_contains(__CPROVER_contracts_obj_set_ptr_t, void *);

__CPROVER_bool
__CPROVER_contracts_is_freed(void *ptr, __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
  __CPROVER_assert(
    (set != 0) &
      ((set->assume_ensures_ctx == 1) | (set->assert_ensures_ctx == 1)),
    "__CPROVER_is_freed is used only in ensures clauses");
  __CPROVER_assert(
    (set->linked_deallocated != 0), "linked_deallocated is not null");
  return __CPROVER_contracts_obj_set_contains(set->linked_deallocated, ptr);
}

/* FUNCTION: __CPROVER_contracts_check_replace_ensures_is_freed_preconditions */

#ifndef __CPROVER_contracts_write_set_t_defined
#  define __CPROVER_contracts_write_set_t_defined

typedef struct __CPROVER_contracts_car_t
{
  __CPROVER_bool is_writable;
  __CPROVER_size_t size;
  void *lb;
  void *ub;
} __CPROVER_contracts_car_t;

typedef struct __CPROVER_contracts_car_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // A array of car_t of size max_elems
  __CPROVER_contracts_car_t *elems;
} __CPROVER_contracts_car_set_t;

typedef __CPROVER_contracts_car_set_t *__CPROVER_contracts_car_set_ptr_t;

typedef struct __CPROVER_contracts_obj_set_t
{
  // maximum number of elements that can be stored in the set
  __CPROVER_size_t max_elems;
  // 1 + greatest used index in elems,
  // next usable index in elems if less than max_elems
  __CPROVER_size_t watermark;
  // number of elements currently in the elems array
  __CPROVER_size_t nof_elems;
  // true iff nof_elems is 0
  __CPROVER_bool is_empty;
  // true iff elems is indexed by the object id of the pointers
  __CPROVER_bool indexed_by_object_id;
  // array of void *pointers, indexed by their object ID
  // or some other order
  void **elems;
} __CPROVER_contracts_obj_set_t;

typedef __CPROVER_contracts_obj_set_t *__CPROVER_contracts_obj_set_ptr_t;

typedef struct __CPROVER_contracts_write_set_t
{
  // set of car derived from the contract (by rank)
  __CPROVER_contracts_car_set_t contract_assigns;
  // set of freeable pointers derived from the contract (by object id)
  __CPROVER_contracts_obj_set_t contract_frees;
  // set of freeable pointers derived from the contract (by rank)
  __CPROVER_contracts_obj_set_t contract_frees_replacement;
  // set of objects allocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t allocated;
  // set of objects deallocated by the function under analysis (by object id)
  __CPROVER_contracts_obj_set_t deallocated;
  // object set supporting the is_freshr predicate checks (by object id)
  __CPROVER_contracts_obj_set_t is_freshr_seen;
  // object set recording the is_freshr allocations in post conditions
  // (replacement mode only)
  __CPROVER_contracts_obj_set_ptr_t linked_allocated;
  // object set recording the deallocations (used by predicate is_freed)
  __CPROVER_contracts_obj_set_ptr_t linked_deallocated;
  // true iff this write set is used for contract replacement
  __CPROVER_bool replacement;
  // true iff this write set checks requires clauses in an assumption ctx
  __CPROVER_bool assume_requires_ctx;
  // true iff this write set checks requires clauses in an assertion ctx
  __CPROVER_bool assert_requires_ctx;
  // true iff this write set checks ensures clauses in an assumption ctx
  __CPROVER_bool assume_ensures_ctx;
  // true iff this write set checks ensures clauses in an assertion ctx
  __CPROVER_bool assert_ensures_ctx;
} __CPROVER_contracts_write_set_t;

typedef __CPROVER_contracts_write_set_t *__CPROVER_contracts_write_set_ptr_t;
#endif

__CPROVER_bool
__CPROVER_contracts_obj_set_contains(__CPROVER_contracts_obj_set_ptr_t, void *);

void __CPROVER_contracts_check_replace_ensures_is_freed_preconditions(
  void *ptr,
  __CPROVER_contracts_write_set_ptr_t set)
{
__CPROVER_HIDE:;
  __CPROVER_assert(
    set && ((set->assume_ensures_ctx == 1) | (set->assert_ensures_ctx == 1)),
    "__CPROVER_is_freed is used only in ensures clauses");

  if(set->assume_ensures_ctx)
  {
    __CPROVER_assert(
      __CPROVER_contracts_obj_set_contains(&(set->contract_frees), ptr),
      "assuming __CPROVER_is_freed(ptr) requires ptr to always exist in the "
      "contract's frees clause");
  }
}
