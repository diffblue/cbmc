// Test suite for uninitialized local variable checks.
// Covers: basic cases, control flow, address-taken, structs/unions/arrays,
// function calls, and edge cases.

#include <assert.h>
#include <stdlib.h>

// === Phase 1: Basic scalar cases ===

void test_definitely_uninitialized(void)
{
  int x;
  int y = x; // FAIL: x is uninitialized
}

void test_initialized_before_use(void)
{
  int x;
  x = 42;
  int y = x; // PASS: x is initialized
}

void test_self_assignment(void)
{
  int x;
  x = x + 1; // FAIL: x is read before initialization
}

// === Phase 1: Control flow ===

void test_maybe_uninitialized(int cond)
{
  int x;
  if(cond)
    x = 1;
  int y = x; // FAIL: x may be uninitialized (cond == 0 path)
}

void test_both_branches_init(int cond)
{
  int x;
  if(cond)
    x = 1;
  else
    x = 2;
  int y = x; // PASS: x is initialized on all paths
}

void test_loop_init(int n)
{
  int x;
  for(int i = 0; i < n; i++)
    x = i;
  // x may be uninitialized if n <= 0
  int y = x; // FAIL: x may be uninitialized
}

// === Phase 1: Static lifetime and globals ===

static int static_var; // PASS: static lifetime, zero-initialized

void test_static_local(void)
{
  static int s;
  int y = s; // PASS: static local is zero-initialized
}

// === Phase 1: Address-taken (dirty) ===

void init_via_pointer(int *p)
{
  *p = 42;
}

void test_address_taken(void)
{
  int x;
  init_via_pointer(&x);
  int y = x; // PASS: address taken, conservatively assume initialized
  // (indeterminate but not UB per C11 6.3.2.1)
}

void test_address_taken_no_init(void)
{
  int x;
  int *p = &x;
  // x's address is taken but never written through p
  int y = x; // address taken → skip check (conservative)
}

// === Phase 2: Multiple reads ===

void test_multiple_reads(void)
{
  int x;
  int a = x; // FAIL: first read
  int b = x; // FAIL: second read should also be flagged
}

// === Phase 3: Struct members ===

struct point
{
  int x;
  int y;
};

void test_struct_fully_uninitialized(void)
{
  struct point p;
  int a = p.x; // FAIL: p.x uninitialized
}

void test_struct_partial_init(void)
{
  struct point p;
  p.x = 1;
  int a = p.x; // PASS: p.x initialized
  int b = p.y; // FAIL: p.y still uninitialized
}

void test_struct_whole_assign(void)
{
  struct point p;
  struct point q = {1, 2};
  p = q;
  int a = p.x; // PASS: whole struct assigned
  int b = p.y; // PASS: whole struct assigned
}

// === Phase 3: Unions ===

union variant
{
  int i;
  float f;
};

void test_union_uninitialized(void)
{
  union variant v;
  int a = v.i; // FAIL: v uninitialized
}

void test_union_write_one_read_other(void)
{
  union variant v;
  v.i = 42;
  float f = v.f; // PASS: union is initialized (type-punning is
                 // implementation-defined but not UB for reading)
}

// === Phase 3: Arrays ===

void test_array_uninitialized(void)
{
  int arr[10];
  int a = arr[0]; // FAIL: arr[0] uninitialized
}

void test_array_partial_init(int idx)
{
  int arr[10];
  arr[0] = 42;
  int a = arr[0]; // PASS: arr[0] initialized
  int b = arr[1]; // FAIL: arr[1] uninitialized
}

void test_array_loop_init(void)
{
  int arr[10];
  for(int i = 0; i < 10; i++)
    arr[i] = i;
  int a = arr[5]; // PASS: all elements initialized
}

// === Phase 3: Function calls ===

int return_value(void)
{
  return 42;
}

void test_init_from_return(void)
{
  int x;
  x = return_value();
  int y = x; // PASS: initialized from return value
}

void test_pass_by_pointer(void)
{
  int x;
  init_via_pointer(&x);
  int y = x; // PASS: initialized via pointer (address taken)
}

// === Edge cases ===

void test_const_local(void)
{
  const int x = 5;
  int y = x; // PASS: const with initializer
}

void test_volatile_local(void)
{
  volatile int x;
  int y = x; // implementation-defined, but reading volatile
             // uninitialized is still UB
}

void test_nested_scope(void)
{
  int x;
  {
    int x; // shadows outer x
    x = 1;
    int a = x; // PASS: inner x initialized
  }
  int b = x; // FAIL: outer x still uninitialized
}

// === Pointer aliasing ===

void test_pointer_alias_init(void)
{
  int x;
  int *p = &x;
  *p = 42;
  int y = x; // address taken → skip check (conservative)
}

void test_pointer_alias_no_init(void)
{
  int x;
  int *p = &x;
  // p exists but never written through
  int y = x; // address taken → skip check (conservative)
}

// === Function parameters ===

void test_parameter(int param)
{
  int y = param; // PASS: parameters are always initialized
}

// === Multiple variables ===

void test_multiple_vars(void)
{
  int x, y;
  x = 1;
  int z = x + y; // FAIL: y is uninitialized
}

// === Switch/goto ===

void test_switch_init(int sel)
{
  int x;
  switch(sel)
  {
  case 0:
    x = 10;
    break;
  case 1:
    x = 20;
    break;
  default:
    x = 30;
    break;
  }
  int y = x; // PASS: all switch cases initialize x
}

void test_switch_partial(int sel)
{
  int x;
  switch(sel)
  {
  case 0:
    x = 10;
    break;
  case 1:
    break; // x not initialized
  default:
    x = 30;
    break;
  }
  int y = x; // FAIL: case 1 doesn't initialize x
}

// === Concurrency ===

int shared_flag;

void test_concurrent_init(void)
{
  int x;
  // Another thread might initialize x, but without synchronization
  // reading x is still UB if this thread hasn't initialized it.
  // However, x's address is not taken here, so the check should fire.
  int y = x; // FAIL: x is uninitialized in this thread
}

// === Comma operator ===

void test_comma_operator(void)
{
  int x;
  int y = (x = 1, x); // PASS: x is initialized by comma expression
}

// === Ternary with init ===

void test_ternary_init(int cond)
{
  int x;
  int y = cond ? (x = 1) : (x = 2);
  int z = x; // PASS: x initialized on both branches
}

// === VLA size from uninitialized ===

void test_vla_uninit_size(void)
{
  int n;
  int arr[n]; // FAIL: n is uninitialized (UB: VLA size is indeterminate)
  (void)arr;
}

// === Nested structs ===

struct outer
{
  struct point inner;
  int z;
};

void test_nested_struct_uninit(void)
{
  struct outer o;
  int a = o.inner.x; // FAIL: o.inner.x uninitialized
}

void test_nested_struct_partial(void)
{
  struct outer o;
  o.inner.x = 1;
  int a = o.inner.x; // PASS: o.inner.x initialized
  int b = o.inner.y; // FAIL: o.inner.y uninitialized
  int c = o.z;       // FAIL: o.z uninitialized
}

void test_deep_nested_struct(void)
{
  struct A
  {
    int x;
  };
  struct B
  {
    struct A a;
    int y;
  };
  struct C
  {
    struct B b;
    int z;
  };
  struct C c;
  c.b.a.x = 1;
  int a = c.b.a.x; // PASS
  int b = c.b.y;   // FAIL
  int d = c.z;     // FAIL
}

struct has_arr
{
  int arr[3];
  int x;
};

void test_struct_array_member(void)
{
  struct has_arr s;
  s.arr[0] = 1;
  int a = s.arr[0]; // PASS
  int b = s.arr[1]; // FAIL
  int c = s.x;      // FAIL
}

void test_symbolic_index_read(void)
{
  int arr[4];
  arr[0] = 1;
  arr[1] = 2;
  int i = 2;
  int a = arr[i]; // FAIL: arr[2], arr[3] not initialized
}

void test_symbolic_index_all_init(void)
{
  int arr[4];
  arr[0] = 1;
  arr[1] = 2;
  arr[2] = 3;
  arr[3] = 4;
  int i = 2;
  int a = arr[i]; // PASS: all elements initialized
}

// === Heap allocation ===

void test_heap_uninit(void)
{
  int *p = malloc(sizeof(int));
  if(p)
  {
    int y = *p; // FAIL: heap memory is indeterminate
  }
}

void test_heap_init(void)
{
  int *p = malloc(sizeof(int));
  if(p)
  {
    *p = 42;
    int y = *p; // PASS: heap memory initialized
  }
}

void test_heap_alias_write(void)
{
  int *p = malloc(sizeof(int));
  if(p)
  {
    int *q = p;
    *q = 42;
    int y = *p; // PASS: *q = 42 initializes same memory
  }
}

// === Constant-size array per-element ===

void test_array_partial_element(void)
{
  int arr[3];
  arr[0] = 10;
  int a = arr[0]; // PASS: arr[0] initialized
  int b = arr[1]; // FAIL: arr[1] uninitialized
}

// === Function call with struct pointer ===

void init_point_x(struct point *p)
{
  p->x = 1;
}

void test_struct_init_via_call(void)
{
  struct point p;
  init_point_x(&p);
  int a = p.x; // address taken → skip (conservative)
}

// === Nondet-static interaction ===

static int static_nondet;

void test_static_nondet(void)
{
  // With --nondet-static, static_nondet is nondet (not zero-init).
  // Without it, static_nondet is zero-initialized.
  int y = static_nondet; // PASS: static lifetime
}

// === Concurrency: shared variable ===

int shared_var;

void writer_thread(void)
{
  shared_var = 42;
}

void test_concurrent_shared(void)
{
  // shared_var is global (static lifetime), always initialized
  int y = shared_var; // PASS: static lifetime
}

// === Goto across initialization ===

void test_goto_skip_init(int cond)
{
  int x;
  int y;
  if(cond)
    goto skip;
  x = 1;
skip:
  y = x; // FAIL: x may be uninitialized (goto skipped init)
}

// === Dirty variable tests (hybrid: shadow-mem for address-taken) ===

void helper_init(int *out)
{
  *out = 42;
}

void helper_noop(int *out)
{
  // does not write
}

void test_dirty_interprocedural_init(void)
{
  int x;
  helper_init(&x);
  int y = x; // PASS: x initialized by helper_init
}

void test_dirty_interprocedural_no_init(void)
{
  int x;
  helper_noop(&x);
  int y = x; // FAIL: helper_noop does not write to *out
}

void test_dirty_pointer_alias(void)
{
  int x;
  int *p = &x;
  *p = 42;
  int y = x; // PASS: *p = 42 initializes x
}

void test_dirty_cond_alias(void)
{
  int x;
  int dummy = 0;
  int cond = __VERIFIER_nondet_int();
  int *p = cond ? &x : &dummy;
  *p = 42;
  int y = x; // FAIL: x may not be initialized (p might point to dummy)
}

int main(void)
{
  // The individual test functions are called separately via
  // --function in the test descriptors.
  return 0;
}
