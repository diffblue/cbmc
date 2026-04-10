// Comparison test for uninitialized check approaches:
// - "shadow-bool": current goto_check_c shadow boolean approach
// - "shadow-mem": new shadow memory (symex-level) approach
//
// For each test, we note the expected precise result and what each
// approach actually produces.

#include <assert.h>
#include <stdlib.h>

// === 1. Basic scalar ===
// Expected: FAIL (x never assigned)
// shadow-bool: FAIL  shadow-mem: FAIL
void test_basic_uninit(void)
{
  int x;
  int y = x;
}

// === 2. Basic initialized ===
// Expected: PASS
// shadow-bool: PASS  shadow-mem: PASS
void test_basic_init(void)
{
  int x;
  x = 42;
  int y = x;
}

// === 3. Conditional init (both branches) ===
// Expected: PASS
// shadow-bool: PASS  shadow-mem: PASS
void test_cond_both(void)
{
  int x;
  int cond = __VERIFIER_nondet_int();
  if(cond)
    x = 1;
  else
    x = 2;
  int y = x;
}

// === 4. Conditional init (one branch only) ===
// Expected: FAIL
// shadow-bool: FAIL  shadow-mem: FAIL
void test_cond_partial(void)
{
  int x;
  int cond = __VERIFIER_nondet_int();
  if(cond)
    x = 1;
  int y = x;
}

// === 5. Init via address-taken (dirty variable) ===
// Expected: PASS (x is initialized through pointer)
// shadow-bool: SKIPPED (dirty vars excluded)  shadow-mem: PASS
void test_dirty_init(void)
{
  int x;
  int *p = &x;
  *p = 42;
  int y = x;
}

// === 6. Init via function call with output pointer ===
// Expected: PASS
// shadow-bool: SKIPPED (dirty)  shadow-mem: PASS
void do_init(int *out)
{
  *out = 42;
}

void test_interprocedural_init(void)
{
  int x;
  do_init(&x);
  int y = x;
}

// === 7. NOT init via function call (callee doesn't write) ===
// Expected: FAIL
// shadow-bool: SKIPPED (dirty)  shadow-mem: FAIL
void do_nothing(int *out)
{
  // does not write to *out
}

void test_interprocedural_no_init(void)
{
  int x;
  do_nothing(&x);
  int y = x;
}

// === 8. Heap alias: write through copy ===
// Expected: PASS
// shadow-bool: PASS (shared flag)  shadow-mem: PASS
void test_heap_alias(void)
{
  int *p = malloc(sizeof(int));
  if(!p)
    return;
  int *q = p;
  *q = 42;
  int y = *p;
}

// === 9. Heap alias: write through original, read through copy ===
// Expected: PASS
// shadow-bool: PASS (shared flag)  shadow-mem: PASS
void test_heap_alias_reverse(void)
{
  int *p = malloc(sizeof(int));
  if(!p)
    return;
  int *q = p;
  *p = 42;
  int y = *q;
}

// === 10. Conditional pointer alias ===
// Expected: FAIL (on path where p != &x, x is uninit)
// shadow-bool: SKIPPED (dirty)  shadow-mem: FAIL
void test_cond_alias(void)
{
  int x;
  int dummy = 0;
  int cond = __VERIFIER_nondet_int();
  int *p = cond ? &x : &dummy;
  *p = 42;
  int y = x;
}

// === 11. Array element via symbolic index ===
// Expected: FAIL (not all elements initialized)
// shadow-bool: FAIL (conjunction)  shadow-mem: FAIL
void test_array_symbolic_partial(void)
{
  int arr[4];
  arr[0] = 1;
  arr[1] = 2;
  int i = __VERIFIER_nondet_int();
  __CPROVER_assume(i >= 0 && i < 4);
  int y = arr[i];
}

// === 12. Array fully initialized via loop ===
// Expected: PASS
// shadow-bool: PASS (symbolic write sets all)  shadow-mem: PASS
void test_array_loop_full(void)
{
  int arr[4];
  for(int i = 0; i < 4; i++)
    arr[i] = i;
  int j = __VERIFIER_nondet_int();
  __CPROVER_assume(j >= 0 && j < 4);
  int y = arr[j];
}

// === 13. Struct member partial init ===
// Expected: FAIL (s.y not initialized)
// shadow-bool: FAIL  shadow-mem: FAIL
struct S
{
  int x;
  int y;
};

void test_struct_partial(void)
{
  struct S s;
  s.x = 1;
  int a = s.x;
  int b = s.y;
}

// === 14. Nested struct ===
// Expected: FAIL (o.inner.y not initialized)
// shadow-bool: FAIL  shadow-mem: FAIL
struct inner
{
  int x;
  int y;
};
struct outer
{
  struct inner i;
  int z;
};

void test_nested_struct(void)
{
  struct outer o;
  o.i.x = 1;
  int a = o.i.x;
  int b = o.i.y;
}

// === 15. Union write one member, read another ===
// Expected: PASS (union semantics: writing any member initializes storage)
// shadow-bool: PASS (single flag)  shadow-mem: PASS
union U
{
  int i;
  float f;
};

void test_union_cross_member(void)
{
  union U u;
  u.i = 42;
  float f = u.f;
}

// === 16. Return value from function ===
// Expected: PASS
// shadow-bool: PASS  shadow-mem: PASS
int get_value(void)
{
  return 42;
}

void test_return_value(void)
{
  int x;
  x = get_value();
  int y = x;
}

// === 17. Self-referential: read before write in same expression ===
// Expected: FAIL (x is read before it's assigned)
// shadow-bool: FAIL  shadow-mem: FAIL
void test_self_assign(void)
{
  int x;
  x = x + 1;
}

int main()
{
  return 0;
}
