#include <stdlib.h>

typedef struct
{
  size_t k;
  void **ptrs;
} shadow_map_t;

extern size_t __CPROVER_max_malloc_size;
int __builtin_clzll(unsigned long long);

// computes 2^OBJECT_BITS
#define __nof_objects                                                          \
  ((size_t)(1ULL << __builtin_clzll(__CPROVER_max_malloc_size)))

// Initialises the given shadow memory map
void shadow_map_init(shadow_map_t *smap, size_t k)
{
  *smap = (shadow_map_t){
    .k = k, .ptrs = __CPROVER_allocate(__nof_objects * sizeof(void *), 1)};
}

// Returns a pointer to the shadow bytes of the byte pointed to by ptr
void *shadow_map_get(shadow_map_t *smap, void *ptr)
{
  size_t id = __CPROVER_POINTER_OBJECT(ptr);
  void *sptr = smap->ptrs[id];
  if(!sptr)
  {
    sptr = __CPROVER_allocate(smap->k * __CPROVER_OBJECT_SIZE(ptr), 1);
    smap->ptrs[id] = sptr;
  }
  return sptr + smap->k * __CPROVER_POINTER_OFFSET(ptr);
}

shadow_map_t smap;

// read before write instrumentation
void shadow_read(void *ptr)
{
  char *sptr = (char *)shadow_map_get(&smap, ptr);
  __CPROVER_assert(*sptr, "read before write");
}

void shadow_write(void *ptr)
{
  char *sptr = (char *)shadow_map_get(&smap, ptr);
  *sptr = *sptr | 1;
}

size_t nondet_size_t();

int main()
{
  shadow_map_init(&smap, 1);
  size_t size;
  size = SIZE;
  shadow_write(&size);
  shadow_read(&size);
  char **arr = malloc(size * sizeof(char *));
  shadow_write(&arr);
  char a;
  a = 0;
  shadow_write(&a);
  char b;
  if(nondet_size_t() || 1)
  {
    b = 1;
    shadow_write(&b);
  }
  char c;
  c = 2;
  shadow_write(&c);
  size_t i;
  i = 0;
  shadow_write(&i);

LOOP_HEAD:
  shadow_read(&i);
  shadow_read(&size);
  if(i >= ITERS)
    goto LOOP_EXIT;
  arr[i] = malloc(3);
  shadow_write(&arr[i]);
  shadow_read(&a);
  arr[i][0] = a;
  shadow_write(&(arr[i][0]));
  shadow_read(&b);
  arr[i][1] = b;
  shadow_write(&(arr[i][1]));
  shadow_read(&c);
  arr[i][2] = c;
  shadow_write(&(arr[i][2]));
  shadow_read(&i);
  i = i + 1;
  shadow_write(&i);
  goto LOOP_HEAD;
LOOP_EXIT:;
}
