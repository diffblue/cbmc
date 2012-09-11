typedef __typeof__(sizeof(int)) __CPROVER_size_t;
void *__CPROVER_malloc(__CPROVER_size_t size);
extern const void *__CPROVER_deallocated;
extern const void *__CPROVER_malloc_object;
extern __CPROVER_size_t __CPROVER_malloc_size;
extern _Bool __CPROVER_malloc_is_new_array;
