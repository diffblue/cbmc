#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdbool.h>
#include <stdlib.h>

sem_t create_semaphore(int initial_value)
{
  const int shared_between_processes = false;
  sem_t semaphore;
  const int init_error =
    sem_init(&semaphore, shared_between_processes, initial_value);
  assert(init_error == false);
  return semaphore;
}

void destroy_semaphore(sem_t *const semaphore)
{
  int destroy_error = sem_destroy(semaphore);
  assert(destroy_error == false);
}

sem_t global_semaphore;

int main(void)
{
  global_semaphore = create_semaphore(0);
  destroy_semaphore(&global_semaphore);
  return EXIT_SUCCESS;
}
