#include <assert.h>
#include <pthread.h>
#include <semaphore.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

pthread_t start_worker_thread(void *(*start_routine)(void *))
{
  pthread_t worker_thread;
  const pthread_attr_t *const attributes = NULL;
  void *const worker_argument = NULL;
  const int create_status =
    pthread_create(&worker_thread, attributes, start_routine, worker_argument);
  assert(create_status == 0);
  return worker_thread;
}

void join_thread(const pthread_t thread)
{
  const int join_status = pthread_join(thread, NULL);
  assert(join_status == 0);
}

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

// This blocking queue structure supports waiting for free space before
// enqueuing and waiting for data before dequeuing, using a pair of semaphores.
// These functions do not employ a mutex, so a data race may occur if multiple
// threads attempt to enqueue at the same time or multiple threads attempt to
// dequeue at the same time. The expected valid use case is with two threads,
// where one of the two enqueues and the other thread dequeues.
struct blocking_queuet
{
  size_t size;
  int *elements;
  size_t begin;
  size_t end;
  sem_t free_space;
  sem_t data_waiting;
};

struct blocking_queuet initialise_blocking_queue(const size_t size)
{
  printf("init queue begin\n");
  struct blocking_queuet queue;
  queue.size = size;
  queue.elements = calloc(size, sizeof(int));
  queue.begin = 0;
  queue.end = 0;
  queue.free_space = create_semaphore(size);
  queue.data_waiting = create_semaphore(0);
  printf("init queue end\n");
  return queue;
}

void free_blocking_queue(struct blocking_queuet *queue)
{
  free(queue->elements);
  queue->elements = NULL;
  destroy_semaphore(&queue->free_space);
  destroy_semaphore(&queue->data_waiting);
}

void enqueue(struct blocking_queuet *queue, const int data)
{
  printf(
    "enqueue begin:%lu end:%lu data:%d \n", queue->begin, queue->end, data);
  const int free_wait_error = sem_wait(&queue->free_space);
  assert(free_wait_error == false);
  queue->elements[queue->end] = data;
  if(++queue->end == queue->size)
  {
    queue->end = 0;
  }
  const int post_error = sem_post(&queue->data_waiting);
  assert(post_error == false);
  printf("enqueue done\n");
}

int dequeue(struct blocking_queuet *queue)
{
  printf("dequeue begin:%lu end:%lu\n", queue->begin, queue->end);
  const int data_wait_error = sem_wait(&queue->data_waiting);
  assert(data_wait_error == false);
  int result = queue->elements[queue->begin];
  if(++queue->begin == queue->size)
  {
    queue->begin = 0;
  }
  const int free_error = sem_post(&queue->free_space);
  assert(free_error == false);
  printf("dequeue done. data:%d \n", result);
  return result;
}

struct blocking_queuet input_queue;
struct blocking_queuet output_queue;

void *worker(void *arguments)
{
  int data;
  while(data = dequeue(&input_queue))
  {
    enqueue(&output_queue, data * data);
  }
  pthread_exit(NULL);
}

int main(void)
{
  input_queue = initialise_blocking_queue(3);
  output_queue = initialise_blocking_queue(10);
  const pthread_t worker_thread1 = start_worker_thread(&worker);
  printf("worker_started\n");
  enqueue(&input_queue, 1);
  enqueue(&input_queue, 2);
  enqueue(&input_queue, 3);
  enqueue(&input_queue, 4);
  enqueue(&input_queue, 5);
  enqueue(&input_queue, 6);
  enqueue(&input_queue, 7);
  enqueue(&input_queue, 8);
  enqueue(&input_queue, 9);
  enqueue(&input_queue, 0);
  join_thread(worker_thread1);
  free_blocking_queue(&input_queue);
  assert(dequeue(&output_queue) == 1);
  assert(dequeue(&output_queue) == 4);
  assert(dequeue(&output_queue) == 9);
  assert(dequeue(&output_queue) == 16);
  assert(dequeue(&output_queue) == 25);
  assert(dequeue(&output_queue) == 36);
  assert(dequeue(&output_queue) == 49);
  assert(dequeue(&output_queue) == 64);
  assert(dequeue(&output_queue) == 81);
  free_blocking_queue(&output_queue);
  return EXIT_SUCCESS;
}
