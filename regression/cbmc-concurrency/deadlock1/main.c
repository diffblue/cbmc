#include <pthread.h>
#include <stdlib.h>
#include <assert.h>

pthread_mutex_t lock_never_unlock_002_glb_mutex = PTHREAD_MUTEX_INITIALIZER;

void* lock_never_unlock_002_tsk_001(void* pram) { 
  pthread_mutex_lock(&lock_never_unlock_002_glb_mutex);  
  return NULL; 
} 

void main() { 
  pthread_t tid1; 
  pthread_t tid2; 
  pthread_mutex_init(&lock_never_unlock_002_glb_mutex, NULL); 
  pthread_create(&tid1, NULL, lock_never_unlock_002_tsk_001, NULL); 
  pthread_create(&tid2, NULL, lock_never_unlock_002_tsk_001, NULL); 
  pthread_join(tid1, NULL); 
  pthread_join(tid2, NULL); 
  // deadlock in the threads; assertion should not be reachable
  assert(0);
} 
