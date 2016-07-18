#ifndef PRQA_PTHREAD_H
#define PRQA_PTHREAD_H

typedef struct __pthread_t {char __dummy;} *pthread_t;
typedef struct __pthread_mutex_t {char __dummy;} *pthread_mutex_t;
typedef struct __pthread_attr_t {char __dummy;} *pthread_attr_t;

int pthread_create (pthread_t *, const pthread_attr_t *, void * (*) (void *), void *);
int pthread_join (pthread_t thread, void ** retval);

int pthread_mutex_lock (pthread_mutex_t * mutex);
int pthread_mutex_trylock (pthread_mutex_t * mutex);
int pthread_mutex_unlock (pthread_mutex_t * mutex);

#ifndef NULL
#define NULL 0
#endif

#endif
