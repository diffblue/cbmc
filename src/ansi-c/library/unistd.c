/* FUNCTION: sleep */

unsigned int sleep(unsigned int seconds)
{
  // do nothing, but return nondet value
  unsigned remaining_time;
  
  if(remaining_time>seconds) remaining_time=seconds;
  
  return remaining_time;
}

/* FUNCTION: unlink */

int unlink(const char *s)
{
  __CPROVER_HIDE:;
  (void)*s;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "unlink zero-termination");
  #endif
  int retval;
  return retval;
}

/* FUNCTION: pipe */

#ifndef __CPROVER_ERRNO_H_INCLUDED
#include <errno.h>
#define __CPROVER_ERRNO_H_INCLUDED
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;
extern unsigned __CPROVER_pipe_count;

int pipe(int fildes[2])
{
  __CPROVER_HIDE:;
  char error;
  if(error)
  {
    errno=error==1 ? EMFILE : ENFILE;
    return -1;
  }

  __CPROVER_atomic_begin();
  __CPROVER_assume(__CPROVER_pipe_offset%2==0);
  __CPROVER_assume(__CPROVER_pipe_offset<=(int)(__CPROVER_pipe_offset+__CPROVER_pipe_count));
  fildes[0]=__CPROVER_pipe_offset+__CPROVER_pipe_count;
  fildes[1]=__CPROVER_pipe_offset+__CPROVER_pipe_count+1;
  __CPROVER_pipes[__CPROVER_pipe_count].widowed=0;
  __CPROVER_pipes[__CPROVER_pipe_count].next_avail=0;
  __CPROVER_pipes[__CPROVER_pipe_count].next_unread=0;
  __CPROVER_pipe_count+=2;
  __CPROVER_atomic_end();

  __CPROVER_assume(fildes[0]!=0 && fildes[0]!=1 && fildes[0]!=2);
  __CPROVER_assume(fildes[1]!=0 && fildes[1]!=1 && fildes[1]!=2);

  return 0;
}

/* FUNCTION: close */

#ifdef _WIN32
#include <io.h>
#else
#ifndef __CPROVER_UNISTD_H_INCLUDED
#include <unistd.h>
#define __CPROVER_UNISTD_H_INCLUDED
#endif
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

int close(int fildes)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
    return 0;

  int retval=-1;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed)
  {
    __CPROVER_pipes[fildes].widowed=1;
    __CPROVER_pipes[fildes].next_avail=__CPROVER_pipes[fildes].next_unread=0;
    retval=0;
  }
  __CPROVER_atomic_end();
  return retval;
}

/* FUNCTION: write */

#ifdef _WIN32
#include <io.h>
#else
#ifndef __CPROVER_UNISTD_H_INCLUDED
#include <unistd.h>
#define __CPROVER_UNISTD_H_INCLUDED
#endif
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

#ifdef _MSC_VER
#define ssize_t signed long
#endif

ssize_t write(int fildes, const void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ssize_t retval;
    __CPROVER_assume(retval>=-1 && retval<=(ssize_t)nbyte);
    return retval;
  }

  int retval=-1;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed &&
      sizeof(__CPROVER_pipes[fildes].data) >=
      __CPROVER_pipes[fildes].next_avail+nbyte)
  {
    for(size_t i=0; i<nbyte; ++i)
      __CPROVER_pipes[fildes].data[i+__CPROVER_pipes[fildes].next_avail]=
        ((char*)buf)[i];
    __CPROVER_pipes[fildes].next_avail+=nbyte;
    retval=nbyte;
  }
  __CPROVER_atomic_end();
  return retval;
}

/* FUNCTION: read */

#ifdef _WIN32
#include <io.h>
#else
#ifndef __CPROVER_UNISTD_H_INCLUDED
#include <unistd.h>
#define __CPROVER_UNISTD_H_INCLUDED
#endif
#endif

extern struct __CPROVER_pipet __CPROVER_pipes[];
// offset to make sure we don't collide with other fds
extern const int __CPROVER_pipe_offset;

#ifdef _MSC_VER
#define ssize_t signed long
#endif

ssize_t read(int fildes, void *buf, size_t nbyte)
{
  __CPROVER_HIDE:;
  if((fildes>=0 && fildes<=2) || fildes < __CPROVER_pipe_offset)
  {
    ssize_t nread;
    size_t i;
    __CPROVER_assume((size_t)nread<=nbyte);

    for(i=0; i<nbyte; i++)
    {
      char nondet_char;
      ((char *)buf)[i]=nondet_char;
    }

    __CPROVER_bool error;
    return error ? -1 : nread;
  }

  int retval=0;
  fildes-=__CPROVER_pipe_offset;
  if(fildes%2==1)
    --fildes;
  __CPROVER_atomic_begin();
  if(!__CPROVER_pipes[fildes].widowed)
  {
    for(size_t i=0; i<nbyte &&
      __CPROVER_pipes[fildes].next_unread <
      __CPROVER_pipes[fildes].next_avail;
      ++i)
    {
      ((char*)buf)[i]=__CPROVER_pipes[fildes].
        data[__CPROVER_pipes[fildes].next_unread];
      ++__CPROVER_pipes[fildes].next_unread;
      ++retval;
    }
    if(__CPROVER_pipes[fildes].next_avail==
        __CPROVER_pipes[fildes].next_unread)
      __CPROVER_pipes[fildes].next_avail=__CPROVER_pipes[fildes].next_unread=0;
  }
  __CPROVER_atomic_end();
  return retval;
}

