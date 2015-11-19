
/* FUNCTION: putchar */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int putchar(int c)
{
  __CPROVER_bool error;
  __CPROVER_HIDE: printf("%c", c);
  return (error?-1:c);
}

/* FUNCTION: puts */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int puts(const char *s)
{
  __CPROVER_HIDE:;
  __CPROVER_bool error;
  int ret;
  printf("%s\n", s);
  if(error) ret=-1; else __CPROVER_assume(ret>=0);
  return ret;
}

/* FUNCTION: fopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

#ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
inline void fclose_cleanup(void *stream)
{
  __CPROVER_HIDE:;
  __CPROVER_assert(__CPROVER_get_must(stream, "closed"),
                   "resource leak: fopen file not closed");
}
#endif

inline FILE *fopen(const char *filename, const char *mode)
{
  __CPROVER_HIDE:;
  (void)*filename;
  (void)*mode;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(filename), "fopen zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(mode), "fopen zero-termination of 2nd argument");
  #endif

  FILE *f;

  _Bool fopen_error;
  f=fopen_error?NULL:malloc(sizeof(FILE));

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_set_must(f, "open");
  __CPROVER_cleanup(f, fclose_cleanup);
  #endif

  return f;
}

/* FUNCTION: fclose */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fclose(FILE *stream)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fclose file must be open");
  __CPROVER_clear_must(stream, "open");
  __CPROVER_set_must(stream, "closed");
  #endif
  int return_value;
  free(stream);
  return return_value;
}

/* FUNCTION: fdopen */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

inline FILE *fdopen(int handle, const char *mode)
{
  __CPROVER_HIDE:;
  (void)handle;
  (void)*mode;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(mode),
    "fdopen zero-termination of 2nd argument");
  #endif

  FILE *f=malloc(sizeof(FILE));

  return f;
}

/* FUNCTION: fgets */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline char *fgets(char *str, int size, FILE *stream)
{
  __CPROVER_HIDE:;
  __CPROVER_bool error;

  (void)size;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fgets file must be open");
  #endif

  #ifdef __CPROVER_STRING_ABSTRACTION
  int resulting_size;
  __CPROVER_assert(__CPROVER_buffer_size(str)>=size, "buffer-overflow in fgets");
  if(size>0)
  {
    __CPROVER_assume(resulting_size<size);
    __CPROVER_is_zero_string(str)=!error;
    __CPROVER_zero_string_length(str)=resulting_size;
  }
  #endif

  return error?0:str;
}

/* FUNCTION: fread */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline size_t fread(
  void *ptr,
  size_t size,
  size_t nitems,
  FILE *stream)
{
  __CPROVER_HIDE:;
  size_t nread;
  size_t bytes=nread*size;
  size_t i;
  __CPROVER_assume(nread<=nitems);

  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fread file must be open");
  #endif

  for(i=0; i<bytes; i++)
  {
    char nondet_char;
    ((char *)ptr)[i]=nondet_char;
  }

  return nread;
}

/* FUNCTION: feof */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int feof(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "feof file must be open");
  #endif

  return return_value;
}

/* FUNCTION: ferror */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int ferror(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS    
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "feof file must be open");
  #endif
  
  return return_value;
}

/* FUNCTION: fileno */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fileno(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fileno file must be open");
  #endif

  return return_value;
}

/* FUNCTION: fputs */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fputs(const char *s, FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "fputs zero-termination of 1st argument");
  #endif
  (void)*s;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fputs file must be open");
  #endif

  return return_value;
}

/* FUNCTION: fflush */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fflush(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fflush file must be open");
  #endif

  return return_value;
}

/* FUNCTION: fpurge */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fpurge(FILE *stream)
{
  // just return nondet
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fpurge file must be open");
  #endif

  return return_value;
}

/* FUNCTION: fgetc */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fgetc(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
  // it's a byte or EOF (-1)
  __CPROVER_assume(return_value>=-1 && return_value<=255);

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fgetc file must be open");
  #endif

  return return_value;
}

/* FUNCTION: getc */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int getc(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "getc file must be open");
  #endif

  // It's a byte or EOF, which we fix to -1.
  __CPROVER_assume(return_value>=-1 && return_value<=255);
  return return_value;
}

/* FUNCTION: getchar */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int getchar()
{
  __CPROVER_HIDE:;
  int return_value;
  // it's a byte or EOF
  __CPROVER_assume(return_value>=-1 && return_value<=255);
  return return_value;
}

/* FUNCTION: getw */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int getw(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "getw file must be open");
  #endif

  // it's any int, no restriction
  return return_value;
}

/* FUNCTION: fseek */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline int fseek(FILE *stream, long offset, int whence)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;
  (void)offset;
  (void)whence;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fseek file must be open");
  #endif

  return return_value;
}

/* FUNCTION: ftell */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

inline long ftell(FILE *stream)
{
  __CPROVER_HIDE:;
  int return_value;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "ftell file must be open");
  #endif

  return return_value;
}

/* FUNCTION: rewind */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

void rewind(FILE *stream)
{
  __CPROVER_HIDE:
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "rewind file must be open");
  #endif
}

/* FUNCTION: fwrite */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

size_t fwrite(
  const void *ptr,
  size_t size,
  size_t nitems,
  FILE *stream)
{
  __CPROVER_HIDE:;
  (void)*(char*)ptr;
  (void)size;
  (void)*stream;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "fwrite file must be open");
  #endif

  size_t nwrite;
  __CPROVER_assume(nwrite<=nitems);
  return nwrite;
}

/* FUNCTION: perror */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

void perror(const char *s)
{
  __CPROVER_HIDE:;
  if(s!=0)
  {
    #ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_assert(__CPROVER_is_zero_string(s), "perror zero-termination");
    #endif
    // should go to stderr
    if(s[0]!=0)
      printf("%s: ", s);
  }
  
  // TODO: print errno error
}

/* FUNCTION: fscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int fscanf(FILE *restrict stream, const char *restrict format, ...)
{
  __CPOVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfscanf(stream, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: scanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int scanf(const char *restrict format, ...)
{
  __CPOVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfscanf(stdin, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: sscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int sscanf(const char *restrict s, const char *restrict format, ...)
{
  __CPOVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vsscanf(s, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: vfscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int vfscanf(FILE *restrict stream, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result;
  (void)*stream;
  (void)*format;
  (void)arg;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "vfscanf file must be open");
  #endif

  return result;
}

/* FUNCTION: vscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int vscanf(const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  return vfscanf(stdin, format, arg);
}

/* FUNCTION: vsscanf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int vsscanf(const char *restrict s, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result;
  (void)*s;
  (void)*format;
  (void)arg;
  return result;
}

/* FUNCTION: fprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int fprintf(FILE *stream, const char *restrict format, ...)
{
  __CPROVER_HIDE:;
  va_list list;
  va_start(list, format);
  int result=vfprintf(stream, format, list);
  va_end(list);
  return result;
}

/* FUNCTION: vfprintf */

#ifndef __CPROVER_STDIO_H_INCLUDED
#include <stdio.h>
#define __CPROVER_STDIO_H_INCLUDED
#endif

#ifndef __CPROVER_STDARG_H_INCLUDED
#include <stdarg.h>
#define __CPROVER_STDARG_H_INCLUDED
#endif

inline int vfprintf(FILE *stream, const char *restrict format, va_list arg)
{
  __CPROVER_HIDE:;
  int result;
  (void)*stream;
  (void)*format;
  (void)arg;

  #ifdef __CPROVER_CUSTOM_BITVECTOR_ANALYSIS
  __CPROVER_assert(__CPROVER_get_must(stream, "open"),
                   "vfprintf file must be open");
  #endif

  return result;
}

