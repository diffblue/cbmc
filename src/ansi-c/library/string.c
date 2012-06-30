/* FUNCTION: __builtin___strcpy_chk */

inline char *__builtin___strcpy_chk(char *dst, const char *src, __CPROVER_size_t s)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strcpy zero-termination of 2nd argument");
  __CPROVER_assert(__CPROVER_buffer_size(dst)>__CPROVER_zero_string_length(src), "strcpy buffer overflow");
  dst[__CPROVER_zero_string_length(src)]=0;
  __CPROVER_is_zero_string(dst)=1;
  __CPROVER_zero_string_length(dst)=__CPROVER_zero_string_length(src);
  #else
  __CPROVER_size_t i=0;
  char ch;
  do
  {
    ch=src[i];
    dst[i]=ch;
    i++;
  }
  while(ch!=(char)0);
  #endif
  return dst;
}

/* FUNCTION: __builtin___strcat_chk */

__inline char *__builtin___strcat_chk(char *dst, const char *src, __CPROVER_size_t s)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_size_t new_size;
  __CPROVER_assert(__CPROVER_is_zero_string(dst), "strcat zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strcat zero-termination of 2nd argument");
  new_size=__CPROVER_zero_string_length(dst)+__CPROVER_zero_string_length(src);
  __CPROVER_assert(__CPROVER_buffer_size(dst)>new_size,
                   "strcat buffer overflow");
  __CPROVER_size_t old_size=__CPROVER_zero_string_length(dst);
  //"  for(size_t i=0; i<__CPROVER_zero_string_length(src); i++)
  //"    dst[old_size+i];
  dst[new_size]=0;
  __CPROVER_is_zero_string(dst)=1;
  __CPROVER_zero_string_length(dst)=new_size;
  #else
  __CPROVER_size_t i=0;
  while(dst[i]!=0) i++;

  __CPROVER_size_t j=0;
  char ch;
  do
  {
    char ch=src[j];
    dst[i]=ch;
    i++;
    j++;
  }
  while(ch!=(char)0);
  #endif
  return dst;
}                        

/* FUNCTION: __builtin___strncat_chk */

__inline char *__builtin___strncat_chk(
  char *dest, const char *src, __CPROVER_size_t len, __CPROVER_size_t s)
{
}                        

/* FUNCTION: strcpy */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strcpy

inline char *strcpy(char *dst, const char *src)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strcpy zero-termination of 2nd argument");
  __CPROVER_assert(__CPROVER_buffer_size(dst)>__CPROVER_zero_string_length(src), "strcpy buffer overflow");
  dst[__CPROVER_zero_string_length(src)]=0;
  __CPROVER_is_zero_string(dst)=1;
  __CPROVER_zero_string_length(dst)=__CPROVER_zero_string_length(src);
  #else
  __CPROVER_size_t i=0;
  char ch;
  do
  {
    ch=src[i];
    dst[i]=ch;
    i++;
  }
  while(ch!=(char)0);
  #endif
  return dst;
}

/* FUNCTION: strncpy */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strncpy

inline char *strncpy(char *dst, const char *src, size_t n)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strncpy zero-termination of 2nd argument");
  __CPROVER_assert(__CPROVER_buffer_size(dst)>=n, "strncpy buffer overflow");
  __CPROVER_is_zero_string(dst)=__CPROVER_zero_string_length(src)<n;
  __CPROVER_zero_string_length(dst)=__CPROVER_zero_string_length(src);  
  #else
  __CPROVER_size_t i=0;
  char ch;

  for( ; i<n && (ch=src[i])!=(char)0; i++)
    dst[i]=ch;

  for( ; i<n ; i++)
    dst[i]=0;
  #endif
  return dst;
}

/* FUNCTION: strcat */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strcat

inline char *strcat(char *dst, const char *src)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_size_t new_size;
  __CPROVER_assert(__CPROVER_is_zero_string(dst), "strcat zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strcat zero-termination of 2nd argument");
  new_size=__CPROVER_zero_string_length(dst)+__CPROVER_zero_string_length(src);
  __CPROVER_assert(__CPROVER_buffer_size(dst)>new_size,
                   "strcat buffer overflow");
  __CPROVER_size_t old_size=__CPROVER_zero_string_length(dst);
  //"  for(size_t i=0; i<__CPROVER_zero_string_length(src); i++)
  //"    dst[old_size+i];
  dst[new_size]=0;
  __CPROVER_is_zero_string(dst)=1;
  __CPROVER_zero_string_length(dst)=new_size;
  #else
  __CPROVER_size_t i=0;
  while(dst[i]!=0) i++;

  __CPROVER_size_t j=0;
  char ch;
  do
  {
    char ch=src[j];
    dst[i]=ch;
    i++;
    j++;
  }
  while(ch!=(char)0);
  #endif
  return dst;
}

/* FUNCTION: strncat */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strncat

inline char *strncat(char *dst, const char *src, size_t n)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_size_t additional, new_size;
  __CPROVER_assert(__CPROVER_is_zero_string(dst), "strncat zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(src) || __CPROVER_buffer_size(src)>=n, "strncat zero-termination of 2nd argument");
  additional=(n<__CPROVER_zero_string_length(src))?n:__CPROVER_zero_string_length(src);
  new_size=__CPROVER_is_zero_string(dst)+additional; 
  __CPROVER_assert(__CPROVER_buffer_size(dst)>new_size,
                   "strncat buffer overflow");
  __CPROVER_size_t dest_len=__CPROVER_zero_string_length(dst); 
  __CPROVER_size_t i;
  for (i = 0 ; i < n && i<__CPROVER_zero_string_length(src) ; i++)
    dst[dest_len + i] = src[i];
  dst[dest_len + i] = 0;
  __CPROVER_is_zero_string(dst)=1;
  __CPROVER_zero_string_length(dst)=new_size;
  #else
  #endif
  return dst;
}

/* FUNCTION: strcmp */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strcmp

inline int strcmp(const char *s1, const char *s2)
{
  __CPROVER_HIDE:;
  int retval;
  if(s1!=0 && s1==s2) return 0;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s1), "strcmp zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(s2), "strcmp zero-termination of 2nd argument");
  if(__CPROVER_zero_string_length(s1) != __CPROVER_zero_string_length(s2)) __CPROVER_assume(retval!=0);
  return retval;
  #else
  __CPROVER_size_t i=0;
  unsigned char ch1, ch2;
  do
  {
    ch1=s1[i];
    ch2=s2[i];

    if(ch1==ch2)
    {
    }
    else if(ch1<ch2)
      return -1;
    else
      return 1;

    i++;
  }
  while(ch1!=0 && ch2!=0);
  return 0;
  #endif
}

/* FUNCTION: strcasecmp */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strcasecmp

inline int strcasecmp(const char *s1, const char *s2)
{
  __CPROVER_HIDE:;
  int retval;
  if(s1!=0 && s1==s2) return 0;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s1), "strcasecmp zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(s2), "strcasecmp zero-termination of 2nd argument");
  if(__CPROVER_zero_string_length(s1) != __CPROVER_zero_string_length(s2)) __CPROVER_assume(retval!=0);
  return retval;
  #else
  __CPROVER_size_t i=0;
  unsigned char ch1, ch2;
  do
  {
    ch1=s1[i];
    ch2=s2[i];
    
    if(ch1>='A' && ch1<='Z') ch1+=('a'-'A');
    if(ch2>='A' && ch2<='Z') ch2+=('a'-'A');

    if(ch1==ch2)
    {
    }
    else if(ch1<ch2)
      return -1;
    else
      return 1;

    i++;
  }
  while(ch1!=0 && ch2!=0);
  return 0;
  #endif
}

/* FUNCTION: strncmp */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strncmp

inline int strncmp(const char *s1, const char *s2, size_t n)
{
  __CPROVER_HIDE:;
  if(s1!=0 && s1==s2) return 0;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s1) || __CPROVER_buffer_size(s1)>=n, "strncmp zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(s2) || __CPROVER_buffer_size(s2)>=n, "strncmp zero-termination of 2nd argument");
  #else
  __CPROVER_size_t i=0;
  unsigned char ch1, ch2;
  do
  {
    ch1=s1[i];
    ch2=s2[i];

    if(ch1==ch2)
    {
    }
    else if(ch1<ch2)
      return -1;
    else
      return 1;

    i++;
  }
  while(ch1!=0 && ch2!=0 && i<n);
  return 0;
  #endif
}

/* FUNCTION: strncasecmp */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strncasecmp

inline int strncasecmp(const char *s1, const char *s2, size_t n)
{
  __CPROVER_HIDE:;
  int retval;
  if(s1!=0 && s1==s2) return 0;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s1), "strncasecmp zero-termination of 1st argument");
  __CPROVER_assert(__CPROVER_is_zero_string(s2), "strncasecmp zero-termination of 2nd argument");
  return retval;
  #else
  __CPROVER_size_t i=0;
  unsigned char ch1, ch2;
  do
  {
    ch1=s1[i];
    ch2=s2[i];
    
    if(ch1>='A' && ch1<='Z') ch1+=('a'-'A');
    if(ch2>='A' && ch2<='Z') ch2+=('a'-'A');

    if(ch1==ch2)
    {
    }
    else if(ch1<ch2)
      return -1;
    else
      return 1;

    i++;
  }
  while(ch1!=0 && ch2!=0 && i<n);
  return 0;
  #endif
}

/* FUNCTION: strlen */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strlen

inline size_t strlen(const char *s)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(s), "strlen zero-termination");
  return __CPROVER_zero_string_length(s);
  #else
  __CPROVER_size_t len=0;
  while(s[len]!=0) len++;
  return len;
  #endif
}

/* FUNCTION: strdup */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#include <stdlib.h>
#define __CPROVER_STDLIB_H_INCLUDED
#endif

#undef strdup
#undef strcpy

inline char *strdup(const char *str)
{
  __CPROVER_HIDE:;
  __CPROVER_size_t bufsz;
  bufsz=(strlen(str)+1);
  char *cpy=(char *)malloc(bufsz*sizeof(char));
  if(cpy==((void *)0)) return 0;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assume(__CPROVER_buffer_size(cpy)==bufsz);
  #endif
  strcpy(cpy, str);
  return cpy;
}

/* FUNCTION: memcpy */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef memcpy

inline void *memcpy(void *dst, const void *src, size_t n)
{
  __CPROVER_HIDE:
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_buffer_size(src)>=n, "memcpy buffer overflow");
  __CPROVER_assert(__CPROVER_buffer_size(dst)>=n, "memcpy buffer overflow");
  //  for(size_t i=0; i<n ; i++) dst[i]=src[i];
  if(__CPROVER_is_zero_string(src) &&
     n > __CPROVER_zero_string_length(src))
  {
    __CPROVER_is_zero_string(dst)=1;
    __CPROVER_zero_string_length(dst)=__CPROVER_zero_string_length(src);
  }
  else if(!(__CPROVER_is_zero_string(dst) &&
            n <= __CPROVER_zero_string_length(dst)))
    __CPROVER_is_zero_string(dst)=0;
  #else
  for(__CPROVER_size_t i=0; i<n ; i++) ((char *)dst)[i]=((const char *)src)[i];
  #endif
  return dst;
}

/* FUNCTION: memset */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef memset

inline void *memset(void *s, int c, size_t n)
{
  __CPROVER_HIDE:
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_buffer_size(s)>=n, "memset buffer overflow");
  //  for(size_t i=0; i<n ; i++) s[i]=c;
  if(__CPROVER_is_zero_string(s) &&
     n > __CPROVER_zero_string_length(s))
  {
    __CPROVER_is_zero_string(s)=1;
  }
  else if(c==0)
  {
    __CPROVER_is_zero_string(s)=1;
    __CPROVER_zero_string_length(s)=0;
  }
  else
    __CPROVER_is_zero_string(s)=0;
  #else
  char *sp=s;
  for(__CPROVER_size_t i=0; i<n ; i++) sp[i]=c;
  #endif
  return s;
}

/* FUNCTION: __builtin___memset_chk */

void *__builtin___memset_chk(void *s, int c, unsigned n, __CPROVER_size_t size)
{
  __CPROVER_HIDE:
  char *sp=s;
  for(__CPROVER_size_t i=0; i<n ; i++) sp[i]=c;
  return s;
}

/* FUNCTION: memmove */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef memmove

inline void *memmove(void *dest, const void *src, size_t n)
{
  __CPROVER_HIDE:
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_buffer_size(src)>=n, "memmove buffer overflow");
  // dst = src (with overlap allowed)
  if(__CPROVER_is_zero_string(src) &&
     n > __CPROVER_zero_string_length(src))
  {
    __CPROVER_is_zero_string(src)=1;
    __CPROVER_zero_string_length(dest)=__CPROVER_zero_string_length(src);
  }
  else
    __CPROVER_is_zero_string(dest)=0;
  #else
  if(dest-src>=n)
  {
    for(__CPROVER_size_t i=0; i<n; i++) ((char *)dest)[i]=((const char *)src)[i];
  }
  else 
  {
    for(__CPROVER_size_t i=n; i>0; i--) ((char *)dest)[i-1]=((const char *)src)[i-1];
  }
  #endif
  return dest;
}

/* FUNCTION: memcmp */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef memcmp

inline int memcmp(const void *s1, const void *s2, size_t n)
{
  __CPROVER_HIDE:;
  int res;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_buffer_size(s1)>=n, "memcmp buffer overflow of 1st argument");
  __CPROVER_assert(__CPROVER_buffer_size(s2)>=n, "memcmp buffer overflow of 2nd argument");
  #else
  const unsigned char *sc1=s1, *sc2=s2;
  for(; n!=0; n--)
  {
    res = (s1++) - (s2++);
    if (res != 0)
      return res;
  }
  #endif
  return res;
}

/* FUNCTION: strchr */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strchr

inline char *strchr(const char *src, int c)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strchr zero-termination of string argument");
  _Bool found;
  __CPROVER_size_t i;
  return found?src+i:0;
  #else
  for(__CPROVER_size_t i=0; src[i]!=0; i++)
    if(src[i]==(char)c)
      return ((char *)src)+i; // cast away const-ness

  return 0;
  #endif
}

/* FUNCTION: strrchr */

#ifndef __CPROVER_STRING_H_INCLUDED
#include <string.h>
#define __CPROVER_STRING_H_INCLUDED
#endif

#undef strchr

inline char *strrchr(const char *src, int c)
{
  __CPROVER_HIDE:;
  #ifdef __CPROVER_STRING_ABSTRACTION
  __CPROVER_assert(__CPROVER_is_zero_string(src), "strrchr zero-termination of string argument");
  _Bool found;
  __CPROVER_size_t i;
  return found?((char *)src)+i:0;
  #else
  char *res=0;
  for(__CPROVER_size_t i=0; src[i]!=0; i++)
    if(src[i]==(char)c) res=((char *)src)+i;
  return res;
  #endif
}

