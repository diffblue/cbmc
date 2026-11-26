/* FUNCTION: wcslen */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

// C23 7.31.4.6.1: the number of wide characters that precede the
// terminating null wide character
size_t wcslen(const wchar_t *s)
{
__CPROVER_HIDE:;
  __CPROVER_size_t len = 0;
  while(s[len] != 0)
    len++;
  return len;
}

/* FUNCTION: wmemcmp */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

// C23 7.31.4.4.5: compares the first n wide characters of s1 and s2
int wmemcmp(const wchar_t *s1, const wchar_t *s2, size_t n)
{
__CPROVER_HIDE:;
  for(__CPROVER_size_t i = 0; i < n; i++)
  {
    if(s1[i] != s2[i])
      return s1[i] < s2[i] ? -1 : 1;
  }
  return 0;
}

/* FUNCTION: wmemchr */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

// C23 7.31.4.6.8: the first occurrence of c in the first n wide characters
// of s, or a null pointer
wchar_t *wmemchr(const wchar_t *s, wchar_t c, size_t n)
{
__CPROVER_HIDE:;
  for(__CPROVER_size_t i = 0; i < n; i++)
  {
    if(s[i] == c)
      return (wchar_t *)(s + i);
  }
  return (wchar_t *)0;
}

/* FUNCTION: wmemcpy */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

// C23 7.31.4.2.3: copies n wide characters; the objects shall not overlap
wchar_t *wmemcpy(wchar_t *restrict s1, const wchar_t *restrict s2, size_t n)
{
__CPROVER_HIDE:;
  __CPROVER_precondition(
    __CPROVER_POINTER_OBJECT(s1) != __CPROVER_POINTER_OBJECT(s2) ||
      ((const wchar_t *)s1 >= s2 + n) || ((const wchar_t *)s1 + n <= s2),
    "wmemcpy src/dst overlap");
  for(__CPROVER_size_t i = 0; i < n; i++)
    s1[i] = s2[i];
  return s1;
}

/* FUNCTION: wmemmove */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

// C23 7.31.4.2.4: copies n wide characters as if through a temporary array
wchar_t *wmemmove(wchar_t *s1, const wchar_t *s2, size_t n)
{
__CPROVER_HIDE:;
  if((const wchar_t *)s1 < s2)
  {
    for(__CPROVER_size_t i = 0; i < n; i++)
      s1[i] = s2[i];
  }
  else
  {
    for(__CPROVER_size_t i = n; i > 0; i--)
      s1[i - 1] = s2[i - 1];
  }
  return s1;
}

/* FUNCTION: wmemset */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

// C23 7.31.4.7.1: copies c into each of the first n wide characters of s
wchar_t *wmemset(wchar_t *s, wchar_t c, size_t n)
{
__CPROVER_HIDE:;
  for(__CPROVER_size_t i = 0; i < n; i++)
    s[i] = c;
  return s;
}

/* FUNCTION: wcstol */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#  include <stdlib.h>
#  define __CPROVER_STDLIB_H_INCLUDED
#endif

#undef strtol

// C23 7.31.4.1.2: wcstol is strtol on wide strings.  The characters
// strtol accepts are members of the basic character set, the same in
// both encodings (C23 5.2.1.1); any other character ends the subject
// sequence.  The model of strtol reads at most 31 characters: convert a
// narrowed copy of those.
long wcstol(const wchar_t *nptr, wchar_t **endptr, int base)
{
__CPROVER_HIDE:;
  char narrowed[32];
  int i = 0;
  for(; i < 31; ++i)
  {
    wchar_t ch = nptr[i];
    narrowed[i] = ch > 0 && ch < 128 ? (char)ch : (ch == 0 ? 0 : 127);
    if(ch == 0)
      break;
  }
  narrowed[i < 31 ? i : 31] = 0;
  char *end;
  long result = strtol(narrowed, &end, base);
  if(endptr != 0)
    *endptr = (wchar_t *)nptr + (end - narrowed);
  return result;
}

/* FUNCTION: wcstoul */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#  include <stdlib.h>
#  define __CPROVER_STDLIB_H_INCLUDED
#endif

#undef strtoul

// C23 7.31.4.1.2: wcstoul is strtoul on wide strings.  The characters
// strtoul accepts are members of the basic character set, the same in
// both encodings (C23 5.2.1.1); any other character ends the subject
// sequence.  The model of strtoul reads at most 31 characters: convert a
// narrowed copy of those.
unsigned long wcstoul(const wchar_t *nptr, wchar_t **endptr, int base)
{
__CPROVER_HIDE:;
  char narrowed[32];
  int i = 0;
  for(; i < 31; ++i)
  {
    wchar_t ch = nptr[i];
    narrowed[i] = ch > 0 && ch < 128 ? (char)ch : (ch == 0 ? 0 : 127);
    if(ch == 0)
      break;
  }
  narrowed[i < 31 ? i : 31] = 0;
  char *end;
  unsigned long result = strtoul(narrowed, &end, base);
  if(endptr != 0)
    *endptr = (wchar_t *)nptr + (end - narrowed);
  return result;
}

/* FUNCTION: wcstoll */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#  include <stdlib.h>
#  define __CPROVER_STDLIB_H_INCLUDED
#endif

#undef strtoll

// C23 7.31.4.1.2: wcstoll is strtoll on wide strings.  The characters
// strtoll accepts are members of the basic character set, the same in
// both encodings (C23 5.2.1.1); any other character ends the subject
// sequence.  The model of strtoll reads at most 31 characters: convert a
// narrowed copy of those.
long long wcstoll(const wchar_t *nptr, wchar_t **endptr, int base)
{
__CPROVER_HIDE:;
  char narrowed[32];
  int i = 0;
  for(; i < 31; ++i)
  {
    wchar_t ch = nptr[i];
    narrowed[i] = ch > 0 && ch < 128 ? (char)ch : (ch == 0 ? 0 : 127);
    if(ch == 0)
      break;
  }
  narrowed[i < 31 ? i : 31] = 0;
  char *end;
  long long result = strtoll(narrowed, &end, base);
  if(endptr != 0)
    *endptr = (wchar_t *)nptr + (end - narrowed);
  return result;
}

/* FUNCTION: wcstoull */

#ifndef __CPROVER_WCHAR_H_INCLUDED
#  include <wchar.h>
#  define __CPROVER_WCHAR_H_INCLUDED
#endif

#ifndef __CPROVER_STDLIB_H_INCLUDED
#  include <stdlib.h>
#  define __CPROVER_STDLIB_H_INCLUDED
#endif

#undef strtoull

// C23 7.31.4.1.2: wcstoull is strtoull on wide strings.  The characters
// strtoull accepts are members of the basic character set, the same in
// both encodings (C23 5.2.1.1); any other character ends the subject
// sequence.  The model of strtoull reads at most 31 characters: convert a
// narrowed copy of those.
unsigned long long wcstoull(const wchar_t *nptr, wchar_t **endptr, int base)
{
__CPROVER_HIDE:;
  char narrowed[32];
  int i = 0;
  for(; i < 31; ++i)
  {
    wchar_t ch = nptr[i];
    narrowed[i] = ch > 0 && ch < 128 ? (char)ch : (ch == 0 ? 0 : 127);
    if(ch == 0)
      break;
  }
  narrowed[i < 31 ? i : 31] = 0;
  char *end;
  unsigned long long result = strtoull(narrowed, &end, base);
  if(endptr != 0)
    *endptr = (wchar_t *)nptr + (end - narrowed);
  return result;
}
