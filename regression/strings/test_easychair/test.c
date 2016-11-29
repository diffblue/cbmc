#include <assert.h>
#include "../cprover-string-hack.h"
#define false 0
#define true 1

int main(){
  //IsEasyChairQuery
  __CPROVER_string str;
  // (1) check that str contains "/" followed by anything not
  // containing "/" and containing "EasyChair"
  int lastSlash = __CPROVER_string_last_index_of(str,__CPROVER_char_literal("/"));
  if(lastSlash < 0) {
    __CPROVER_assert(false,"PC1");
    return false;
  }

  __CPROVER_string rest = __CPROVER_string_substring(str,lastSlash + 1, __CPROVER_string_length(str)-1);

  if(! __CPROVER_string_contains(rest,__CPROVER_string_literal("EasyChair"))) {
    __CPROVER_assert(false,"PC2");
    return false;
  }

  // (2) Check that str starts with "http://"
  if(! __CPROVER_string_isprefix(__CPROVER_string_literal("http://"),str)) {
    __CPROVER_assert(false,"PC3");
    return false;
  }
  //(3) Take the string between "http://" and the last "/".
  // if it starts with "www." strip the "www." off
  __CPROVER_string t = __CPROVER_string_substring(str,__CPROVER_string_length(__CPROVER_string_literal("http://")), lastSlash - __CPROVER_string_length(__CPROVER_string_literal("http://")));
  if(__CPROVER_string_isprefix(__CPROVER_string_literal("www."),t))
    t = __CPROVER_string_substring(t,__CPROVER_string_length(__CPROVER_string_literal("www.")), __CPROVER_string_length(t)-1);
  // (4) Check that after stripping we have either "live.com"
  // or "google.com"
  if (!__CPROVER_string_equal(t,__CPROVER_string_literal("live.com")) && !__CPROVER_string_equal(t,__CPROVER_string_literal( "google.com"))) {
    __CPROVER_assert(false,"PC4");
    return false;
  }
  // s survived all checks
  return true;
}
