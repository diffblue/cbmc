#include <assert.h>
#include <string.h>

extern int nondet_int();

int append(char *buf, int pos, char *src)
{
  int len = strlen(src);
  for(int i = 0; i < len; ++i)
  {
    buf[pos + i] = src[i];
    // propagate taint
    __CPROVER_set_field(
      &buf[pos + i], "tainted", __CPROVER_get_field(&src[i], "tainted"));
  }
  return pos + len;
}

void encode(char *buf, char *uname, char *passwd)
{
  int pos = append(buf, 0, "{\"username\":\"");
  pos = append(buf, pos, uname);
  pos = append(buf, pos, "\",\"password\":\"");
  pos = append(buf, pos, passwd);
  pos = append(buf, pos, "\"}");
  buf[pos] = '\0';
}

void make_nondet_len_string(char *buf, _Bool taint)
{
  int len = nondet_int();
  __CPROVER_assume(0 <= len && len < 8);
  buf[len] = '\0';
  // taint the input data
  for(int i = 0; i < len; ++i)
    __CPROVER_set_field(&buf[i], "tainted", taint);
}

int check_part(char *buf, int pos, char *src, _Bool expected)
{
  int len = strlen(src);
  for(int i = 0; i < len; ++i)
  {
    _Bool actual = __CPROVER_get_field(&buf[pos + i], "tainted");
    assert(actual == expected);
  }
  return pos + len;
}

void check(char *buf, char *uname, char *passwd)
{
  int pos = check_part(buf, 0, "{\"username\":\"", 0);
  pos = check_part(buf, pos, uname, 0);
  pos = check_part(buf, pos, "\",\"password\":\"", 0);
  pos = check_part(buf, pos, passwd, 1);
  pos = check_part(buf, pos, "\"}", 0);
  check_part(buf, pos, "\0", 0);
}

void main()
{
  // declare shadow fields
  __CPROVER_field_decl_local("tainted", (_Bool)0);
  __CPROVER_field_decl_global("tainted", (_Bool)0);
  // create harness for SUT
  char uname[8];
  char passwd[8];
  make_nondet_len_string(uname, 0);  // untainted
  make_nondet_len_string(passwd, 1); // tainted
  // call SUT
  char json[46];
  encode(json, uname, passwd);
  // check properties
  check(json, uname, passwd);
}
