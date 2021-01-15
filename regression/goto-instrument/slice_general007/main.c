// This is a benchmark for the full-slicer
// This is a simplified version of end-to-end regression tests
// 'general005', 'general006', and 'general007' of the security-scanner.

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>

struct object
{
  bool Tainted_stream;
};

struct java_array
{
  struct object super;
  char *data;
  int length;
};

struct java_array_wrapper
{
  struct java_array super;
  bool Tainted_byte_array;
};

struct InputStream
{
  struct object super;
  struct java_array_wrapper *s;
};

struct ServletInputStream
{
  struct InputStream super;
};

struct HttpServletRequest
{
  struct ServletInputStream *s;
};

void getBytes(struct java_array_wrapper *data, struct InputStream *in)
{
  // These 2 lines are wrongly sliced away!
  if(in->super.Tainted_stream)
    data->Tainted_byte_array = true;
}

struct InputStream *getInputStream(struct HttpServletRequest *this)
{
  return &this->s->super;
}

struct InputStream *getInStream(struct HttpServletRequest *request)
{
  struct InputStream *x = getInputStream(request);
  x->super.Tainted_stream = true;
  return x;
}

extern void *CProver_nondetWithNull();

int main()
{
  struct HttpServletRequest *request = CProver_nondetWithNull();
  struct InputStream *in0 = getInStream(request);
  struct InputStream *in = in0;
  struct java_array_wrapper *data,
    *tmp1 =
      (struct java_array_wrapper *)malloc(sizeof(struct java_array_wrapper));
  tmp1->Tainted_byte_array = false;
  tmp1->super.super.Tainted_stream = false;
  data = tmp1;
  getBytes(data, in);
  if(data->Tainted_byte_array)
    assert(false);
  return 0;
}
