typedef unsigned blue;
 
typedef struct { unsigned blue; } ar_t;
typedef struct { ar_t ar; } format_t;
 
int main () {
  // note that 'blue' is a type-token
  format_t data = { .ar.blue = 1 };
  __CPROVER_assert(data.ar.blue==1, "initialization ok");
  return 1;
}
