struct st1
{
  int a;
  int arr[10];
};

struct st2
{
  int a;
  struct st1 arr[10];
};

struct st3
{
  struct st1 *s1;
  struct st2 *s2;
  struct st1 arr1[10];
  struct st2 arr2[10];
};

enum tagt
{
  CHAR,
  INT,
  CHAR_PTR,
  INT_ARR,
  STRUCT_ST1_ARR
};

// clang-format off
struct taggedt {
  enum tagt tag;
  union {
    struct{ char a; };
    struct{ int b; };
    struct{ char *ptr; };
    struct{ int arr[10]; };
    struct{ struct st1 arr1[10]; };
  };
};
// clang-format on

int foo(int i) __CPROVER_assigns()
{
  // all accesses to locals should pass
  int arr[10];
  struct st1 s1;
  struct st2 s2;
  struct st1 dirty_s1;
  struct st3 s3;
  s3.s1 = &dirty_s1;
  s3.s2 = malloc(sizeof(struct st2));

  if(0 <= i && i < 10)
  {
    arr[i] = 0;
    s1.a = 0;
    s1.arr[i] = 0;
    s2.a = 0;
    s2.arr[i].a = 0;
    s2.arr[i].arr[i] = 0;
    s3.s1->a = 0;
    s3.s1->arr[i] = 0;
    s3.s2->a = 0;
    s3.s2->arr[i].a = 0;
    s3.s2->arr[i].arr[i] = 0;
    *(&(s3.s2->arr[i].arr[0]) + i) = 0;
    (&(s3.arr1[0]) + i)->arr[i] = 0;
    (&((&(s3.arr2[0]) + i)->arr[i]))->a = 0;
  }

  struct taggedt tagged;
  switch(tagged.tag)
  {
  case CHAR:
    tagged.a = 0;
    break;
  case INT:
    tagged.b = 0;
    break;
  case CHAR_PTR:
    tagged.ptr = 0;
    break;
  case INT_ARR:
    if(0 <= i && i < 10)
      tagged.arr[i] = 0;
    break;
  case STRUCT_ST1_ARR:
    if(0 <= i && i < 10)
    {
      tagged.arr1[i].a = 0;
      tagged.arr1[i].arr[i] = 0;
    }
    break;
  }

  return 0;
}

void main()
{
  int i;
  foo(i);
}
