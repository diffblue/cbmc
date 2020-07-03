struct lexigraphically_ordered_struct
{
  int a;
  int b;
};

struct lexigraphically_unordered_struct
{
  int b;
  int a;
};

struct lexigraphically_ordered_struct los;
struct lexigraphically_ordered_struct los2 = {.a = 3, .b = 4};
struct lexigraphically_ordered_struct los3 = {.b = 4, .a = 3};
struct lexigraphically_ordered_struct los4 = {.a = 3};
struct lexigraphically_ordered_struct los5 = {.b = 4};
struct lexigraphically_ordered_struct los6 = {3, 4};

struct lexigraphically_unordered_struct lus;
struct lexigraphically_unordered_struct lus2 = {.a = 3, .b = 4};
struct lexigraphically_unordered_struct lus3 = {.b = 4, .a = 3};
struct lexigraphically_unordered_struct lus4 = {.a = 3};
struct lexigraphically_unordered_struct lus5 = {.b = 4};
struct lexigraphically_unordered_struct lus6 = {4, 3};

void main(void)
{
  __CPROVER_assert(los.a == 0, "los.a==0");
  __CPROVER_assert(los.b == 0, "los.b==0");
  __CPROVER_assert(los2.a == 3, "los2.a==3");
  __CPROVER_assert(los2.b == 4, "los2.b==4");
  __CPROVER_assert(los3.a == 3, "los3.a==3");
  __CPROVER_assert(los3.b == 4, "los3.b==4");
  __CPROVER_assert(los4.a == 3, "los4.a==3");
  __CPROVER_assert(los4.b == 0, "los4.b==0");
  __CPROVER_assert(los5.a == 0, "los5.a==0");
  __CPROVER_assert(los5.b == 4, "los5.b==4");
  __CPROVER_assert(los6.a == 3, "los6.a==3");
  __CPROVER_assert(los6.b == 4, "los6.b==4");

  __CPROVER_assert(lus.a == 0, "lus.a==0");
  __CPROVER_assert(lus.b == 0, "lus.b==0");
  __CPROVER_assert(lus2.a == 3, "lus2.a==3");
  __CPROVER_assert(lus2.b == 4, "lus2.b==4");
  __CPROVER_assert(lus3.a == 3, "lus3.a==3");
  __CPROVER_assert(lus3.b == 4, "lus3.b==4");
  __CPROVER_assert(lus4.a == 3, "lus4.a==3");
  __CPROVER_assert(lus4.b == 0, "lus4.b==0");
  __CPROVER_assert(lus5.a == 0, "lus5.a==0");
  __CPROVER_assert(lus5.b == 4, "lus5.b==4");
  __CPROVER_assert(lus6.a == 3, "lus6.a==3");
  __CPROVER_assert(lus6.b == 4, "lus6.b==4");
}
