[CPROVER Manual TOC](../../)

## Modeling with Assumptions

Assumptions are used to restrict nondeterministic choices made by the
program. As an example, suppose we wish to model a nondeterministic
choice that returns a number from 1 to 100. There is no integer type
with this range. We therefore use \_\_CPROVER\_assume to restrict the
range of a nondeterministically chosen integer:

```C
unsigned int nondet_uint();

unsigned int one_to_hundred()
{
  unsigned int result=nondet_uint();
  __CPROVER_assume(result>=1 && result<=100);
  return result;
}
```

The function above returns the desired integer from 1 to 100. You must
ensure that the condition given as an assumption is actually satisfiable
by some nondeterministic choice, or otherwise the model checking step
will pass vacuously.

Also note that assumptions are never retroactive: They only affect
assertions (or other properties) that follow them in program order. This
is best illustrated with an example. In the following fragment, the
assumption has no effect on the assertion, which means that the
assertion will fail:

```C
x=nondet_uint();
assert(x==100);
__CPROVER_assume(x==100);
```

Assumptions do restrict the search space, but only for assertions that
follow. As an example, the following program will pass:

```C
int main() {
  int x;

  __CPROVER_assume(x>=1 && x<=100000);

  x*=-1;

  __CPROVER_assert(x<0, "x is negative");
}
```

Beware that nondeterminism cannot be used to obtain the effect of
universal quantification in assumptions. As an example,

```C
int main() {
  int a[10], x, y;

  x=nondet_int();
  y=nondet_int();
  __CPROVER_assume(x>=0 && x<10 && y>=0 && y<10);

  __CPROVER_assume(a[x]>=0);

  assert(a[y]>=0);
}
```

fails, as there is a choice of x and y which results in a counterexample
(any choice in which x and y are different).

