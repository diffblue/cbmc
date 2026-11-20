#define C 10

// const in brackets: no modification of x is fine
void f_const(int x[const C], int i)
{
  x[i] = x[i] + 1;
}

// restrict in brackets
void f_restrict(int x[restrict C], int i)
{
  x[i] = 1;
}

// volatile in brackets
void f_volatile(int x[volatile C], int i)
{
  x[i] = 1;
}

// static in brackets: caller guarantees min size
void f_static(int x[static C], int i)
{
  x++;
  x[i] = 1;
}

// const and static combined
void f_const_static(int x[const static C], int i)
{
  x[i] = 1;
}

// type compatibility: declaration without qualifiers, definition with
void f_compat(int x[C]);
void f_compat(int x[const C])
{
  x[0] = 1;
}

// no qualifiers: increment should be fine
void f_none(int x[C], int i)
{
  x++;
  x[i] = 1;
}

int main()
{
  int arr[C];
  f_const(arr, 0);
  f_restrict(arr, 0);
  f_volatile(arr, 0);
  f_static(arr, 0);
  f_const_static(arr, 0);
  f_compat(arr);
  f_none(arr, 0);
  return 0;
}
