// The inner loop directly follows a backward goto. When path exploration
// resumes the fall-through path of that backward goto, the transition into
// the inner loop's head is a forward one and must reset the inner loop's
// unwinding counter: the inner loop runs 3 times per entry, so --unwind 3
// suffices.
int nondet_int(void);

int main(void)
{
  int i = 0;
  int n = nondet_int();
  __CPROVER_assume(n >= 1 && n <= 2);
outer:;
  int j = 0;
  int k = 0;
back:
  k++;
  if(k < n)
    goto back;
inner:
  j++;
  if(j < 3)
    goto inner;
  i++;
  if(i < 2)
    goto outer;
  return 0;
}
