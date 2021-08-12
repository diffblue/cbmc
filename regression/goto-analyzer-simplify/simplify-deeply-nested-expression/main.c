int nondet_int(void);

struct MH
{
  int s;
  int t;
  int to;
  int su;
};

int main(void)
{
  int l = nondet_int();
  int s = nondet_int();
  int n = nondet_int();
  int o = nondet_int();
  int nt = nondet_int();
  int ns = nondet_int();

  struct MH mh;
  mh.s = nondet_int();
  mh.t = nondet_int();
  mh.to = nondet_int();
  mh.su = nondet_int();

  int result =
    ((l >= mh.s ? 1 : 0) &
     (((mh.s >= s ? 1 : 0) &
       (((n >= mh.t ? 1 : 0) &
         (((mh.t >= o ? 1 : 0) & ((((int)mh.to == (int)nt ? 0 : 1) &
                                   ((int)mh.su == (int)ns ? 0 : 1)) == 0
                                    ? 0
                                    : 1)) == 0
            ? 0
            : 1)) == 0
          ? 0
          : 1)) == 0
        ? 0
        : 1)) == 0;

  assert(result = 0);
}
