// From Cousot's FMSD paper

void main()
{
  int x, y, _x = __VERIFIER_nondet_int(), _y = __VERIFIER_nondet_int();

  x = _x;
  y = _y;

  if(
    (-4681 < y) && (y < 4681) && (x < 32767) && (-32767 < x) &&
    ((7 * y * y - 1) == x * x))
  {
    y = 1 / x;
  }
}
