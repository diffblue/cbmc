int x = 0;

_Bool f()
{
  x++;
  return x!=10;
}

int main() {
  int y =0;

  for( ; f(); ) {
    y++;
  }

  assert(y == 9);
  assert(x == 10);

}
