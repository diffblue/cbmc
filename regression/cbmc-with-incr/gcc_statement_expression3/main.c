int state;

int doassert()
{
  assert(state == 3);
  return 0;
}

int main() {
  int x;

  /*x =*/ ( // COMMENT 'x =' BACK IN, AND THINGS WORK
    {
      state = 3;
      doassert();
    }
    );

  return 0;

}
