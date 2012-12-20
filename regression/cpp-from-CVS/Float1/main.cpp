int main(int argc, char* argv[])
{
  float x = 0.1;
  float y = 1.01;
  assert(x+y >= 1.1);

  double s = x;
  double t = 1;
  assert(x+y >= 1.1);
}
