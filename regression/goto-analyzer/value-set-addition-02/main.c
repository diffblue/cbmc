int unknown();

int main(int argc, char argv[]) {
  int p = 1;
  int q = 2;

  if (unknown())
    p = 1;
  else
    p = 2; 


  int t = p + q;
}
