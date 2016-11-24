int main()
{
  // this is ok
  double xd=2.3;

  int xi=static_cast<int>(xd);
  
  assert(xi==2);
}
