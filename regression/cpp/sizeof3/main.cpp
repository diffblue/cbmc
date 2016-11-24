int iDebugRec [20] ;

void bar() {
  unsigned s;
  s=sizeof(iDebugRec);
  s=sizeof(iDebugRec[0]);
  iDebugRec[0]=1;
}

int main()
{
  bar();
  return 0;
}

