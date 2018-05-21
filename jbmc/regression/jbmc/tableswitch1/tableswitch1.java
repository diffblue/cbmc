class tableswitch1
{
  public static void main(String[] args)
  {
    int i, j;
    
    java.util.Random random = new java.util.Random(42);
    i=random.nextInt();    

    switch(i)
    {
    case -1: j=0; break;
    case  0: j=1; break;
    case  1: j=2; break;
    case  2: j=3; break;
    case  3: j=4; break;
    case  4: j=5; break;
    case  5: j=6; break;
    case  6: j=7; break;
    case  7: j=8; break;
    case  8: j=9; break;
    case  9: j=10; break;
    case 10: j=11; break;
    case 11: j=12; break;
    default: j=1000;
    }
    
    if(i>=-1 && i<=11)
      assert j==i+1;
    else
      assert j==1000;
  }
}
