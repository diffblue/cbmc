class if_expr1
{
  static public void main(String[] args) throws java.io.IOException
  {
    int x=System.in.read();
    int y=x==10?11:9;
    if(x==10)
      assert y==11;
    else
      assert y==9;
  }
};
