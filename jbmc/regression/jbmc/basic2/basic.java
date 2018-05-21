class basic2
{
  void other_method(int q)
  {
    q++;
  }
}

class basic {
    public static void main(String[] args) {
      some_method(123, 456);
      basic2 b=new basic2();
      b.other_method(123);
    }
    
    public static void some_method(int p, int q)
    {
    }

    int some_field;
}

