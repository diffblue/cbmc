class method_parameters
{
  void test1()
  {}

  void test2(boolean b)
  {}

  void test3(byte b)
  {}

  void test3a(char c)
  {}

  void test4(int i)
  {}

  void test5(float f)
  {}

  void test6(String s)
  {}

  void test7(long l)
  {}

  void test8(double l)
  {}

  void test9(int i, long l)
  {
    int local = 123;
  }

  void test10(double i, String s)
  {
    int local = 123;
  }

  void test11(int a[][])
  {}

  double test12(double a[][], double d)
  {
    if (a.length < 1) return 0;
    if (a[0].length < 1) return 0;
    return d + a[0][0];
  }

  void test12a(double a[][][], int i, double d)
  {}

  double test12b(double a[][], double d)
  {
    return 123.123;
  }

  void test12c(double a[][][], double d)
  {
  }

  void test13(double d, int i, byte b, char c)
  {}

  // Same as above but now static

  static void ttest1()
  {}

  static void ttest2(boolean b)
  {}

  static void ttest3(byte b)
  {}

  static void ttest3a(char c)
  {}

  static void ttest4(int i)
  {}

  static void ttest5(float f)
  {}

  static void ttest6(String s)
  {}

  static void ttest7(long l)
  {}

  static void ttest8(double l)
  {}

  static void ttest9(int i, long l)
  {
    int local = 123;
  }

  static void ttest10(double i, String s)
  {
    int local = 123;
  }

  static void ttest11(int a[][])
  {}

  static double ttest12(double a[][], double d)
  {
    if (a.length < 1) return 0;
    if (a[0].length < 1) return 0;
    return d + a[0][0];
  }

  static void ttest12a(double a[][][], int i, double d)
  {}

  static double ttest12b(double a[][], double d)
  {
    return 123.123;
  }

  static void ttest12c(double a[][][], double d)
  {
  }

  static void ttest13(double d, int i, byte b, char c)
  {}

}
