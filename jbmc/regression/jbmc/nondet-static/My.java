public class My {
  public static int val() { return 3; }

  public static int p1;
  public static int p2 = 1;
  public static int p3;
  static { p3 = 2; }
  public static int p4 = val();
  public static Integer p5 = new Integer(5);

  public static final int pf1 = 1;
  public static final int pf2;
  static { pf2 = 2; }
  public static final int pf3 = val();
  public static final Integer pf4 = new Integer(4);

  private static int pr1;
  private static int pr2 = 1;
  private static int pr3;
  static { pr3 = 2; }
  private static int pr4 = val();
  private static Integer pr5 = new Integer(5);

  private static final int prf1 = 1;
  private static final int prf2;
  static { prf2 = 2; }
  private static final int prf3 = val();
  private static final Integer prf4 = new Integer(4);

  // for inner classes, the missing cases of the above fields do not compile
  public class PInner {
    public static final int pf1 = 1;

    private static final int prf1 = 1;
  }

  public static class PSInner {
    public static int p1;
    public static int p2 = 1;
    public static int p3;
    static { p3 = 2; }
    public static int p4 = val();
    public static Integer p5 = new Integer(5);

    public static final int pf1 = 1;
    public static final int pf2;
    static { pf2 = 2; }
    public static final int pf3 = val();
    public static final Integer pf4 = new Integer(4);

    private static int pr1;
    private static int pr2 = 1;
    private static int pr3;
    static { pr3 = 2; }
    private static int pr4 = val();
    private static Integer pr5 = new Integer(5);

    private static final int prf1 = 1;
    private static final int prf2;
    static { prf2 = 2; }
    private static final int prf3 = val();
    private static final Integer prf4 = new Integer(4);
  }

  private class PrInner {
    public static final int pf1 = 1;

    private static final int prf1 = 1;
  }

  private static class PrSInner {
    public static int p1;
    public static int p2 = 1;
    public static int p3;
    static { p3 = 2; }
    public static int p4 = val();
    public static Integer p5 = new Integer(5);

    public static final int pf1 = 1;
    public static final int pf2;
    static { pf2 = 2; }
    public static final int pf3 = val();
    public static final Integer pf4 = new Integer(4);

    private static int pr1;
    private static int pr2 = 1;
    private static int pr3;
    static { pr3 = 2; }
    private static int pr4 = val();
    private static Integer pr5 = new Integer(5);

    private static final int prf1 = 1;
    private static final int prf2;
    static { prf2 = 2; }
    private static final int prf3 = val();
    private static final Integer prf4 = new Integer(4);
  }

  public int field;
  public My(int i) {
    String s = "bla";
    field = i;
    if (p1 != 0)
      field = 108; // this line can only be covered with nondet-static
    if (p2 != 1)
      field = 108; // this line can only be covered with nondet-static
    if (p3 != 2)
      field = 108; // this line can only be covered with nondet-static
    if (p4 != 3)
      field = 108; // this line can only be covered with nondet-static
    if (!p5.equals(5))
      field = 108; // this line can only be covered with nondet-static

    if (pf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static
    if (pf2 != 2)
      field = 108; // this line cannot be covered even with nondet-static
    if (pf3 != 3)
      field = 108; // this line cannot be covered even with nondet-static
    if (!pf4.equals(4))
      field = 108; // this line cannot be covered even with nondet-static

    if (pr1 != 0)
      field = 108; // this line can only be covered with nondet-static
    if (pr2 != 1)
      field = 108; // this line can only be covered with nondet-static
    if (pr3 != 2)
      field = 108; // this line can only be covered with nondet-static
    if (pr4 != 3)
      field = 108; // this line can only be covered with nondet-static
    if (!pr5.equals(5))
      field = 108; // this line can only be covered with nondet-static

    if (prf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static
    if (prf2 != 2)
      field = 108; // this line cannot be covered even with nondet-static
    if (prf3 != 3)
      field = 108; // this line cannot be covered even with nondet-static
    if (!prf4.equals(4))
      field = 108; // this line cannot be covered even with nondet-static

    if (PInner.pf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static

    if (PInner.prf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static

    if (PSInner.p1 != 0)
      field = 108; // this line can only be covered with nondet-static
    if (PSInner.p2 != 1)
      field = 108; // this line can only be covered with nondet-static
    if (PSInner.p3 != 2)
      field = 108; // this line can only be covered with nondet-static
    if (PSInner.p4 != 3)
      field = 108; // this line can only be covered with nondet-static
    if (!PSInner.p5.equals(5))
      field = 108; // this line can only be covered with nondet-static

    if (PSInner.pf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static
    if (PSInner.pf2 != 2)
      field = 108; // this line cannot be covered even with nondet-static
    if (PSInner.pf3 != 3)
      field = 108; // this line cannot be covered even with nondet-static
    if (!PSInner.pf4.equals(4))
      field = 108; // this line cannot be covered even with nondet-static

    if (PSInner.pr1 != 0)
      field = 108; // this line can only be covered with nondet-static
    if (PSInner.pr2 != 1)
      field = 108; // this line can only be covered with nondet-static
    if (PSInner.pr3 != 2)
      field = 108; // this line can only be covered with nondet-static
    if (PSInner.pr4 != 3)
      field = 108; // this line can only be covered with nondet-static
    if (!PSInner.pr5.equals(5))
      field = 108; // this line can only be covered with nondet-static

    if (PSInner.prf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static
    if (PSInner.prf2 != 2)
      field = 108; // this line cannot be covered even with nondet-static
    if (PSInner.prf3 != 3)
      field = 108; // this line cannot be covered even with nondet-static
    if (!PSInner.prf4.equals(4))
      field = 108; // this line cannot be covered even with nondet-static

    if (PrInner.pf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static

    if (PrInner.prf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static

    if (PrSInner.p1 != 0)
      field = 108; // this line can only be covered with nondet-static
    if (PrSInner.p2 != 1)
      field = 108; // this line can only be covered with nondet-static
    if (PrSInner.p3 != 2)
      field = 108; // this line can only be covered with nondet-static
    if (PrSInner.p4 != 3)
      field = 108; // this line can only be covered with nondet-static
    if (!PrSInner.p5.equals(5))
      field = 108; // this line can only be covered with nondet-static

    if (PrSInner.pf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static
    if (PrSInner.pf2 != 2)
      field = 108; // this line cannot be covered even with nondet-static
    if (PrSInner.pf3 != 3)
      field = 108; // this line cannot be covered even with nondet-static
    if (!PrSInner.pf4.equals(4))
      field = 108; // this line cannot be covered even with nondet-static

    if (PrSInner.pr1 != 0)
      field = 108; // this line can only be covered with nondet-static
    if (PrSInner.pr2 != 1)
      field = 108; // this line can only be covered with nondet-static
    if (PrSInner.pr3 != 2)
      field = 108; // this line can only be covered with nondet-static
    if (PrSInner.pr4 != 3)
      field = 108; // this line can only be covered with nondet-static
    if (!PrSInner.pr5.equals(5))
      field = 108; // this line can only be covered with nondet-static

    if (PrSInner.prf1 != 1)
      field = 108; // this line cannot be covered even with nondet-static
    if (PrSInner.prf2 != 2)
      field = 108; // this line cannot be covered even with nondet-static
    if (PrSInner.prf3 != 3)
      field = 108; // this line cannot be covered even with nondet-static
    if (!PSInner.prf4.equals(4))
      field = 108; // this line cannot be covered even with nondet-static

    if (s != "bla")
      field = 108; // this line cannot be covered even with nondet-static
  }
}
