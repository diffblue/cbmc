public class Test {

  interface factory_intf {
    public intf getintf();
  }

  interface intf {
    public void f();
  }

  public static void main(factory_intf i) { i.getintf().f(); }
}
