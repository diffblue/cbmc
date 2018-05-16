
public class Parent {

  // This is the version of Parent we will run jbmc against, which has
  // a static field 'x', but that field is private and cannot correspond
  // to the reference 'Test.x'.
  private static int x;

}
