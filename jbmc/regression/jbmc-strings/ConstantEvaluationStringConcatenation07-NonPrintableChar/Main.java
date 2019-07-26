public class Main {
  public void test() {
    String s1 = "\t";
    String s2 = "\\";
    String s3 = s1 + s2;
    assert s3.length() == 2;
    assert s3.startsWith("\t\\");
  }
}
