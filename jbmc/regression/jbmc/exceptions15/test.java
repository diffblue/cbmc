class InetAddress {}
class InetSocketAddress {}

public class test {
  public String lookupPtrRecord(InetAddress address) {
    return "Foo";
  }

  public InetAddress reverse(InetAddress address) {
    return address;
  }

  public void translate(InetAddress address, int i) {
    try {
      String domainName = lookupPtrRecord(reverse(address));
    } catch (Exception e) {
      assert false;
    }
  }
}
