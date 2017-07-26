
public class test {

  public Other o1;
  public Other o2;

  public void main() {
    if(o1 != null && o2 != null) {
      if(o1.next != null && o2.next != null) {
        next_pointers_not_null();
      }
      toplevel_pointers_not_null();
    }
  }

  public void next_pointers_not_null() {
    // Not currently achievable due to recursive types
    assert(false);
  }

  public void toplevel_pointers_not_null() {
    // Should be possible to hit
    assert(false);
  }

}

class Other {
  int x;
  Other next;
}
