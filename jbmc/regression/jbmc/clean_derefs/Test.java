
public class Test {

  public int field;

  public Test(int f) { field = f; }

  public static void main(int nondet) {

    // This test creates and uses objects in a few different contexts to check
    // that in all cases goto-symex realises that the dereferenced object cannot
    // be null (due to the NullPointerException check that guards all derefs),
    // therefore symex never generates a reference to any $failed_object symbol
    // that for a C program would stand in for an unknown or invalid object such
    // as a dereferenced null pointer.

    Test t1 = new Test(nondet);
    Test t2 = new Test(nondet);

    Test[] tarray = new Test[5];
    tarray[0] = null;
    tarray[1] = t2;
    tarray[2] = t1;

    t1.field++;
    (nondet == 10 ? t1 : t2).field--;
    tarray[nondet % 5].field++;
    (nondet == 20 ? t1 : tarray[2]).field++;

    Container c1 = new Container(t1);
    Container c2 = new Container(t2);
    Container c3 = new Container(null);

    c1.t.field++;
    (nondet == 30 ? c1 : c3).t.field++;
    (nondet == 40 ? c2.t : tarray[3]).field--;

    // Check that we produce a clean deref when a cast restricts the possible
    // targets of a field access:
    Object o = nondet % 2 == 0 ? new Object() : new Container(new Test(10));
    int field = ((Container)o).t.field;

    assert false;

  }

}

class Container {

  public Container(Test _t) { t = _t; }

  public Test t;

}
