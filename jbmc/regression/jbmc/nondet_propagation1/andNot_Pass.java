class BitSet {
  boolean bits[];
  public BitSet()
  {
    int size = org.cprover.CProver.nondetInt();
    org.cprover.CProver.assume(size >= 0);
    bits = new boolean[size];
  }
  public void set(int i)
  {
    org.cprover.CProver.assume(i < bits.length);
    bits[i] = true;
  }
  public boolean get(int i)
  {
    if(i < bits.length)
      return bits[i];
    return false;
  }
  public void andNot(BitSet other)
  {
    for (int i = 0; i < bits.length; i++) {
      bits[i] = bits[i] && !other.get(i);
    }
  }
}

public class andNot_Pass {
  public static void main(String args[]) {
    BitSet b1 = new BitSet();
    b1.set(1);
    b1.set(2);
    BitSet b2 = new BitSet();
    b2.set(0);
    b2.set(2);
    b1.andNot(b2);

    assert(!b1.get(0));
    assert(b1.get(1));
    assert(b1.get(2)); // expected to fail
  }
}
