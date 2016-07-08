package trickyexamples;

import java.util.ConcurrentModificationException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

public class RemoveDuringIteration {
  public static void main(String[] args) {
    final Set<Integer> set = new HashSet<Integer>();
    for (int i = 0; i < 10; i++) {
      set.add(i);
    }

    for (int i = 0; i < 2; i++) {
      Thread t1 = new Thread() {
        @Override
        public void run() {
          iterateAndRemove(set);
          super.run();
        }
      };
      t1.start();
    }

  }

  /**
   * Sometimes this method throws during iteration a {@link ConcurrentModificationException} because
   * of the remove.
   *
   * @param set
   */
  private static void iterateAndRemove(Set<Integer> set) {
    System.out.println("Before remove");
    for (Integer i : set) {
      System.out.println(i);
    }
    Iterator<Integer> it = set.iterator();
    while (it.hasNext()) {
      Integer i = it.next();
      if (i % 2 == 0) {
        // set.remove(i);
        it.remove();
      }
    }
    System.out.println("\nAfter remove");
    for (Integer i : set) {
      System.out.println(i);
    }
  }
}
