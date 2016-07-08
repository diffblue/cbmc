package misc;

import java.util.Iterator;
import java.util.TreeSet;

import junit.framework.Assert;

import org.junit.Test;

public class TreeSetIteratorRemoveTest {

	@Test
	public void testRemove() {
		
		TreeSet<Integer> ts = new TreeSet<Integer>();
		for (int i = 1; i <= 5; ++i)
			ts.add(i);
		
		for (Iterator<Integer> it = ts.iterator(); it.hasNext(); ) {
			Integer x = it.next();
			if (x == 3) {
				it.remove();
				continue;
			}
		}
		Assert.assertFalse(ts.contains(3));
	}
}
