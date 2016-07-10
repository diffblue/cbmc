package com.netappsid.observable.internal;

import java.util.ListIterator;

import org.junit.Test;

import com.netappsid.collection.ArrayListSet;

public class ListSetIteratorTest
{
	private ArrayListSet<Integer> list;

	@Test
	public void testSetSameObject()
	{
		list = ArrayListSet.of(1, 2);
		ListIterator listIterator = list.listIterator();

		while (listIterator.hasNext())
		{
			Object next = listIterator.next();
			listIterator.set(next);
		}
	}

	@Test
	public void testSetDifferentObject_NotAlreadyInList()
	{
		list = ArrayListSet.of(1);
		ListIterator listIterator = list.listIterator();

		while (listIterator.hasNext())
		{
			Integer next = (Integer) listIterator.next();
			listIterator.set(next + 1);
		}
	}

	@Test(expected = IllegalArgumentException.class)
	public void testSetDifferentObject_AlreadyInList()
	{
		list = ArrayListSet.of(1, 2);
		ListIterator listIterator = list.listIterator();

		while (listIterator.hasNext())
		{
			listIterator.next();
			listIterator.set(2);
		}
	}
}
