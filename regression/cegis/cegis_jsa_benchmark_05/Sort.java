package ru.hse.example;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

public class Sort {

	public static void main(String[] args) {
		ArrayList<Integer> list = new ArrayList<Integer>();
		list.add( 3 );
		list.add(7);
		list.add(1);
		list.add(4);
		list.add(8);
		list.add(2);

		System.out.println(sort2(list));
		System.out.println(sort1(list));
	}

	static List<Integer> sort1(List<Integer> list) {
		List<Integer> res = new ArrayList<Integer>(list.size());

		while (!list.isEmpty())
			res.add(removeMax(list));

		return res;
	}

	static List<Integer> sort2(List<Integer> list) {
		List<Integer> res = new LinkedList<Integer>();

		for (int v : list)
			insertDesc(res, v);

		return res;
	}

	static int removeMax(List<Integer> list) {
		Integer max = list.get(0);

		for ( Integer v : list )
			if ( v > max )
				max = v;

		list.remove(max);

		return max;
	}

	static int removeMax1(List<Integer> list) {
		Iterator<Integer> it = list.iterator();
		Integer max = it.next();

		while ( it.hasNext() ) {
			Integer v = it.next();

			if ( v > max )
				max = v;
		}

		list.remove(max);

		return max;
	}

	static void insertDesc(List<Integer> list, int value) {
		ListIterator<Integer> it = list.listIterator();

		while (it.hasNext() && it.next() > value );

		if (it.hasPrevious())
			if (it.previous() > value)
				it.next();

		it.add(value);
	}


}
