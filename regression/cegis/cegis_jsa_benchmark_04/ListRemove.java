package com.mercury.interview;

import java.util.*;

public class ListRemove {
	public static void main(String[] args) {
		List<Integer> list = new ArrayList<Integer>();
		list.add(1);
		list.add(1);
		list.add(3);
		list.add(6);
		list.add(2);
		list.add(1);
		myRemove(list, 1);
		for(int i = 0; i < list.size(); i++) {
			System.out.println(list.get(i));
		}
	}
	public static void myRemove(List<Integer> list, int x) {
		Iterator<Integer> it = list.iterator();
		while(it.hasNext()) {
			int temp = it.next();
			if (x == temp) {
				it.remove();
			}
		}
	}
}
