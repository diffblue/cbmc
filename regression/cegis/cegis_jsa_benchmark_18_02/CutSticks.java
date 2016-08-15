package com.sanjay.hackerrank;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class CutSticks {
	/* Cut Sticks
	 * Given an array of integers, Subtract the minimum from the entire array elements till its zero.
	 * At each step return the size of non-zero elements that are being subtracted. Once an element=0
	 * ignore it.
	 * */
	public static void main(String[] args) {
		Scanner in = new Scanner(System.in);
		Integer size = in.nextInt();
		List<Integer> list = new ArrayList<Integer>();
		List<Integer> counts = null;

		while (size > 0) {
			String res = in.next();
			list.add(Integer.parseInt(res));
			size--;

		}
		in.close();

		counts = getCount(list);

		for (Integer integer : counts) {
			System.out.println(integer);
		}
	}

	private static List<Integer> getCount(List<Integer> list) {
		List<Integer> size = new ArrayList<Integer>();
		List<Integer> nonZero = null;

		while (list.size() > 0) {
			List<Integer> newList = new ArrayList<Integer>();
			nonZero = removeZero(list);
			Integer min = getMin(nonZero);
			size.add(nonZero.size());

			for (Integer integer : nonZero) {
				if ((integer - min) > 0)
					newList.add(integer - min);
			}
			list = newList;
		}
		return size;
	}

	private static Integer getMin(List<Integer> list) {
		Integer min = list.get(0);

		for (int i = 1; i < list.size(); i++) {
			if (list.get(i) < min)
				min = list.get(i);
		}
		return min;
	}

	private static List<Integer> removeZero(List<Integer> list) {
		List<Integer> nonZero = new ArrayList<Integer>();

		for (int i = 0; i < list.size(); i++) {
			if (list.get(i) > 0)
				nonZero.add(list.get(i));
		}
		return nonZero;
	}
}
