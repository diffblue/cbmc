package com.hackerrank.test;

import java.util.ArrayList;
import java.util.List;

public class GenPrime {
	public static void main(String[] args) {
		int pp = 2;
		List<Integer> ps = new ArrayList<Integer>();
		ps.add(pp);
		int limit = 100;
		while (pp < limit){
			pp+=1;
			for (Integer integer : ps) {
				if(pp%integer == 0)
					break;
				else
					ps.add(pp);
			}
			
		}
		for (Integer integer : ps) {
			System.out.println(integer);
		}
	}
}
