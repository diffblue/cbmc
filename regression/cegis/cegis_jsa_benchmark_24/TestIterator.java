package com.training.cap7;

import java.util.ArrayList;
import java.util.Collections;
import java.util.ListIterator;

public class TestIterator {

	public static void main(String[] args){
		ArrayList l = new ArrayList<>();
		
		for(int i = 0; i<100;i++){
			l.add(new Integer(i));
		}
		
		Collections.shuffle(l);
		
		for(ListIterator iter = l.listIterator(); iter.hasNext();){
			int x = (int)iter.next();
			
			if( x % 2 == 0){
				iter.set(new Integer(0));
			}
		}
		
		System.out.println(l);
	}
}
