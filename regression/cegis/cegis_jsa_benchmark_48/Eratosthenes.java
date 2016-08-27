package com.madtape.eratosthenes;

import java.util.LinkedList;

public class Eratosthenes {
	
	private LinkedList<Integer> mPrimes;
	
	public Eratosthenes() {
		mPrimes = null;
	}
	
	private boolean isPrime(int x) {
		if(x < 2) return false;
		for(Integer num : mPrimes) {
			if(num * num > x) break;
			if((x % num) == 0)return false; 
		}
		return true;
	}
	
	private void makePrimeList(int max) {
		mPrimes.add(new Integer(2));
		for(int x = 3; x * x < max; x += 2) {
			if(isPrime(x)) mPrimes.add(new Integer(x));
		}
	}
	
	public LinkedList<Integer> findPrimes(int min, int max) {
		mPrimes = new LinkedList<Integer>();
		LinkedList<Integer> retList = new LinkedList<Integer>();
		makePrimeList(max);
		
		for(int x = min; x <= max; x++) {
			if(isPrime(x)) retList.add(new Integer(x));
		}
		return retList;
	}
}
