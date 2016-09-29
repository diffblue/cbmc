package leetcode.l1405;

import java.util.*;

public class CombinationSum {
    public ArrayList<ArrayList<Integer>> combinationSum(int[] candidates, int target) {
        if (target == 0)
            return new ArrayList<ArrayList<Integer>>();
        Arrays.sort(candidates);
        
        ArrayList<ArrayList<Integer>> list = new ArrayList<ArrayList<Integer>>();
        list.add(new ArrayList<Integer>());
        
        return combinationSum(candidates, target, 0, list);
    }
    
    private ArrayList<ArrayList<Integer>> combinationSum(int[] a, int target, int s, ArrayList<ArrayList<Integer>> preList) {
        ArrayList<ArrayList<Integer>> list = new ArrayList<ArrayList<Integer>>(); //list for this step
        
        for (int i=s; i<a.length; i++) {
            // scanning from smallest number, see if a[i] can form combo with it's following subarray
            if (a[i] > target) break;
            if (a[i] == target) {
                for (ArrayList<Integer> line: preList){
                    ArrayList<Integer> newLine = new ArrayList<Integer>();
                    for (int j: line) {
                        newLine.add(j);
                    }
                    newLine.add(a[i]);
                    list.add(newLine);
                }
            } else {
                ArrayList<ArrayList<Integer>> tempList = new ArrayList<ArrayList<Integer>>();
                
                for (ArrayList<Integer> line: preList) {
                    ArrayList<Integer> newLine = new ArrayList<Integer>();
                    for (int j: line) {
                        newLine.add(j);
                    }
                    newLine.add(a[i]);
                    tempList.add(newLine);
                }
                
                ArrayList<ArrayList<Integer>> nextList = combinationSum(a, target-a[i], i, tempList);
                
                if (nextList.size()!=0) {
                    list.addAll(nextList);
                }
            }
        }
        return list;
    }
}