package com.thoughtworks.collection;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.*;

public class Filter {

    List<Integer>  array;

    public Filter(List<Integer> array) {
     this.array = array;
    }

    public List<Integer> filterEven() {
        List<Integer> result = new ArrayList<>();

        for(int i=0; i<array.size(); i++){
            if(array.get(i)%2 == 0){
                result.add(array.get(i));
            }
        }

        return result;
    }

    public List<Integer> filterMultipleOfThree() {
        List<Integer> result = new ArrayList<>();

        for(int i=0; i<array.size(); i++){
            if(array.get(i)%3 == 0){
                result.add(array.get(i));
            }
        }

        return result;
    }

    public List<Integer> getDifferentElements() {
        List<Integer> result = new ArrayList<>();

        for(int i=0; i<array.size(); i++){
            if(!result.contains(array.get(i))){
                result.add(array.get(i));
            }
        }

        return result;
    }

    public Map<Integer, Integer> getMapOfArrayList() {
        Map map = new HashMap<Integer,Integer>();

        for(int i=0; i<array.size(); i++){

            Integer element = array.get(i);
            if(map.containsKey(element)){

                Integer previousValue = (Integer) map.get(element);
                map.put(element, ++previousValue);
            }else{
                map.put(element, 1);
            }
        }

        return map;
    }

    public List<List<Integer>> getDividedArray() {

        List<List<Integer>> result = new ArrayList<>();

        for(int i=0; i<array.size(); i++){
            int num = 0;
            for(int j=0; j<result.size(); j++){

                if(result.get(j).contains(array.get(i))){
                    result.get(j).add(array.get(i));
                    break;
                }else {
                    num++;
                }
            }
            if(num == result.size()){
                List<Integer> sonList = new ArrayList<>();
                sonList.add(array.get(i));
                result.add(sonList);
            }
        }

        return result;
    }

    public List<Integer> getCommonElements(List<Integer> firstList, List<Integer> secondList) {
        List<Integer> result = new ArrayList<>();

        for(int i=0; i<firstList.size(); i++){
            if(secondList.contains(firstList.get(i))){
                result.add(firstList.get(i));
            }
        }

        return result;
    }

    public List<Integer> getUncommonElements(List<Integer> firstList, List<Integer> secondList) {

        List<Integer> result = new ArrayList<>();

        for(int i=0; i<firstList.size(); i++){
            if(!secondList.contains(firstList.get(i))){
                result.add(firstList.get(i));
            }
        }

        return result;
    }

    public List<Integer> getElementsByRelationship(FilterHandler filterHandler, List<Integer> objectList) {
        throw new NotImplementedException();
    }
}