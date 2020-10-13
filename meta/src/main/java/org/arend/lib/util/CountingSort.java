package org.arend.lib.util;

import java.util.ArrayList;
import java.util.List;

public class CountingSort {
  public static List<Integer> sort(List<Integer> list) {
    int k = 0;
    List<Integer> result = new ArrayList<>(list.size());
    for (Integer x : list) {
      result.add(0);
      if (x > k) k = x;
    }

    int[] count = new int[k+1];
    for (Integer x : list) {
      count[x] += 1;
    }

    int total = 0;
    for (int i = 0; i <= k; i++) {
      int t = total;
      total += count[i];
      count[i] = t;
    }

    for (Integer x : list) {
      result.set(count[x], x);
      count[x] += 1;
    }
    return result;
  }
}
