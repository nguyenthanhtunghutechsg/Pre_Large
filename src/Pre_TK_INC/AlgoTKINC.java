package Pre_TK_INC;


import PIHUPM.AlgoPIHUPM;

import java.io.*;
import java.text.SimpleDateFormat;
import java.util.*;
import java.util.Map.Entry;
/* This file is copyright (c) 2008-2015 Srikumar Krishnamoorty
 *
 * This file is part of the SPMF DATA MINING SOFTWARE
 * (http://www.philippe-fournier-viger.com/spmf).
 *
 * SPMF is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * SPMF is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License along with
 * SPMF. If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * Implementation of the THUI algorithm as proposed in this paper: <br/>
 * <br/>
 * <br/>
 * Srikumar Krishnamoorthy: Mining top-k high utility itemsets with effective
 * threshold raising strategies. Expert Syst. Appl. 117: 148-165 (2019)
 *
 * @author Srikumar Krishnamoorty
 */
public class AlgoTKINC {

    // variable for statistics
    /**
     * the maximum memory usage
     */
    public double maxMemory = 0;
    /**
     * the time the algorithm started
     */
    public long startTimestamp = 0;
    public long startTimestampPha2 = 0;
    /**
     * the time the algorithm terminated
     */
    public long endTimestamp = 0;
    /**
     * the number of HUI generated
     */
    public int huiCount = 0;
    /**
     * the number of candidates
     */
    public int candidateCount = 0;

    /**
     * map that indicate the TWU of each item (key)
     */
    Map<Integer, Integer> mapItemToTWU;

    /**
     * internal minimum utility threshold
     */
    long minUtility_upper = 0;
    long minUtility_lower = 0;
    /**
     * the number k of patterns to be found
     */
    int upper_topkstatic = 0;
    int lower_topkstatic = 0;

    /**
     * writer to write the output file
     */
    BufferedWriter writer = null;

    /**
     * Priority queue to store the top k patterns
     */
    PriorityQueue<PatternTHUI> k_Pre_Large_And_Large_Patterns;
    PriorityQueue<Long> leafPruneUtils = null;


    /**
     * During first database, the item are sorted by TWU.... Then we keep this ordering
     * in the following map because if the ordering change in an updated database,
     * then the result may be incorrect.
     */
    Map<Integer, Integer> mapItemToRank;

    private java.text.DecimalFormat df = new java.text.DecimalFormat("#.00");
    Map<Integer, Map<Integer, ItemTHUI>> mapFMAP = null;
    private StringBuilder buffer = new StringBuilder(32);

    Map<Integer, Map<Integer, Long>> mapLeafMAP = null;

    List<Node> singleItemsNodes;

    int[] totUtil;
    int[] ej;
    int[] pos;
    int[] twu;

    //boolean EUCS_PRUNE = false;

    class Pair {
        int item = 0;
        int utility = 0;

        Pair(int item, int utility) {
            this.item = item;
            this.utility = utility;
        }

        public String toString() {
            return "[" + item + "," + utility + "]";
        }
    }

    class PairComparator implements Comparator<Pair> {
        @Override
        public int compare(Pair o1, Pair o2) {
            return compareItemsByRank(o1.item, o2.item);
        }
    }

    class UtilComparator implements Comparator<UtilityList> {
        @Override
        public int compare(UtilityList o1, UtilityList o2) {
            return compareItemsByRank(o1.item, o2.item);
        }
    }

    public AlgoTKINC() {

    }

    String inputFile;
    boolean firstTime;
    Map<Integer, UtilityList> mapItemToUtilityList;
    int firstLine;
    Map<Integer, Long> mapItemToUtility;


    /**
     * This is the total utility of all transactions in Incremental Database
     */
    long totalDBUtility_ID;
    /**
     * This is the total utility of all transactions in Original Database
     */
    long totalDBUtility_OD;
    long minUtility_upper_previous = 0;
    long minUtility_lower_previous = 0;
    /**
     * Run the algorithm
     *
     * @param input       path to the input file
     * @param output      path to the output file
     * @param eucsPrune   if true, the EUCS strategy will be activated
     * @param lower_top_k the number of patterns to be found
     * @param upper_top_k the number of patterns to be found
     * @throws IOException if writing or reading error from file
     */
    public void runAlgorithm(String input, String output, boolean eucsPrune, int lower_top_k, int upper_top_k,
                             int firstLine, int lastLine) throws IOException {
        upper_topkstatic = upper_top_k;
        lower_topkstatic = lower_top_k;

        maxMemory = 0;

        this.firstLine = firstLine;
        inputFile = input;
        if (firstLine == 0) {
            firstTime = true;
        } else {
            firstTime = false;
        }

        if (firstTime) {
            mapItemToUtilityList = new HashMap<>();
            mapItemToUtility = new HashMap<Integer, Long>();
            mapItemToTWU = new HashMap<Integer, Integer>();
            mapLeafMAP = new HashMap<Integer, Map<Integer, Long>>();
            mapItemToRank = new HashMap<>();
            singleItemsNodes = new ArrayList<>();
            totalDBUtility_OD = 0;
        }
        k_Pre_Large_And_Large_Patterns = new PriorityQueue<>();
        minUtility_lower = 0;
        minUtility_upper = 0;

        leafPruneUtils = new PriorityQueue<Long>();
        startTimestamp = System.currentTimeMillis();
        writer = new BufferedWriter(new FileWriter(output));
        candidateCount = 0;
        BufferedReader myInput = null;
        String thisLine;
        huiCount = 0;
        List<UtilityList> newItemsUtilityLists = new ArrayList<UtilityList>();
        List<List<Pair>> newTrans = new ArrayList<>();
        try {
            int tid = 1;
            myInput = new BufferedReader(new InputStreamReader(new FileInputStream(new File(input))));
            while ((thisLine = myInput.readLine()) != null && tid <= lastLine) {
                if (tid >= firstLine) {
                    if (thisLine.isEmpty() == true || thisLine.charAt(0) == '#' || thisLine.charAt(0) == '%'
                            || thisLine.charAt(0) == '@') {
                        continue;
                    }
                    String split[] = thisLine.split(":");
                    String items[] = split[0].split(" ");
                    String utilityValues[] = split[2].split(" ");
                    int transactionUtility = Integer.parseInt(split[1]);
                    List<Pair> transaction = new ArrayList<>();
                    for (int i = 0; i < items.length; i++) {
                        Integer item = Integer.parseInt(items[i]);
                        int util = Integer.parseInt(utilityValues[i]);
                        Integer twu = mapItemToTWU.get(item);
                        Long sumUtil = mapItemToUtility.get(item);
                        Element element = new Element(tid, util, 0);
                        Pair pair = new Pair(item,util);
                        transaction.add(pair);
                        if (twu == null) {
                            twu = transactionUtility;
                            sumUtil = (long) util;
                            UtilityList newUL = new UtilityList(item);
                            newUL.addElement(element);
                            newItemsUtilityLists.add(newUL);
                            mapItemToUtilityList.put(item, newUL);
                        } else {
                            twu += transactionUtility;
                            sumUtil += util;
                            UtilityList uLItem = mapItemToUtilityList.get(item);
                            uLItem.addElement(element);
                            //mapItemToUtilityList.put(item, uLItem);
                        }
                        mapItemToTWU.put(item, twu);
                        mapItemToUtility.put(item, sumUtil);
                    }
                    totalDBUtility_ID += transactionUtility;
                    newTrans.add(transaction);
                }
                tid++;
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            if (myInput != null) {
                myInput.close();
            }
        }
        raisingThresholdByUtilityOfSingleItem(mapItemToUtility, upper_topkstatic,lower_topkstatic);

        newItemsUtilityLists.sort(new Comparator<UtilityList>() {
            public int compare(UtilityList o1, UtilityList o2) {
                return compareItems(o1.item, o2.item);
            }
        });
        for(UtilityList list : newItemsUtilityLists){
            mapItemToRank.put(list.item, mapItemToRank.size()+1);
        }
        ArrayList<UtilityList> listOfUtilityLists = new ArrayList<>();
        for(UtilityList list : mapItemToUtilityList.values()){
            listOfUtilityLists.add(list);
        }
        listOfUtilityLists.sort(new UtilComparator());
        for (List<Pair> revisedTransaction : newTrans) {
            Collections.sort(revisedTransaction, new PairComparator());
            for (int i = revisedTransaction.size() - 1; i >= 0; i--) {
                Pair pair = revisedTransaction.get(i);
                updateLeafprune(i, pair, revisedTransaction, listOfUtilityLists);
            }
        }
        raisingThresholdLeaf(listOfUtilityLists);
        leafPruneUtils = null;

        if(minUtility_upper<minUtility_upper_previous){
            minUtility_upper = minUtility_upper_previous;
        }
        if(minUtility_lower<minUtility_lower_previous){
            minUtility_lower = minUtility_lower_previous;
        }

        boolean condition_Rescan = totalDBUtility_ID>(minUtility_upper-minUtility_lower);
        System.out.println(totalDBUtility_ID);
        System.out.println(minUtility_upper-minUtility_lower);
        if(condition_Rescan||firstTime){
            System.out.println("Remine");
            List<UtilityList> listOfPromisingUtilityLists = new ArrayList<>();
            for (Entry<Integer, UtilityList> entry : mapItemToUtilityList.entrySet()) {
                if (mapItemToTWU.get(entry.getKey()) >= minUtility_lower) {
                    listOfPromisingUtilityLists.add(entry.getValue());
                }
            }
            Collections.sort(listOfPromisingUtilityLists, new UtilComparator());
            int arrayRu[] = new int[lastLine + 1];
            for (int i = listOfPromisingUtilityLists.size() - 1; i >= 0; i--) {
                UtilityList ul = listOfPromisingUtilityLists.get(i);
                int newRemain = 0;
                for (int j = 0; j < ul.elements.size(); j++) {
                    Element element = ul.elements.get(j);
                    element.rutils = arrayRu[element.tid];
                    arrayRu[element.tid] += element.iutils;
                    newRemain += element.rutils;
                }
                ul.sumRutils = newRemain;
            }
            checkMemory();
            thui(new int[0], null, listOfPromisingUtilityLists);
            singleItemsNodes = new ArrayList<>();
            while(k_Pre_Large_And_Large_Patterns.size()>0){
                PatternTHUI hui = k_Pre_Large_And_Large_Patterns.poll();
                if (k_Pre_Large_And_Large_Patterns.size()==(lower_top_k-1)){
                    minUtility_upper = hui.utility;
                }
                insertHUIinTrie(hui.prefix, hui.prefix.length, hui.item, hui.utility);
            }

            totalDBUtility_OD+=totalDBUtility_ID;
            totalDBUtility_ID =0;
            minUtility_upper_previous = minUtility_upper;
            minUtility_lower_previous = minUtility_lower;
            checkMemory();

            writeResultTofile();
            writer.close();

            endTimestamp = System.currentTimeMillis();
        }else{
            System.out.println("update");
            for(List<Pair> transaction:newTrans){
                UpdateTree(transaction);
            }
            checkMemory();
            //printTrie();
            InsertItemsetFromTreeToQueue(singleItemsNodes,new int[0]);
            minUtility_lower = k_Pre_Large_And_Large_Patterns.peek().utility;
            while(k_Pre_Large_And_Large_Patterns.size()>lower_top_k-1){
                k_Pre_Large_And_Large_Patterns.poll();
            }
            minUtility_upper = k_Pre_Large_And_Large_Patterns.peek().utility;
            minUtility_upper_previous = minUtility_upper;
            minUtility_lower_previous = minUtility_lower;
            endTimestamp = System.currentTimeMillis();
        }
        //kPatterns.clear();
    }
    public void InsertItemsetFromTreeToQueue(List<Node> list, int prefix[]) {
        for (Node node : list) {
            if (node.utility!=-1){
                PatternTHUI newPattern = new PatternTHUI(prefix,node.item,node.utility);
                k_Pre_Large_And_Large_Patterns.add(newPattern);
            }

            int newPrefix[] = new int[prefix.length+1];
            System.arraycopy(prefix, 0, newPrefix, 0, prefix.length);
            newPrefix[prefix.length] = node.item;
            // Make a recursive call to print childs of that node
            InsertItemsetFromTreeToQueue(node.childs, newPrefix);
        }
    }

//    public void updateEUCSprune(int i, Pair pair, List<Pair> revisedTransaction, long newTWU) {
//
//        Map<Integer, ItemTHUI> mapFMAPItem = mapFMAP.get(pair.item);
//        if (mapFMAPItem == null) {
//            mapFMAPItem = new HashMap<Integer, ItemTHUI>();
//            mapFMAP.put(pair.item, mapFMAPItem);
//        }
//        for (int j = i + 1; j < revisedTransaction.size(); j++) {
//            if (pair.item == revisedTransaction.get(j).item)
//                continue;// kosarak dataset has duplicate items
//            Pair pairAfter = revisedTransaction.get(j);
//            ItemTHUI twuItem = mapFMAPItem.get(pairAfter.item);
//            if (twuItem == null)
//                twuItem = new ItemTHUI();
//            twuItem.twu += newTWU;
//            twuItem.utility += (long) pair.utility + pairAfter.utility;
//            mapFMAPItem.put(pairAfter.item, twuItem);
//        }
//    }

    public void updateLeafprune(int i, Pair pair, List<Pair> revisedTransaction, List<UtilityList> ULs) {

        long cutil = (long) pair.utility;
        int followingItemIdx = getTWUindex(pair.item, ULs);
        Map<Integer, Long> mapLeafItem = mapLeafMAP.get(followingItemIdx);
        if (mapLeafItem == null) {
            mapLeafItem = new HashMap<Integer, Long>();
            mapLeafMAP.put(followingItemIdx, mapLeafItem);
        }
        for (int j = i - 1; j >= 0; j--) {
            if (pair.item == revisedTransaction.get(j).item)
                continue;// kosarak dataset has duplicate items
            Pair pairAfter = revisedTransaction.get(j);

            if (ULs.get(--followingItemIdx).item != pairAfter.item)
                break;
            Long twuItem = mapLeafItem.get(followingItemIdx);
            if (twuItem == null)
                twuItem = 0l;
            cutil += pairAfter.utility;
            twuItem += cutil;
            mapLeafItem.put(followingItemIdx, twuItem);
        }
    }

    public int getTWUindex(int item, List<UtilityList> ULs) {
        for (int i = ULs.size() - 1; i >= 0; i--)
            if (ULs.get(i).item == item)
                return i;
        return -1;
    }

    private int compareItems(int item1, int item2) {
        int compare = (int) (mapItemToTWU.get(item1) - mapItemToTWU.get(item2));
        return (compare == 0) ? item1 - item2 : compare;
    }

//    public void writeResultTofileUnord() throws IOException {
//
//        Iterator<PatternTHUI> iter = k_Pre_Large_And_Large_Patterns.iterator();
//        while (iter.hasNext()) {
//            huiCount++; // increase the number of high utility itemsets found
//            PatternTHUI pattern = (PatternTHUI) iter.next();
//            StringBuilder buffer = new StringBuilder();
//            buffer.append(pattern.prefix.toString());
//            // write separator
//            buffer.append(" #UTIL: ");
//            // write support
//            buffer.append(pattern.utility);
//            writer.write(buffer.toString());
//            writer.newLine();
//        }
//        writer.close();
//    }

    private void thui(int[] prefix, UtilityList pUL, List<UtilityList> ULs) throws IOException {

        for (int i = ULs.size() - 1; i >= 0; i--) {
            UtilityList X = ULs.get(i);
            long utilityOfX = X.sumIutils;
            if (X.getUtils() >= minUtility_lower){
                //insertHUIinTrie(prefix, prefixLength, X.item, utilityOfX);
                save(prefix, ULs.get(i));
            }
                //save(prefix, prefixLength, ULs.get(i));
        }

        for (int i = ULs.size() - 2; i >= 0; i--) {// last item is a single item, and hence no extension
            checkMemory();
            UtilityList X = ULs.get(i);
            if (X.sumIutils + X.sumRutils >= minUtility_lower && X.sumIutils > 0) {// the utility value of zero cases can be
                List<UtilityList> exULs = new ArrayList<UtilityList>();
                for (int j = i + 1; j < ULs.size(); j++) {
                    UtilityList Y = ULs.get(j);
                    candidateCount++;
                    UtilityList exul = construct(pUL, X, Y);
                    if (exul != null)
                        exULs.add(exul);

                }
                int newArray[] = new int[prefix.length+1];
                System.arraycopy(prefix, 0, newArray, 0, prefix.length);
                newArray[prefix.length] = X.item;
                thui(newArray, X, exULs);
            }
        }
    }

    public String getPrefixString(int[] prefix, int length) {
        String buffer = "";
        for (int i = 0; i < length; i++) {
            buffer += prefix[i];
            buffer += " ";
        }
        return buffer;
    }

    private UtilityList construct(UtilityList P, UtilityList px, UtilityList py) {
        UtilityList pxyUL = new UtilityList(py.item);
        long totUtil = px.sumIutils + px.sumRutils;
        int ei = 0, ej = 0, Pi = -1;

        Element ex = null, ey = null, e = null;
        while (ei < px.elements.size() && ej < py.elements.size()) {
            if (px.elements.get(ei).tid > py.elements.get(ej).tid) {
                ++ej;
                continue;
            } // px not present, py pres
            if (px.elements.get(ei).tid < py.elements.get(ej).tid) {// px present, py not present
                totUtil = totUtil - px.elements.get(ei).iutils - px.elements.get(ei).rutils;
                if (totUtil < minUtility_lower) {
                    return null;
                }
                ++ei;
                ++Pi;// if a parent is present, it should be as large or larger than px; besides the
                // ordering is by tid
                continue;
            }
            ex = px.elements.get(ei);
            ey = py.elements.get(ej);

            if (P == null) {
                pxyUL.addElement(new Element(ex.tid, ex.iutils + ey.iutils, ey.rutils));
            } else {
                while (Pi < P.elements.size() && P.elements.get(++Pi).tid < ex.tid)
                    ;
                e = P.elements.get(Pi);

                pxyUL.addElement(new Element(ex.tid, ex.iutils + ey.iutils - e.iutils, ey.rutils));
            }
            ++ei;
            ++ej;
        }
        while (ei < px.elements.size()) {
            totUtil = totUtil - px.elements.get(ei).iutils - px.elements.get(ei).rutils;
            if (totUtil < minUtility_lower) {
                return null;
            }
            ++ei;
        }
        return pxyUL;
    }

    public void writeResultTofile() throws IOException {

        if (k_Pre_Large_And_Large_Patterns.size() == 0)
            return;
        List<PatternTHUI> lp = new ArrayList<PatternTHUI>();
        do {
            huiCount++;
            PatternTHUI pattern = k_Pre_Large_And_Large_Patterns.poll();

            lp.add(pattern);
        } while (k_Pre_Large_And_Large_Patterns.size() > 0);

        Collections.sort(lp, new Comparator<PatternTHUI>() {
            public int compare(PatternTHUI o1, PatternTHUI o2) {
                return comparePatterns(o1, o2);
            }
        });

        for (PatternTHUI pattern : lp) {
            StringBuilder buffer = new StringBuilder();

            buffer.append(pattern.prefix.toString());
            buffer.append(" #UTIL: ");
            // write support
            buffer.append(pattern.utility);

            writer.write(buffer.toString());
            writer.newLine();
        }
        writer.close();
    }

    private int comparePatterns(PatternTHUI item1, PatternTHUI item2) {
        int i1 = item1.prefix.length==0?item1.item:item1.prefix[0];
        int i2 = item2.prefix.length==0?item2.item:item2.prefix[0];

        int compare = (int) (mapItemToTWU.get(i1) - mapItemToTWU.get(i2));
        return compare;
    }

    private int comparePatternsIdx(PatternTHUI item1, PatternTHUI item2) {
        int compare = item1.idx - item2.idx;
        return compare;
    }

    private double getObjectSize(Object object) throws IOException {
        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        ObjectOutputStream oos = new ObjectOutputStream(baos);
        oos.writeObject(object);
        oos.close();
        double maxMemory = baos.size() / 1024d / 1024d;
        return maxMemory;
    }

    public void raisingThresholdByUtilityOfSingleItem(Map<Integer, Long> map, int k_upper, int k_lower) {
        List<Entry<Integer, Long>> list = new LinkedList<Entry<Integer, Long>>(map.entrySet());

        Collections.sort(list, new Comparator<Entry<Integer, Long>>() {
            @Override
            public int compare(Entry<Integer, Long> value1, Entry<Integer, Long> value2) {
                return (value2.getValue()).compareTo(value1.getValue());
            }
        });

        if ((list.size() >= k_upper) && (k_upper > 0)) {
            minUtility_lower = list.get(k_upper - 1).getValue();
        }
        if ((list.size() >= k_lower) && (k_lower > 0)) {
            minUtility_upper = list.get(k_lower - 1).getValue();
        }
        list = null;
    }

//    public void raisingThresholdCUDOptimize(int k) {
//        PriorityQueue<Long> ktopls = new PriorityQueue<Long>();
//        long value = 0L;
//        for (Entry<Integer, Map<Integer, ItemTHUI>> entry : mapFMAP.entrySet()) {
//            for (Entry<Integer, ItemTHUI> entry2 : entry.getValue().entrySet()) {
//                value = entry2.getValue().utility;
//                if (value >= minUtility) {
//                    if (ktopls.size() < k)
//                        ktopls.add(value);
//                    else if (value > ktopls.peek()) {
//                        ktopls.add(value);
//                        do {
//                            ktopls.poll();
//                        } while (ktopls.size() > k);
//                    }
//                }
//            }
//        }
//        if ((ktopls.size() > k - 1) && (ktopls.peek() > minUtility))
//            minUtility = ktopls.peek();
//        ktopls.clear();
//    }

    public void addToLeafPruneUtils(long value) {
        if (leafPruneUtils.size() < upper_topkstatic)
            leafPruneUtils.add(value);
        else if (value > leafPruneUtils.peek()) {
            leafPruneUtils.add(value);
            do {
                leafPruneUtils.poll();
            } while (leafPruneUtils.size() > upper_topkstatic);
        }
    }

    public void raisingThresholdLeaf(List<UtilityList> ULs) {
        long value = 0L;
        // LIU-Exact
        for (Entry<Integer, Map<Integer, Long>> entry : mapLeafMAP.entrySet()) {
            for (Entry<Integer, Long> entry2 : entry.getValue().entrySet()) {
                value = entry2.getValue();
                if (value >= minUtility_lower) {
                    addToLeafPruneUtils(value);
                }
            }
        }

        // LIU-LB
        for (Entry<Integer, Map<Integer, Long>> entry : mapLeafMAP.entrySet()) {
            for (Entry<Integer, Long> entry2 : entry.getValue().entrySet()) {
                value = entry2.getValue();
                if (value >= minUtility_lower) {
                    int end = entry.getKey() + 1;// master contains the end reference 85 (leaf)
                    int st = entry2.getKey();// local map contains the start reference 76-85 (76 as parent)
                    long value2 = 0L;
                    // all entries between st and end processed, there will be go gaps in-between
                    // (only leaf with consecutive entries inserted in mapLeafMAP)

                    for (int i = st + 1; i < end - 1; i++) {// exclude the first and last e.g. 12345 -> 1345,1245,1235
                        // estimates
                        value2 = value - ULs.get(i).getUtils();
                        if (value2 >= minUtility_lower)
                            addToLeafPruneUtils(value2);
                        for (int j = i + 1; j < end - 1; j++) {
                            value2 = value - ULs.get(i).getUtils() - ULs.get(j).getUtils();
                            if (value2 >= minUtility_lower)
                                addToLeafPruneUtils(value2);
                            for (int k = j + 1; k + 1 < end - 1; k++) {
                                value2 = value - ULs.get(i).getUtils() - ULs.get(j).getUtils() - ULs.get(k).getUtils();
                                if (value2 >= minUtility_lower)
                                    addToLeafPruneUtils(value2);
                            }
                        }
                    }
                }
            }
        }
        for (UtilityList u : ULs) {// add all 1 items
            value = u.getUtils();
            if (value >= minUtility_lower)
                addToLeafPruneUtils(value);
        }
        if ((leafPruneUtils.size() > upper_topkstatic - 1) && (leafPruneUtils.peek() > minUtility_lower))
            minUtility_lower = leafPruneUtils.peek();
        do {
            leafPruneUtils.poll();
        } while (leafPruneUtils.size() > lower_topkstatic);
        minUtility_upper = leafPruneUtils.peek();

    }

//    private void removeEntry() {
//        for (Entry<Integer, Map<Integer, ItemTHUI>> entry : mapFMAP.entrySet()) {
//            for (Iterator<Entry<Integer, ItemTHUI>> it = entry.getValue().entrySet().iterator(); it.hasNext(); ) {
//                Entry<Integer, ItemTHUI> entry2 = it.next();
//                if (entry2.getValue().twu < minUtility) {
//                    it.remove();
//                }
//            }
//        }
//    }
//
//    private void removeLeafEntry() {
//        for (Entry<Integer, Map<Integer, Long>> entry : mapLeafMAP.entrySet()) {
//            for (Iterator<Entry<Integer, Long>> it = entry.getValue().entrySet().iterator(); it.hasNext(); ) {
//                Entry<Integer, Long> entry2 = it.next();
//                it.remove();
//            }
//        }
//    }

    private void save(int[] prefix, UtilityList X) {

        k_Pre_Large_And_Large_Patterns.add(new PatternTHUI(prefix, X, candidateCount));
        if (k_Pre_Large_And_Large_Patterns.size() > upper_topkstatic) {
            if (X.getUtils() >= minUtility_lower) {
                do {
                    k_Pre_Large_And_Large_Patterns.poll();
                } while (k_Pre_Large_And_Large_Patterns.size() > upper_topkstatic);
            }
            minUtility_lower = k_Pre_Large_And_Large_Patterns.peek().utility;
        }
    }

    private void checkMemory() {
        double currentMemory = (Runtime.getRuntime().totalMemory() - Runtime.getRuntime().freeMemory()) / 1024d / 1024d;
        if (currentMemory > maxMemory) {
            maxMemory = currentMemory;
        }
    }

    public void printStats() throws IOException {
        java.text.DecimalFormat df = new java.text.DecimalFormat("#.00");
        System.out.println("=============  THUI ALGORITHM - STATS =============");
        System.out.println(" Total time ~ " + (endTimestamp - startTimestamp) + " ms");
        System.out.println(" Memory ~ " + df.format(maxMemory) + " MB");
        System.out.println(" High-utility itemsets count : " + huiCount + " Candidates " + candidateCount);
        System.out.println(" Final minimum utility upper : " + minUtility_upper);
        System.out.println(" Final minimum utility lower : " + minUtility_lower);
        File f = new File(inputFile);
        String tmp = f.getName();
        tmp = tmp.substring(0, tmp.lastIndexOf('.'));
        System.out.println(" Dataset : " + tmp);
        String timeStamp = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(Calendar.getInstance().getTime());
        System.out.println(" End time " + timeStamp);
        System.out.println("===================================================");

    }

    /**
     * This is a helper method to count the number of HUIs stored in the HUI-trie structure.
     *
     * @param list a list of nodes to explore in a depth-first search way to count the HUIs.
     * @return the number of HUIs.
     */
    public Infor getRealHUICount(List<Node> list) {
        Infor info = new Infor();
        // for each node
        for (Node node : list) {
            // if it represents a HUI
            if (node.utility >= minUtility_upper) {
                // increase the count
                info.Large++;
            } else {
                if (node.utility >= minUtility_lower) {
                    info.Pre_lage++;
                }
            }
            // explore childs of that node
            info.Large += getRealHUICount(node.childs).Large;
            info.Pre_lage += getRealHUICount(node.childs).Pre_lage;
        }
        // return the total count
        return info;
    }

    /**
     * Print all HUIs stored in the trie to the console.
     */
    public void printHUIs() {
        // Make a recursive call to the helper method using childs of the root node.
        System.out.println("Large: ");
        print_Large_Itemset(singleItemsNodes, "");
        System.out.println("Pre_Large: ");
        print_Pre_Large_Itemset(singleItemsNodes, "");
    }

    /**
     * Recursive method to print all PreHUIs stored in the trie to the console.
     *
     * @param list   a list of nodes to explore in a depth-first search way
     * @param prefix the current prefix, which is the concatenation of all items in the current
     *               branch of the tree.
     */
    public void print_Pre_Large_Itemset(List<Node> list, String prefix) {
        for (Node node : list) {
            // append the item of that node to the prefix
            String itemset = prefix + " " + node.item;
            // if that node represents a high-utility itemset
            if (node.utility < minUtility_upper && node.utility >= minUtility_lower) {
                // print it to the console
                System.out.println(itemset + "  #UTIL: " + node.utility);
            }
            // Make a recursive call to print childs of that node
            print_Pre_Large_Itemset(node.childs, itemset);
        }
    }

    /**
     * Recursive method to print all HUIs stored in the trie to the console.
     *
     * @param list   a list of nodes to explore in a depth-first search way
     * @param prefix the current prefix, which is the concatenation of all items in the current
     *               branch of the tree.
     */
    public void print_Large_Itemset(List<Node> list, String prefix) {
        // for each node
        for (Node node : list) {
            // append the item of that node to the prefix
            String itemset = prefix + " " + node.item;
            // if that node represents a high-utility itemset
            if (node.utility >= minUtility_upper) {
                // print it to the console
                System.out.println(itemset + "  #UTIL: " + node.utility);
            }
            // Make a recursive call to print childs of that node
            print_Large_Itemset(node.childs, itemset);
        }
    }

    /**
     * Write HUIs found to a file. Note that this method write all HUIs found until now
     * and erase the file by doing so, if the file already exists.
     *
     * @param output the output file path
     * @throws IOException if error writing to output file
     */
    public void writeHUIsToFile(String output) throws IOException {
        // writer to write the output file
        BufferedWriter writer_Large = new BufferedWriter(new FileWriter(output + "_Large"));
        // Make a recursive call to the helper method using childs of the root node.
        writeLargesToFile(singleItemsNodes, "", writer_Large);
        // close the file
        writer_Large.close();
        BufferedWriter writer_Pre_Large = new BufferedWriter(new FileWriter(output + "_Pre_Large"));
        // Make a recursive call to the helper method using childs of the root node.
        writePreLargeIsToFile(singleItemsNodes, "", writer_Pre_Large);
        // close the file
        writer_Pre_Large.close();
    }

    /**
     * Helper method to Write HUIs found to a file (a recursive method)
     *
     * @param writer writer object to write HUIs to file
     * @param list   a list of nodes to explore in a depth-first search way
     * @param prefix the current prefix, which is the concatenation of all items in the current
     *               branch of the tree.
     * @throws IOException if error writing to output file
     */
    public void writeLargesToFile(List<Node> list, String prefix, BufferedWriter writer) throws IOException {

        // for each node
        for (Node node : list) {
            // append the item of that node to the prefix
            String itemset = prefix + " " + node.item;
            // if that node represents a high-utility itemset
            if (node.utility > minUtility_upper) {
                // save the itemset representing the current branch to file
                writer.write(itemset + "  #UTIL: " + node.utility + "\n");
            }
            // recursive call to extend this itemset
            writeLargesToFile(node.childs, itemset, writer);
        }
    }

    /**
     * Helper method to Write Pre HUIs found to a file (a recursive method)
     *
     * @param writer writer object to write HUIs to file
     * @param list   a list of nodes to explore in a depth-first search way
     * @param prefix the current prefix, which is the concatenation of all items in the current
     *               branch of the tree.
     * @throws IOException if error writing to output file
     */
    public void writePreLargeIsToFile(List<Node> list, String prefix, BufferedWriter writer) throws IOException {
        // for each node
        for (Node node : list) {
            // append the item of that node to the prefix
            String itemset = prefix + " " + node.item;
            // if that node represents a high-utility itemset
            if (node.utility < minUtility_upper && node.utility >= minUtility_lower) {
                // save the itemset representing the current branch to file
                writer.write(itemset + "  #UTIL: " + node.utility + "\n");
            }
            // recursive call to extend this itemset
            writePreLargeIsToFile(node.childs, itemset, writer);
        }
    }

    /**
     * Recursive method to print the trie to the console
     *
     * @param list   a list of nodes to explore in a depth-first search way
     * @param indent an indentation consisting of a set of tabulations to indent the branches of the
     *               tree in the console.
     */
    public void printTrie(List<Node> list, String indent) {
        // for each node
        for (Node node : list) {
            // append the item
            String itemset = indent + node.item;
            // print the item with its uility to the console
            System.out.println(itemset + "  (" + node.utility + ")");
            // recursively print all child nodes of that node.
            printTrie(node.childs, indent + "\t");
        }
    }

    /**
     * Insert a HUI in the trie.
     *
     * @param prefix       the prefix of the HUI
     * @param lastitem     the last item of the HUI
     * @param utility      the utility of the HUI
     * @param prefixLength The current prefix length
     */
    public void insertHUIinTrie(int prefix[], int prefixLength, int lastitem, long utility) {
        List<Node> listNodes = singleItemsNodes;
        Node currentNode = null;

        // if more than one item, first add all the prefix
        for (int i = 0; i < prefixLength; i++) {
            int item = prefix[i];
            // find the current item
            currentNode = binarySearchForItem(listNodes, item);
            // if not found
            if (currentNode == null) {
                currentNode = new Node(item);
                listNodes.add(middle, currentNode);
                listNodes = currentNode.childs;
            } else {
                listNodes = currentNode.childs;
            }
        }

        // Now the last item... find it!
        currentNode = binarySearchForItem(listNodes, lastitem);
        // if not found
        if (currentNode == null) {
            currentNode = new Node(lastitem, utility); // with utility
            listNodes.add(middle, currentNode);
            huiCount++;
        } else {
            // if found
            if (currentNode.utility == -1) {
                huiCount++;
            }
            currentNode.utility = utility;
        }
    }

    public boolean UpdateHUIinTrie(List<Integer> prefix, int lastitem, int utility) {
        List<Node> listNodes = singleItemsNodes;
        Node currentNode = null;

        // if more than one item, first add all the prefix
        for (int i = 0; i < prefix.size(); i++) {
            int item = prefix.get(i);
            currentNode = binarySearchForItem(listNodes, item);
            if (currentNode == null) {
                return false;
            } else {
                listNodes = currentNode.childs;
            }
        }
        // Now the last item... find it!
        currentNode = binarySearchForItem(listNodes, lastitem);
        // if not found
        if (currentNode == null) {
            return false;
        } else {
            if (currentNode.utility != -1) {
                currentNode.utility += utility;
                return true;
            }
            return false;
        }
    }

    public void UpdateTree(List<Pair> transaction) {
        List<Integer> current = new ArrayList<>();
        dfs(transaction, current, 0, 0, 0);
    }

    public void dfs(List<Pair> transaction, List<Integer> current, int index, int length, int accumulatedUtility) {
        if (length > 0) {
            List<Integer> prefix = current.subList(0, length - 1);
            int last = current.getLast();
            boolean update = UpdateHUIinTrie(prefix, last, accumulatedUtility);
            if (update) {
                //printTrie();
                //System.out.println("minU: " +accumulatedUtility);
            } else {
                return;
            }
//			if(UpdateHUIinTrie(prefix,last,accumulatedUtility)){
////				printTrie();
////				System.out.println("minU: " +accumulatedUtility);
//			};
        }
        for (int i = index; i < transaction.size(); i++) {
            int currentItem = transaction.get(i).item;
            current.add(currentItem);
            dfs(transaction, current, i + 1, length + 1, accumulatedUtility + transaction.get(i).utility);
            current.remove(current.size() - 1);
        }
    }

    // NOTE : This variable used by the binary search has been made global so that we can insert a new node
    // at the position where it should be in a list of nodes
    int middle = -1;

    public Node binarySearchForItem(List<Node> list, int item) {
        middle = 0;
        // perform a binary search to check if the item is here
        int first = 0;
        int last = list.size() - 1;

        // the binary search
        while (first <= last) {
            middle = (first + last) >>> 1; // divide by 2
            if (compareItemsByRank(item, list.get(middle).item) > 0) {
                first = middle + 1;
            } else if (compareItemsByRank(item, list.get(middle).item) < 0) {
                last = middle - 1;
            } else {
                return list.get(middle);
            }
        }
        middle = first;
        return null;
    }

    private int compareItemsByRank(int item1, int item2) {
        int compare = mapItemToRank.get(item1) - mapItemToRank.get(item2);
        return (compare == 0) ? item1 - item2 : compare;
    }

    public void printTrie() {
        System.out.println("==== trie ====");
        // call a recursive helper method to print the trie in a depth-first search way starting
        // with the childs of the root node.
        printTrie(singleItemsNodes, "");
    }


}
