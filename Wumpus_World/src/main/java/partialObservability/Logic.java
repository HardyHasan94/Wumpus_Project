package partialObservability;
import org.tweetyproject.logics.pl.reasoner.SatReasoner;
import org.tweetyproject.logics.pl.reasoner.SimplePlReasoner;
import org.tweetyproject.logics.pl.sat.Sat4jSolver;
import org.tweetyproject.logics.pl.sat.SatSolver;
import wumpus.Agent;

import org.tweetyproject.logics.pl.syntax.*;

import java.util.Arrays;
import java.util.Hashtable;
import java.util.LinkedList;

public class Logic{
    public static Proposition constructProp(String s, int col, int row){
        String p = s + "_[" + col + ", " + row + "]";
        return new Proposition(p);
    }
    public static Proposition constructPropArray(String s, int[] arr){
        String p = s + "_" + Arrays.toString(arr);
        return new Proposition(p);
    }
    public static boolean in(LinkedList<int[]> l, int[] obj){
        for(int[] el: l){
            if(Arrays.equals(obj, el)){
                return true;
            }
        }
        return false;
    }
    public static void main(String[] args){

        PlBeliefSet KB = new PlBeliefSet();
        SimplePlReasoner reasoner = new SimplePlReasoner();
        SatReasoner sat = new SatReasoner();
        SatSolver.setDefaultSolver(new Sat4jSolver());

        Proposition R1 = new Proposition("B_00");
        KB.add(new Negation(R1));
        Disjunction d = new Disjunction();
        d.add(new Proposition("P_01"), new Proposition("P_10"));
        KB.add(new Equivalence(R1, d).toCnf());
        KB.add(new Negation(new Proposition("P_00")));
        System.out.println(KB);
        System.out.println(sat.query(KB, new Proposition("P_02")));
        System.out.println(reasoner.query(KB, new Proposition("P_02")));



    }
}