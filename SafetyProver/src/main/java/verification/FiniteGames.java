package verification;

import common.Timer;
import common.VerificationUtility;
import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;
import common.finiteautomata.AutomataUtility;
import learning.NoInvariantException;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import java.util.*;

public class FiniteGames {
    private static final Logger LOGGER = LogManager.getLogger();
    private final Automata v_0,v_1, B;
    private final EdgeWeightedDigraph T;
    private final Map<Integer, Set<List<Integer>>> reachableStates =
            new HashMap<Integer, Set<List<Integer>>>();
    private final Map<Integer, Automata> reachableStateAutomata =
            new HashMap<Integer, Automata>();

    public FiniteGames(Automata v_0, Automata v_1, EdgeWeightedDigraph T, Automata B) {
        this.v_0 = v_0;
        this.v_1 = v_1;
        this.T = T;
        this.B = B;
    }

    public Automata getAttractor_player0(int wordLen)
            throws common.Timer.TimeoutException {
        Automata marked = reachableStateAutomata.get(wordLen);
        if (marked == null) {
            LOGGER.debug("computing automaton describing reachable configurations of length " + wordLen);

            Map<List<Integer>,Integer> v1_markings = new HashMap<>();
            //TODO might need a copy method, this just copies the reference...
            marked = AutomataUtility.getWordAutomaton(B, wordLen);
            Automata marked_prev = null;
            // TODO equals method for automata might be required... or just intersection and emptiness check? or save set of
            // TODO marked vertices and compare sets, test Automata_equality if problems happen here
            while(Automata_equality(marked,marked_prev)){
                marked_prev = marked;
                Automata predecessors = VerificationUtility.getPreImage(T,marked);
                Automata predecessors_v1 = AutomataUtility.getIntersection(predecessors, v_1);
                Automata predecessors_v0 = AutomataUtility.getIntersection(predecessors,v_0);
                List<List<Integer>> v1_predecessor_vertices = AutomataUtility.getWords(predecessors_v1, wordLen);
                for(List<Integer> v : v1_predecessor_vertices){
                    if(v1_markings.containsKey(v)){
                        int n = v1_markings.get(v);
                        if (n-1 == 0){
                            v1_markings.remove(v);
                            marked = AutomataUtility.getUnion(marked, produceWordAutomaton(v, marked.getNumLabels()));
                        }
                        else{
                            v1_markings.put(v,n-1);
                        }
                    }
                    else{
                        Automata image_v = VerificationUtility.getImage(v,T,marked.getNumLabels());
                        int n = AutomataUtility.getWords(image_v,wordLen).size();
                        v1_markings.put(v,n);
                    }
                }
                marked = AutomataUtility.getUnion(marked, predecessors_v0);
            }

            reachableStateAutomata.put(wordLen, marked);
            return marked;
        }
        return marked;
    }

    public boolean isReachable(List<Integer> word)
            throws Timer.TimeoutException {
        return getAttractor_player0(word.size()).accepts(word);
    }
    private Automata produceWordAutomaton(List<Integer> word, int numLetters){
        Automata result = new Automata(0,word.size()+1,numLetters);
        for(int i = 0; i< word.size(); i++) {
            result.addTrans(i, word.get(i), i + 1);
        }
        Set<Integer> acceptings = new HashSet<Integer>();
        acceptings.add(word.size());
        result.setAcceptingStateIds(acceptings);
        return result;
    }

    private Automata concatenate(Automata a, Automata b){return null;}
    private boolean Automata_equality(Automata a, Automata b){
        if (a == null || b == null){
            return false;
        }
        return (AutomataUtility.getIntersection(a,AutomataUtility.getComplement(b)).findAcceptingString() == null);
    }
}
