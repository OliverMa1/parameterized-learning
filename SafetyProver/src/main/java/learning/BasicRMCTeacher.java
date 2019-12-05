package learning;

import common.DOTPrinter;
import common.Timer;
import common.Tuple;
import common.VerificationUtility;
import common.bellmanford.EdgeWeightedDigraph;
import common.finiteautomata.Automata;
import common.finiteautomata.AutomataUtility;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import verification.FiniteStateSets;
import verification.InductivenessChecking;
import verification.SubsetChecking;

import java.util.*;
import java.util.function.Supplier;

public class BasicRMCTeacher extends RMCTeacher {

    public static final Logger LOGGER = LogManager.getLogger();
    protected FiniteStateSets finiteStates;
    private boolean tryMinimalInvariant = true;

    public BasicRMCTeacher(int numLetters, Automata I, Automata B, EdgeWeightedDigraph T) {
        super(numLetters, I, B, T);
        finiteStates = new FiniteStateSets(I, T, B);
    }

    private void debug(Supplier<String> msg) {
        if (LOGGER.isDebugEnabled()) {
            LOGGER.debug(msg.get());
        }
    }

    public void setLearnMinimalInvariant(boolean trymin) {
        tryMinimalInvariant = trymin;
    }

    private boolean canReachBadStatesFrom(List<Integer> word) {
        return VerificationUtility.
                findSomeTrace(word, getBadStates(), getTransition()) != null;
    }

    public boolean isAccepted(List<Integer> word)
            throws Timer.TimeoutException {
        Timer.tick();
        boolean isReachable = finiteStates.isReachable(word);
        boolean isBad = tryMinimalInvariant ?
                getBadStates().accepts(word) : canReachBadStatesFrom(word);

        String labeledWord = LOGGER.isDebugEnabled() ?
                NoInvariantException.getLabeledWord(word) : null;

        if (isReachable && isBad) {
            LOGGER.debug("membership query: " + labeledWord);
            throw new NoInvariantException(word, getInitialStates(), getTransition());
        }

        boolean accepted = tryMinimalInvariant ? isReachable : !isBad;
        LOGGER.debug("membership query: " + labeledWord + " -> " + (accepted ? "accepted" : "rejected"));
        Timer.tick();
        return accepted;
    }

    public boolean isCorrectLanguage(Automata hyp, CounterExample cex)
            throws Timer.TimeoutException {
        if (LOGGER.isDebugEnabled()) {
            LOGGER.debug("found hypothesis, size " + hyp.getStates().length);
            LOGGER.debug(hyp.prettyPrint("candidate invariant:", NoInvariantException.getIndexToLabelMapping()));
            LOGGER.debug(DOTPrinter.getString(hyp, NoInvariantException.getIndexToLabelMapping()));
        }
        Timer.tick();
        List<Integer> ex;

        // first test: are initial states contained?
        ex = new SubsetChecking(getInitialStates(), hyp).check();
        Timer.tick();
        if (ex != null) {
            if (LOGGER.isDebugEnabled()) {
                String word = NoInvariantException.getLabeledWord(ex);
                LOGGER.debug("An initial configuration is not contained in hypothesis: " + word);
            }
            cex.addPositive(ex);
            return false;
        }

        // second test: are bad configurations excluded?
        Automata lang = AutomataUtility.getIntersection(hyp, getBadStates());
        ex = AutomataUtility.findSomeShortestWord(lang);
        Timer.tick();
        if (ex != null) {
            if (LOGGER.isDebugEnabled()) {
                String word = NoInvariantException.getLabeledWord(ex);
                LOGGER.debug("A bad configuration is contained in hypothesis: " + word);
            }
            cex.addNegative(ex);
            return false;
        }
        /*
        // third test: are concrete unreachable configurations excluded?
        for (int l = 0; l <= explicitExplorationDepth; ++l) {
            sc = new SubsetChecking(
                    AutomataConverter.getWordAutomaton(hyp, l),
                    finiteStates.getReachableStateAutomaton(l));
            cex = sc.check();
            Timer.tick();
            if (cex != null) {
                LOGGER.debug("An unreachable configuration is contained in hypothesis: " + cex);
                negCEX.add(cex);
                return false;
            }
        }
        */
        // fourth test: is the invariant inductive?
        InductivenessChecking ic = new InductivenessChecking(hyp, getTransition(), getNumLetters());
        Tuple<List<Integer>> xy = ic.check();
        Timer.tick();
        if (xy != null) {
            String x = null, y = null;
            if (LOGGER.isDebugEnabled()) {
                LOGGER.debug("Hypothesis is not inductive: ");
                x = NoInvariantException.getLabeledWord(xy.x);
                y = NoInvariantException.getLabeledWord(xy.y);
                LOGGER.debug(x + " => " + y);
            }
            boolean addPositive = tryMinimalInvariant ?
                    finiteStates.isReachable(xy.x) : !canReachBadStatesFrom(xy.y);
            if (addPositive) {
                LOGGER.debug("* Configuration " + y + " should be included in the hypothesis.");
                cex.addPositive(xy.y);
            } else {
                LOGGER.debug("* Configuration " + x + " should be excluded from the hypothesis.");
                cex.addNegative(xy.x);
            }
            return false;
        }
        return true;
    }

    // TODO move methods to the right places, finiteautomata/verification utility

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
        return (AutomataUtility.getIntersection(a,AutomataUtility.getComplement(b)).findAcceptingString() == null);
    }
    private Automata attractor_player0(Automata v_0, Automata v_1, Automata reach, EdgeWeightedDigraph T, int wordlength){
        Map<List<Integer>,Integer> v1_markings = new HashMap<>();
        //TODO might need a copy method, this just copies the reference...
        Automata marked = reach;
        Automata marked_prev = null;
        // TODO equals method for automata might be required... or just intersection and emptiness check? or save set of
        // TODO marked vertices and compare sets, test Automata_equality if problems happen here
        while(marked.equals(marked_prev)){
            marked_prev = marked;
            Automata predecessors = VerificationUtility.getPreImage(T,marked);
            Automata predecessors_v1 = AutomataUtility.getIntersection(predecessors, v_1);
            Automata predecessors_v0 = AutomataUtility.getIntersection(predecessors,v_0);
            List<List<Integer>> v1_predecessor_vertices = AutomataUtility.getWords(predecessors_v1, wordlength);
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
                    int n = AutomataUtility.getWords(image_v,wordlength).size();
                    v1_markings.put(v,n);
                }
            }
            marked = AutomataUtility.getUnion(marked, predecessors_v0);
        }

        return marked;
    }
}
