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

import java.util.List;
import java.util.function.Supplier;

public class BasicSafetyGameTeacher extends SafetyGameTeacher {

    public static final Logger LOGGER = LogManager.getLogger();
    protected FiniteStateSets finiteStates;
    private boolean tryMinimalInvariant = true;

    public BasicSafetyGameTeacher(int numLetters, Automata I, Automata B, Automata v_0, Automata v_1, EdgeWeightedDigraph T) {
        super(numLetters,v_0,v_1, I, B, T);
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

    /** Initial Check for safety games. Checks if the hypothesis Automaton h is contained in the
     * initial Automaton i.
     *
     * @return List<Integer> example which is a positive counterexample if the check fails or null if the check succeeds
     */
    private List<Integer> initialCheck(Automata hypothesis, Automata init){
        Automata b = AutomataUtility.getDifference(init,hypothesis);
        return b.findAcceptingString();
    }

    /**
     * Bad Check for safety games. Checks if the hypothesis Automaton h intersected with the bad state
     * Automaton bad is empty.
     *
     * @return List of Integer which is a negative counterexample if the check fails or null if the check succeeds.
     */

    private List<Integer> badCheck(Automata hypothesis, Automata badStates){
        Automata b = AutomataUtility.getDifference(hypothesis, badStates);
        return b.findAcceptingString();

    }

    /**
     * Inductive check for Player 0 in safety games. Checks if the hypothesis Automaton h is closed
     * under Player 0 transitions.
     *
     * @return A tuple of List of Integer (x,y) where x is the Player 0 vertex that violates the property
     * and y is one of it's successors.
     */

    private Tuple<List<Integer>> player0_closedness(){
        return null;
    }

    /**
     * Inductive check for Player 1 in safety games. Checks if the hypothesis Automaton h is closed under
     * Player 1 transitions.
     *
     * @return A tuple of List of Integer (x,y) where x is the Player 1 vertex that violates the property
     * and y is one of it's successors.
     */

    private Tuple<List<Integer>> player1_closedness(){
        return null;

    }
}
