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
import verification.FiniteGames;
import verification.FiniteStateSets;
import verification.InductivenessChecking;
import verification.SubsetChecking;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

public class MailSafetyGameTeacher extends SafetyGameTeacher {

    public static final Logger LOGGER = LogManager.getLogger();
    protected FiniteGames finiteStates;
    private FiniteStateSets finiteStateSets;
    private boolean tryMinimalInvariant = true;

    public MailSafetyGameTeacher(int numLetters, Automata I, Automata B, Automata v_0, Automata v_1, EdgeWeightedDigraph T) {
        super(numLetters,I,B,v_0,v_1,T);
        finiteStates = new FiniteGames(v_0,v_1, I, T, B);

    }

    private void debug(Supplier<String> msg) {
        if (LOGGER.isDebugEnabled()) {
            LOGGER.debug(msg.get());
        }
    }

    public void setLearnMinimalInvariant(boolean trymin) {
        tryMinimalInvariant = trymin;
    }

    public boolean isAccepted(List<Integer> word)
            throws Timer.TimeoutException {
        Timer.tick();
        LOGGER.debug("Check if word" + NoInvariantException.getLabeledWord(word) + " is reachable:");
        boolean isReachable = finiteStates.isReachable(word);
        LOGGER.debug("Word is reachable?: " + isReachable);
        // TODO exclude or include if it is not reachable?
        if (isReachable){
            boolean isBad = finiteStates.isBadReachable(word);
            LOGGER.debug("Is "+ NoInvariantException.getLabeledWord(word) + " bad? " + isBad);
            String labeledWord = LOGGER.isDebugEnabled() ?
                    NoInvariantException.getLabeledWord(word) : null;

            if (isBad) {
                boolean isP1reachable = finiteStates.isReachableP1(word);
                if(isP1reachable) {
                    LOGGER.debug("membership query P1: " + labeledWord + " is P1 reachable and bad");
                    throw new NoInvariantException(word, getInitialStates(), getTransition());
                }
                else {
                    LOGGER.debug(labeledWord + " is reachable from P0 but not P1 and P1 can reach a bad state -> do not include in target language");
                    return false;
                }
            }
            else{
                LOGGER.debug(" P1 cannot reach a bad state from the word " + labeledWord + " and it is reachable by either P0 or P1");
                return true;
            }
        }
        else{
            return false;
        }
    }

    public boolean isCorrectLanguage(Automata hyp, CounterExample cex)
            throws Timer.TimeoutException {
        LOGGER.debug("found hypothesis, size " + hyp.getStates().length);
        LOGGER.debug(hyp.prettyPrint("candidate invariant:", NoInvariantException.getIndexToLabelMapping()));
        LOGGER.debug(DOTPrinter.getString(hyp, NoInvariantException.getIndexToLabelMapping()));
        if (LOGGER.isDebugEnabled()) {
            LOGGER.debug("found hypothesis, size " + hyp.getStates().length);
            LOGGER.debug(hyp.prettyPrint("candidate invariant:", NoInvariantException.getIndexToLabelMapping()));
            LOGGER.debug(DOTPrinter.getString(hyp, NoInvariantException.getIndexToLabelMapping()));
        }
        Timer.tick();
        List<Integer> ex;

        // first test: are initial states contained?
        ex = initialCheck(hyp,getInitialStates());
        LOGGER.debug(getInitialStates().prettyPrint("\n--------------\nConstruct Initial states", NoInvariantException.getIndexToLabelMapping()) + "\n---------------------\n");

        Timer.tick();
        if (ex != null) {
            if (LOGGER.isDebugEnabled()) {
                String word = NoInvariantException.getLabeledWord(ex);
                LOGGER.debug("Line 89: An initial configuration is not contained in hypothesis: " + word);
            }
            boolean reachBad = finiteStates.isBadReachable(ex);

            if (reachBad) {
                String word = NoInvariantException.getLabeledWord(ex);
                if (LOGGER.isDebugEnabled()) {
                    LOGGER.debug("Line 95: Initial state is contained in bad: " + word + " ");
                }
                throw new NoInvariantException(ex, getInitialStates(), getTransition());
            }
            cex.addPositive(ex);
            LOGGER.debug(" Add positive cex: " + NoInvariantException.getLabeledWord(ex));
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

        // player 0 test: is the invariant inductive?
        List<Automata> player0_successors = new LinkedList<>();
        Tuple<List<Integer>> xy = player0_closedness(hyp,player0_successors);
        Timer.tick();
        if (xy != null) {
            String x = null, y = null;
            if (LOGGER.isDebugEnabled()) {
                LOGGER.debug("Hypothesis is not inductive: ");
                x = NoInvariantException.getLabeledWord(xy.x);
                y = NoInvariantException.getLabeledWord(xy.y);
                LOGGER.debug(x + " => " + y);
            }
            boolean isReachable = finiteStates.isReachable(xy.x);
            if (!isReachable){
                LOGGER.debug("* Configuration " + x + " should be excluded from the hypothesis.");
                cex.addNegative(xy.x);
                return false;
            }
            else {
                List<List<Integer>> all_successors = AutomataUtility.getWords(player0_successors.get(0),xy.x.size());
                for (List<Integer> word : all_successors){
                    boolean addNegative = finiteStates.isBadReachable(word);
                    if (!addNegative) {
                        LOGGER.debug("* Configuration " + y + " should be included in the hypothesis.");
                        cex.addPositive(word);
                        return false;
                    } else {
                        LOGGER.debug("* Need to look for other successors");
                    }
                }
                LOGGER.debug("* Configuration " + x + " should be excluded in the hypothesis.");
                cex.addNegative(xy.x);
                return false;
            }
        }

        // player 1 test: is the invariant inductive? TODO: return more than one cex?
        xy = player1_closedness(hyp);
        Timer.tick();
        if (xy != null) {
            String x = null, y = null;
            if (LOGGER.isDebugEnabled()) {
                LOGGER.debug("Hypothesis is not inductive: ");
                x = NoInvariantException.getLabeledWord(xy.x);
                y = NoInvariantException.getLabeledWord(xy.y);
                LOGGER.debug(x + " => " + y);
            }
            boolean isReachable = finiteStates.isReachable(xy.x);
            if (!isReachable){
                LOGGER.debug("* Configuration " + x + " should be excluded in the hypothesis.");
                cex.addNegative(xy.x);
            }else{
                boolean addPositive = finiteStates.isBadReachable(xy.y);
                if (!addPositive) {
                    LOGGER.debug("* Configuration " + y + " should be included in the hypothesis.");
                    cex.addPositive(xy.y);
                } else {
                    LOGGER.debug("* Configuration " + x + " should be excluded from the hypothesis.");
                    cex.addNegative(xy.x);
                }
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
        Automata b = AutomataUtility.getIntersection(hypothesis, badStates);
        return b.findAcceptingString();

    }

    /**
     * Inductive check for Player 0 in safety games. Checks if the hypothesis Automaton h is closed
     * under Player 0 transitions.
     *
     * @return A tuple of List of Integer (x,y) where x is the Player 0 vertex that violates the property
     * and y is one of it's successors.
     */

    private Tuple<List<Integer>> player0_closedness(Automata hypothesis, List<Automata> player0_successors){
        // b_1 contains all vertices that have a successor in hypothesis
        Automata b_1 = VerificationUtility.getPreImage(getTransition(), hypothesis);
        // b_2 contains all vertices of player 0 that have no successor in hypothesis
        Automata b_2 = AutomataUtility.getDifference(getPlayer0_vertices(), hypothesis);
        // b_3 contains contains all vertices of player 0 belonging to the hypothesis that have no successor in hypothesis
        Automata b_3 = AutomataUtility.getIntersection(b_2,hypothesis);
        List<Integer> u = b_3.findAcceptingString();
        if (u == null){
            return null;
        }
        Automata successors_of_u = VerificationUtility.getImage(u,getTransition(),getNumLetters());
        player0_successors.add(successors_of_u);
        List<Integer> one_successor = successors_of_u.findAcceptingString();
        return new Tuple<>(u, one_successor);
    }

    /**
     * Inductive check for Player 1 in safety games. Checks if the hypothesis Automaton h is closed under
     * Player 1 transitions.
     *
     * @return A tuple of List of Integer (x,y) where x is the Player 1 vertex that violates the property
     * and y is one of it's successors.
     */

    private Tuple<List<Integer>> player1_closedness(Automata hypothesis){
        // b_1 contains all vertices not in b_1
        Automata b_1 = AutomataUtility.getDifference(AutomataUtility.getUnion(getPlayer0_vertices(),getPlayer1_vertices()), hypothesis);
        // b_2 contains all vertices that have a successor not belonging to hypothesis
        Automata b_2 = VerificationUtility.getPreImage(getTransition(), b_1);
        // b_3 contains all vertices of player 1 in hypothesis with at least on successor not in hypothesis
        Automata b_3 = AutomataUtility.getIntersection(AutomataUtility.getIntersection(getPlayer1_vertices(),hypothesis),b_2);
        List<Integer> u = b_3.findAcceptingString();
        if (u == null){
            return null;
        }
        // TODO maybe save successors or return multiple ones instead of redoing computation
        Automata successor_of_u = AutomataUtility.getDifference(VerificationUtility.getImage(u,getTransition(),getNumLetters()), hypothesis);
        // TODO maybe problem with termination if the same successor gets picked out again?
        List<Integer> one_successor = successor_of_u.findAcceptingString();
        return new Tuple<>(u,one_successor);
    }
}