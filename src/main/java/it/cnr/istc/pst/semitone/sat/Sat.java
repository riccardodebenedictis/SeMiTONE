/*
 * Copyright (C) 2018 Riccardo De Benedictis
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
package it.cnr.istc.pst.semitone.sat;

import static it.cnr.istc.pst.semitone.sat.LBool.False;
import static it.cnr.istc.pst.semitone.sat.LBool.True;
import static it.cnr.istc.pst.semitone.sat.LBool.Undefined;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.ints.IntArrayList;
import it.unimi.dsi.fastutil.ints.IntOpenHashSet;
import it.unimi.dsi.fastutil.ints.IntSet;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 *
 * @author Riccardo De Benedictis
 */
public class Sat {

    public static final int FALSE_var = 0;
    public static final int TRUE_var = 1;
    private static final int DEFAULT_INIT_SIZE = 16;
    private int n_vars = 0;
    private final List<Clause> clauses = new ArrayList<>(); // collection of problem constraints..
    private LBool[] assigns = new LBool[DEFAULT_INIT_SIZE]; // the current assignments..
    ClauseList[] watches = new ClauseList[DEFAULT_INIT_SIZE << 1]; // for each literal 'p', a list of constraints watching 'p'..
    private Clause[] reason = new Clause[DEFAULT_INIT_SIZE]; // for each variable, the constraint that implied its value..
    private int[] level = new int[DEFAULT_INIT_SIZE]; // for each variable, the decision level it was assigned..
    private final Deque<Lit> trail = new ArrayDeque<>(); // the list of assignment in chronological order..
    private final IntArrayList trail_lim = new IntArrayList(); // separator indices for different decision levels in 'trail'..
    private final Deque<Lit> prop_q = new ArrayDeque<>(); // propagation queue..
    private final Collection<Theory> theories = new ArrayList<>();
    private final Int2ObjectMap<Collection<Theory>> binds = new Int2ObjectOpenHashMap<>();
    private final Object2IntMap<String> exprs = new Object2IntOpenHashMap<>(); // the already existing expressions (string to bool variable)..

    public Sat() {
        int c_false = newVar();
        int c_true = newVar();
        assert c_false == FALSE_var;
        assert c_true == TRUE_var;
        assigns[FALSE_var] = False;
        assigns[TRUE_var] = True;
    }

    public int newVar() {
        final int id = n_vars++;
        ensureCapacity(id);
        assigns[id] = Undefined;
        watches[id << 1] = new ClauseList();
        watches[(id << 1) ^ 1] = new ClauseList();
        level[id] = -1;
        reason[id] = null;
        return id;
    }

    public boolean newClause(final Lit... lits) {
        final List<Lit> c_lits = new ArrayList<>();
        for (Lit lit : lits) {
            switch (value(lit)) {
            case True:
                return true; // the clause is already satisfied..
            case Undefined:
                boolean found = false;
                for (Lit c_lit : c_lits) {
                    if (c_lit.v == lit.v) {
                        if (c_lit.sign == lit.sign) {
                            found = true;
                            break;
                        } else {
                            return true; // the clause represents a tautology..
                        }
                    }
                }
                if (!found) {
                    c_lits.add(lit);
                }
                break;
            }
        }
        switch (c_lits.size()) {
        case 0:
            return false;
        case 1:
            return enqueue(c_lits.get(0), null);
        default:
            clauses.add(new Clause(this, c_lits.toArray(new Lit[c_lits.size()])));
            return true;
        }
    }

    public int newEq(final Lit l, final Lit r) {
        assert rootLevel();
        if (l == r) {
            return TRUE_var;
        }
        if (l.v > r.v) {
            return newEq(r, l);
        }
        return exprs.computeIntIfAbsent((l.sign ? "b" : "!b") + l.v + " == " + (r.sign ? "b" : "!b") + r.v, s_xpr -> {
            final int e = newVar();
            boolean nc;
            nc = newClause(new Lit(e, false), l.not(), r);
            assert nc;
            nc = newClause(new Lit(e, false), l, r.not());
            assert nc;
            nc = newClause(new Lit(e), l.not(), r.not());
            assert nc;
            return e;
        });
    }

    public int newConj(final Lit... ls) {
        assert rootLevel();
        Arrays.sort(ls, (Lit l0, Lit l1) -> Integer.compare(l0.v, l1.v));
        return exprs.computeIntIfAbsent(Stream.of(ls).map(l -> l.toString()).collect(Collectors.joining(" & ")),
                s_xpr -> {
                    int cnj = newVar();
                    Lit[] c_lits = new Lit[ls.length + 1];
                    c_lits[0] = new Lit(cnj);
                    boolean nc;
                    for (int i = 1; i < c_lits.length; i++) {
                        nc = newClause(new Lit(cnj, false), ls[i - 1]);
                        assert nc;
                        c_lits[i] = ls[i - 1].not();
                    }
                    nc = newClause(c_lits);
                    assert nc;
                    return cnj;
                });
    }

    public int newDisj(final Lit... ls) {
        assert rootLevel();
        Arrays.sort(ls, (Lit l0, Lit l1) -> Integer.compare(l0.v, l1.v));
        return exprs.computeIntIfAbsent(Stream.of(ls).map(l -> l.toString()).collect(Collectors.joining(" | ")),
                s_xpr -> {
                    int dsj = newVar();
                    Lit[] c_lits = new Lit[ls.length + 1];
                    c_lits[0] = new Lit(dsj, false);
                    boolean nc;
                    for (int i = 1; i < c_lits.length; i++) {
                        nc = newClause(ls[i - 1].not(), new Lit(dsj));
                        assert nc;
                        c_lits[i] = ls[i - 1];
                    }
                    nc = newClause(c_lits);
                    assert nc;
                    return dsj;
                });
    }

    public int newExctOne(final Lit... ls) {
        assert rootLevel();
        Arrays.sort(ls, (Lit l0, Lit l1) -> Integer.compare(l0.v, l1.v));
        return exprs.computeIntIfAbsent(Stream.of(ls).map(l -> l.toString()).collect(Collectors.joining(" ^ ")),
                s_xpr -> {
                    int eo = newVar();
                    Lit[] c_lits = new Lit[ls.length + 1];
                    c_lits[0] = new Lit(eo, false);
                    boolean nc;
                    for (int i = 1; i < c_lits.length; i++) {
                        for (int j = i + 1; j < c_lits.length; j++) {
                            nc = newClause(ls[i - 1].not(), ls[j - 1].not(), c_lits[0]);
                            assert nc;
                        }
                        c_lits[i] = ls[i - 1];
                    }
                    nc = newClause(c_lits);
                    assert nc;
                    return eo;
                });
    }

    public LBool value(final int x) {
        return assigns[x];
    }

    public LBool value(final Lit p) {
        switch (value(p.v)) {
        case False:
            return p.sign ? False : True;
        case True:
            return p.sign ? True : False;
        case Undefined:
            return Undefined;
        default:
            throw new AssertionError(value(p.v).name());
        }
    }

    /**
     * Returns the current decision level.
     *
     * @return the current decision level.
     */
    public int decisionLevel() {
        return trail_lim.size();
    }

    /**
     * Checks whether this decision level is root level.
     *
     * @return whether this decision level is root level.
     */
    public boolean rootLevel() {
        return trail_lim.isEmpty();
    }

    public boolean assume(final Lit p) {
        trail_lim.push(trail.size());
        for (Theory th : theories) {
            th.push();
        }
        return enqueue(p, null);
    }

    public void pop() {
        while (trail_lim.peekInt(0) < trail.size()) {
            popOne();
        }
        trail_lim.popInt();
        for (Theory th : theories) {
            th.pop();
        }
    }

    public boolean check() {
        final List<Lit> cnfl = new ArrayList<>();
        while (true) {
            if (!propagate(cnfl)) {
                if (rootLevel()) {
                    return false;
                }
                List<Lit> no_good = new ArrayList<>();
                // we analyze the conflict..
                int bt_level = analyze(cnfl, no_good);
                while (decisionLevel() > bt_level) {
                    pop();
                }
                // we record the no-good..
                record(no_good.toArray(new Lit[no_good.size()]));
                cnfl.clear();
            } else {
                return true;
            }
        }
    }

    public boolean check(final Lit... ls) {
        int c_level = decisionLevel();
        final List<Lit> cnfl = new ArrayList<>();
        for (Lit l : ls) {
            // notice that these literals can be modified by propagation..
            if (!assume(l) || !propagate(cnfl)) {
                while (decisionLevel() > c_level) {
                    pop();
                }
                return false;
            }
        }
        while (decisionLevel() > c_level) {
            pop();
        }
        return true;
    }

    private int analyze(final List<Lit> cnfl, final List<Lit> no_good) {
        assert cnfl.stream().allMatch(l -> value(l) != Undefined); // all these literals must have been assigned for belonging to a conflict..
        final IntSet seen = new IntOpenHashSet();
        int counter = 0; // this is the number of variables of the current decision level that have already been seen..
        Lit p = new Lit(-1);
        List<Lit> p_reason = cnfl;
        no_good.add(p);
        int bt_level = 0; // the backtracking level..
        do {
            // trace reason for 'p'..
            for (Lit q : p_reason) { // the order in which these literals are visited is not relevant..
                if (seen.add(q.v)) {
                    assert value(q) == False; // this literal should have propagated the clause..
                    if (level[q.v] == decisionLevel()) {
                        counter++;
                    } else if (level[q.v] > 0) { // exclude variables from decision level 0..
                        no_good.add(q); // this literal has been assigned in a previous decision level..
                        bt_level = Math.max(bt_level, level[q.v]);
                    }
                }
            }
            // select next literal to look at..
            do {
                p = trail.peekFirst();
                assert level[p.v] == decisionLevel(); // this variable must have been assigned at the current decision level..
                if (reason[p.v] != null) // 'p' can be the asserting literal..
                {
                    assert reason[p.v].lits[0].equals(p); // a consequence of propagating the clause is the assignment of literal 'p'..
                    assert value(p) == True; // 'p' has been propagated as true..
                    assert Stream.of(reason[p.v].lits).skip(1).allMatch(l -> value(l) == False); // all these literals must have been assigned as false for propagating 'p'..
                    p_reason = Stream.of(reason[p.v].lits).skip(1).collect(Collectors.toList());
                }
                popOne();
            } while (!seen.contains(p.v));
            counter--;
        } while (counter > 0);
        // 'p' is now the first Unique Implication Point (UIP), possibly the asserting literal, that led to the conflict..
        assert value(p) == Undefined;
        assert no_good.stream().skip(1).allMatch(l -> value(l) == False); // all these literals must have been assigned as false for propagating 'p'..
        no_good.set(0, p.not());
        return bt_level;
    }

    public void record(final Lit... lits) {
        assert value(lits[0]) == Undefined;
        assert Stream.of(lits).noneMatch(l -> value(l) == True);
        assert Stream.of(lits).filter(l -> value(l) == Undefined).count() == 1;
        assert Stream.of(lits).filter(l -> value(l) == False).count() == lits.length - 1;
        if (lits.length == 1) {
            assert rootLevel();
            boolean e = enqueue(lits[0], null);
            assert e;
        } else {
            // we sort literals according to descending order of variable assignment (except for the first literal which is now unassigned)..
            Arrays.sort(lits, 1, lits.length - 1, (Lit l0, Lit l1) -> -Integer.compare(level[l0.v], level[l1.v]));
            Clause c = new Clause(this, lits);
            boolean e = enqueue(lits[0], c);
            assert e;
            clauses.add(c);
        }
    }

    private boolean propagate(final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        while (!prop_q.isEmpty()) {
            // we propagate sat constraints..
            Lit p = prop_q.pollFirst();
            final List<Clause> tmp = watches[index(p)];
            watches[index(p)] = new ClauseList();
            for (int i = 0; i < tmp.size(); i++) {
                final Clause cl = tmp.get(i);
                if (!cl.propagate(p)) {
                    // constraint is conflicting..
                    for (int j = i + 1; j < tmp.size(); j++) {
                        watches[index(p)].add(tmp.get(j));
                    }
                    assert Stream.of(cl.lits).filter(l -> watches[index(l.not())].contains(cl)).count() == 2;
                    cnfl.addAll(Arrays.asList(cl.lits));
                    prop_q.clear();
                    return false;
                }
                assert Stream.of(cl.lits).filter(l -> watches[index(l.not())].contains(cl)).count() == 2;
            }

            // we perform theory propagation..
            Collection<Theory> ths = binds.get(p.v);
            if (ths != null) {
                for (Theory th : ths) {
                    if (!th.propagate(p, cnfl)) {
                        assert !cnfl.isEmpty();
                        prop_q.clear();
                        return false;
                    }
                }
            }
        }

        // we check the theories..
        for (Theory th : theories) {
            if (!th.check(cnfl)) {
                assert !cnfl.isEmpty();
                return false;
            }
        }

        return true;
    }

    boolean enqueue(final Lit p, final Clause c) {
        switch (value(p)) {
        case False:
            return false;
        case True:
            return true;
        case Undefined:
            assigns[p.v] = p.sign ? True : False;
            level[p.v] = decisionLevel();
            reason[p.v] = c;
            trail.addFirst(p);
            prop_q.addLast(p);
            return true;
        default:
            throw new AssertionError(value(p).name());
        }
    }

    public void popOne() {
        int v = trail.pollFirst().v;
        assigns[v] = Undefined;
        reason[v] = null;
        level[v] = -1;
    }

    public void addTheory(final Theory th) {
        theories.add(th);
    }

    public void bind(final int v, final Theory th) {
        Collection<Theory> ths = binds.get(v);
        if (ths == null) {
            ths = new ArrayList<>();
            binds.put(v, ths);
        }
        ths.add(th);
    }

    public void unbind(final int v, final Theory th) {
        Collection<Theory> ths = binds.get(v);
        ths.remove(th);
        if (ths.isEmpty()) {
            binds.remove(v);
        }
    }

    private void ensureCapacity(final int minCapacity) {
        int capacity = assigns.length;
        while (minCapacity > capacity) {
            capacity = (capacity * 3) / 2 + 1;
            if (minCapacity < capacity) {
                LBool[] c_assigns = new LBool[capacity];
                System.arraycopy(assigns, 0, c_assigns, 0, assigns.length);
                assigns = c_assigns;

                ClauseList[] c_watches = new ClauseList[capacity << 1];
                System.arraycopy(watches, 0, c_watches, 0, watches.length);
                watches = c_watches;

                Clause[] c_reason = new Clause[capacity];
                System.arraycopy(reason, 0, c_reason, 0, reason.length);
                reason = c_reason;

                int[] c_level = new int[capacity];
                System.arraycopy(level, 0, c_level, 0, level.length);
                level = c_level;
            }
        }
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n_vars; i++) {
            sb.append("b").append(i).append(": ");
            if (level[i] != -1) {
                sb.append("(").append(level[i]).append(")");
            }
            sb.append(assigns[i]).append('\n');
        }
        for (Clause c : clauses) {
            sb.append(c.toString()).append('\n');
        }
        return sb.toString();
    }

    static int index(final Lit p) {
        return p.sign ? p.v << 1 : (p.v << 1) ^ 1;
    }

    static class ClauseList extends ObjectArrayList<Clause> {
    }
}
