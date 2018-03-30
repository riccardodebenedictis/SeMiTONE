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
package it.cnr.istc.pst.semitone.lra;

import static it.cnr.istc.pst.semitone.lra.Rational.NEGATIVE_INFINITY;
import static it.cnr.istc.pst.semitone.lra.Rational.POSITIVE_INFINITY;
import static it.cnr.istc.pst.semitone.sat.Sat.FALSE_var;
import static it.cnr.istc.pst.semitone.sat.Sat.TRUE_var;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.List;
import java.util.Optional;

import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;
import it.cnr.istc.pst.semitone.sat.Theory;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import it.unimi.dsi.fastutil.objects.ObjectOpenHashSet;

/**
 *
 * @author Riccardo De Benedictis
 */
public class LRATheory implements Theory {

    private static final int DEFAULT_INIT_SIZE = 16;
    final Sat sat;
    private int n_vars = 0;
    Bound[] bounds = new Bound[DEFAULT_INIT_SIZE << 1]; // the current bounds..
    private InfRational[] vals = new InfRational[DEFAULT_INIT_SIZE]; // the current values..
    AssertionList[] a_watches = new AssertionList[DEFAULT_INIT_SIZE]; // for each variable 'v', a list of assertions watching 'v'..
    RowSet[] t_watches = new RowSet[DEFAULT_INIT_SIZE]; // for each variable 'v', a list of tableau rows watching 'v'..
    private final Int2ObjectMap<Assertion> v_asrts = new Int2ObjectOpenHashMap<>(); // the assertions (propositional variable to assertion) used for enforcing (negating) assertions..
    private final Int2ObjectMap<Row> tableau = new Int2ObjectOpenHashMap<>(); // the sparse matrix..
    private final Object2IntMap<String> exprs = new Object2IntOpenHashMap<>(); // the already existing expressions (string to variable)..
    private final Deque<Int2ObjectMap<Bound>> layers = new ArrayDeque<>(); // we store the updated bounds..

    public LRATheory(final Sat sat) {
        this.sat = sat;
        sat.addTheory(this);
    }

    public int newVar() {
        final int id = n_vars++;
        ensureCapacity(id);
        vals[id] = new InfRational();
        bounds[id << 1] = new Bound(new InfRational(NEGATIVE_INFINITY), null);
        bounds[(id << 1) ^ 1] = new Bound(new InfRational(POSITIVE_INFINITY), null);
        a_watches[id] = new AssertionList();
        t_watches[id] = new RowSet();
        return id;
    }

    public int newVar(final Lin l) {
        return exprs.computeIntIfAbsent(l.toString(), s_xpr -> {
            final int slack = newVar();
            vals[slack] = value(l); // we set the initial value of the new slack variable..
            tableau.put(slack, new Row(this, slack, l)); // we add a new row into the tableau..
            return slack;
        });
    }

    public int newLt(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);
        for (int var : l_xpr.vars.keySet().toIntArray()) {
            Row row = tableau.get(var);
            if (row != null) {
                l_xpr.add(row.l.times(l_xpr.vars.remove(var)));
            }
        }

        final InfRational c_right = new InfRational(l_xpr.known_term.minus(), -1);
        l_xpr.known_term = new Rational();

        if (ub(l_xpr).lt(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (lb(l_xpr).geq(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        final int slack = newVar(l_xpr);
        return exprs.computeIntIfAbsent("x" + slack + " <= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_asrts.put(ctr, new Assertion(this, ctr, slack, Assertion.Op.LEq, c_right));
            return ctr;
        });
    }

    public int newLEq(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);
        for (int var : l_xpr.vars.keySet().toIntArray()) {
            Row row = tableau.get(var);
            if (row != null) {
                l_xpr.add(row.l.times(l_xpr.vars.remove(var)));
            }
        }

        final InfRational c_right = new InfRational(l_xpr.known_term.minus());
        l_xpr.known_term = new Rational();

        if (ub(l_xpr).leq(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (lb(l_xpr).gt(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        final int slack = newVar(l_xpr);
        return exprs.computeIntIfAbsent("x" + slack + " <= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_asrts.put(ctr, new Assertion(this, ctr, slack, Assertion.Op.LEq, c_right));
            return ctr;
        });
    }

    public int newEq(final Lin left, final Lin right) {
        return sat.newConj(new Lit(newLEq(left, right)), new Lit(newGEq(left, right)));
    }

    public int newGEq(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);
        for (int var : l_xpr.vars.keySet().toIntArray()) {
            Row row = tableau.get(var);
            if (row != null) {
                l_xpr.add(row.l.times(l_xpr.vars.remove(var)));
            }
        }

        final InfRational c_right = new InfRational(l_xpr.known_term.minus());
        l_xpr.known_term = new Rational();

        if (lb(l_xpr).geq(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (ub(l_xpr).lt(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        final int slack = newVar(l_xpr);
        return exprs.computeIntIfAbsent("x" + slack + " >= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_asrts.put(ctr, new Assertion(this, ctr, slack, Assertion.Op.GEq, c_right));
            return ctr;
        });
    }

    public int newGt(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);
        for (int var : l_xpr.vars.keySet().toIntArray()) {
            Row row = tableau.get(var);
            if (row != null) {
                l_xpr.add(row.l.times(l_xpr.vars.remove(var)));
            }
        }

        final InfRational c_right = new InfRational(l_xpr.known_term.minus(), 1);
        l_xpr.known_term = new Rational();

        if (lb(l_xpr).gt(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (ub(l_xpr).leq(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        final int slack = newVar(l_xpr);
        return exprs.computeIntIfAbsent("x" + slack + " >= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_asrts.put(ctr, new Assertion(this, ctr, slack, Assertion.Op.GEq, c_right));
            return ctr;
        });
    }

    /**
     * Returns the current lower bound of variable 'v'.
     *
     * @param v the variable whose lower bound we are interested in.
     * @return the lower bound of variable 'v'.
     */
    public InfRational lb(final int v) {
        return bounds[lb_index(v)].value;
    }

    /**
     * Returns the current upper bound of variable 'v'.
     *
     * @param v the variable whose upper bound we are interested in.
     * @return the upper bound of variable 'v'.
     */
    public InfRational ub(final int v) {
        return bounds[ub_index(v)].value;
    }

    /**
     * Returns the current value of variable 'v'.
     *
     * @param v the variable whose value we are interested in.
     * @return the value of variable 'v'.
     */
    public InfRational value(final int v) {
        return new InfRational(vals[v].rat, vals[v].inf);
    }

    /**
     * Returns the current lower bound of linear expression 'l'.
     *
     * @param l the linear expression whose lower bound we are interested in.
     * @return the lower bound of linear expression 'l'.
     */
    public InfRational lb(final Lin l) {
        InfRational v = new InfRational(l.known_term);
        for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
            v.add((term.getValue().isPositive() ? lb(term.getIntKey()) : ub(term.getIntKey())).times(term.getValue()));
        }
        return v;
    }

    /**
     * Returns the current upper bound of linear expression 'l'.
     *
     * @param l the linear expression whose upper bound we are interested in.
     * @return the upper bound of linear expression 'l'.
     */
    public InfRational ub(final Lin l) {
        InfRational v = new InfRational(l.known_term);
        for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
            v.add((term.getValue().isPositive() ? ub(term.getIntKey()) : lb(term.getIntKey())).times(term.getValue()));
        }
        return v;
    }

    /**
     * Returns the current value of linear expression 'l'.
     *
     * @param l the linear expression whose value we are interested in.
     * @return the value of linear expression 'l'.
     */
    public InfRational value(final Lin l) {
        InfRational v = new InfRational(l.known_term);
        for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
            v.add(value(term.getIntKey()).times(term.getValue()));
        }
        return v;
    }

    @Override
    public boolean propagate(final Lit p, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        Assertion a = v_asrts.get(p.v);
        switch (a.op) {
        case LEq:
            return p.sign ? assert_upper(a.x, a.v, p, cnfl) : assert_lower(a.x, a.v, p, cnfl);
        case GEq:
            return p.sign ? assert_lower(a.x, a.v, p, cnfl) : assert_upper(a.x, a.v, p, cnfl);
        default:
            throw new AssertionError(a.op.name());
        }
    }

    @Override
    public boolean check(final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        while (true) {
            // we find a basic variable whose value is outside its bounds..
            Optional<Int2ObjectMap.Entry<Row>> x_i = tableau.int2ObjectEntrySet().stream()
                    .filter(row -> value(row.getIntKey()).lt(lb(row.getIntKey()))
                            || value(row.getIntKey()).gt(ub(row.getIntKey())))
                    .findFirst();
            if (!x_i.isPresent()) {
                return true;
            }
            if (value(x_i.get().getIntKey()).lt(lb(x_i.get().getIntKey()))) {
                // the current value is lower than the lower bound..
                Optional<Int2ObjectMap.Entry<Rational>> x_j = x_i.get().getValue().l.vars.int2ObjectEntrySet().stream()
                        .filter(term -> (term.getValue().isPositive()
                                && value(term.getIntKey()).lt(ub(term.getIntKey())))
                                || (term.getValue().isNegative() && value(term.getIntKey()).gt(lb(term.getIntKey()))))
                        .findFirst();
                if (x_j.isPresent()) {
                    // var x_j can be used to increase the value of x_i..
                    pivot_and_update(x_i.get().getIntKey(), x_j.get().getIntKey(),
                            new InfRational(lb(x_i.get().getIntKey())));
                } else {
                    // we generate an explanation for the conflict..
                    for (Int2ObjectMap.Entry<Rational> term : x_i.get().getValue().l.vars.int2ObjectEntrySet()) {
                        if (term.getValue().isPositive()) {
                            cnfl.add(bounds[ub_index(term.getIntKey())].reason.not());
                        } else if (term.getValue().isNegative()) {
                            cnfl.add(bounds[lb_index(term.getIntKey())].reason.not());
                        }
                    }
                    cnfl.add(bounds[lb_index(x_i.get().getIntKey())].reason.not());
                    return false;
                }
            }
            if (value(x_i.get().getIntKey()).gt(ub(x_i.get().getIntKey()))) {
                // the current value is greater than the upper bound..
                Optional<Int2ObjectMap.Entry<Rational>> x_j = x_i.get().getValue().l.vars.int2ObjectEntrySet().stream()
                        .filter(term -> (term.getValue().isNegative()
                                && value(term.getIntKey()).lt(ub(term.getIntKey())))
                                || (term.getValue().isPositive() && value(term.getIntKey()).gt(lb(term.getIntKey()))))
                        .findFirst();
                if (x_j.isPresent()) {
                    // var x_j can be used to decrease the value of x_i..
                    pivot_and_update(x_i.get().getIntKey(), x_j.get().getIntKey(),
                            new InfRational(ub(x_i.get().getIntKey())));
                } else {
                    // we generate an explanation for the conflict..
                    for (Int2ObjectMap.Entry<Rational> term : x_i.get().getValue().l.vars.int2ObjectEntrySet()) {
                        if (term.getValue().isPositive()) {
                            cnfl.add(bounds[lb_index(term.getIntKey())].reason.not());
                        } else if (term.getValue().isNegative()) {
                            cnfl.add(bounds[ub_index(term.getIntKey())].reason.not());
                        }
                    }
                    cnfl.add(bounds[ub_index(x_i.get().getIntKey())].reason.not());
                    return false;
                }
            }
        }
    }

    @Override
    public void push() {
        layers.addFirst(new Int2ObjectOpenHashMap<>());
    }

    @Override
    public void pop() {
        // we restore the variables' bounds and their reason..
        for (Int2ObjectMap.Entry<Bound> bound : layers.pollFirst().int2ObjectEntrySet()) {
            bounds[bound.getIntKey()] = bound.getValue();
        }
    }

    private boolean assert_lower(final int x_i, final InfRational val, final Lit p, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        if (val.leq(lb(x_i))) {
            return true;
        } else if (val.gt(ub(x_i))) {
            cnfl.add(p.not()); // either the literal 'p' is false ..
            cnfl.add(bounds[ub_index(x_i)].reason.not()); // or what asserted the upper bound is false..
            return false;
        } else {
            if (!layers.isEmpty() && !layers.peekFirst().containsKey(lb_index(x_i))) {
                layers.peekFirst().put(lb_index(x_i), new Bound(lb(x_i), bounds[lb_index(x_i)].reason));
            }
            bounds[lb_index(x_i)] = new Bound(val, p);

            if (vals[x_i].lt(val) && !tableau.containsKey(x_i)) {
                update(x_i, val);
            }

            // unate propagation..
            for (Assertion c : a_watches[x_i]) {
                if (!c.propagate_lb(x_i, cnfl)) {
                    return false;
                }
            }
            // bound propagation..
            for (Row c : t_watches[x_i]) {
                if (!c.propagate_lb(x_i, cnfl)) {
                    return false;
                }
            }

            return true;
        }
    }

    private boolean assert_upper(final int x_i, final InfRational val, final Lit p, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        if (val.geq(ub(x_i))) {
            return true;
        } else if (val.lt(lb(x_i))) {
            cnfl.add(p.not()); // either the literal 'p' is false ..
            cnfl.add(bounds[lb_index(x_i)].reason.not()); // or what asserted the lower bound is false..
            return false;
        } else {
            if (!layers.isEmpty() && !layers.peekFirst().containsKey(ub_index(x_i))) {
                layers.peekFirst().put(ub_index(x_i), new Bound(ub(x_i), bounds[ub_index(x_i)].reason));
            }
            bounds[ub_index(x_i)] = new Bound(val, p);

            if (vals[x_i].gt(val) && !tableau.containsKey(x_i)) {
                update(x_i, val);
            }

            // unate propagation..
            for (Assertion c : a_watches[x_i]) {
                if (!c.propagate_ub(x_i, cnfl)) {
                    return false;
                }
            }
            // bound propagation..
            for (Row c : t_watches[x_i]) {
                if (!c.propagate_ub(x_i, cnfl)) {
                    return false;
                }
            }

            return true;
        }
    }

    private void update(final int x_i, final InfRational v) {
        assert !tableau.containsKey(x_i) : "x_i should be a non-basic variable..";
        for (Row row : t_watches[x_i]) {
            // x_j = x_j + a_ji(v - x_i)..
            vals[row.x].add(v.minus(vals[x_i]).times(row.l.vars.get(x_i)));
        }
        // x_i = v..
        vals[x_i] = new InfRational(v);
    }

    private void pivot_and_update(final int x_i, final int x_j, final InfRational v) {
        assert tableau.containsKey(x_i) : "x_i should be a basic variable..";
        assert !tableau.containsKey(x_j) : "x_j should be a non-basic variable..";
        assert tableau.get(x_i).l.vars.containsKey(x_j);

        final InfRational theta = v.minus(vals[x_i]).divide(tableau.get(x_i).l.vars.get(x_j));
        assert !theta.rat.isInfinite();

        // x_i = v
        vals[x_i] = new InfRational(v);

        // x_j += theta
        vals[x_j].add(theta);
        for (Row row : t_watches[x_j]) {
            if (row.x != x_i) {
                // x_k += a_kj * theta..
                vals[row.x].add(theta.times(row.l.vars.get(x_j)));
            }
        }

        pivot(x_i, x_j);
    }

    private void pivot(final int x_i, final int x_j) {
        // the exiting row..
        Row row = tableau.remove(x_i);
        for (Int2ObjectMap.Entry<Rational> term : row.l.vars.int2ObjectEntrySet()) {
            t_watches[term.getIntKey()].remove(row);
        }

        final Lin xpr = row.l;
        final Rational c = xpr.vars.remove(x_j);
        xpr.div(c.minus());
        xpr.vars.put(x_i, new Rational(1).divide(c));

        for (Row r : t_watches[x_j].toArray(new Row[t_watches[x_j].size()])) {
            for (Int2ObjectMap.Entry<Rational> term : row.l.vars.int2ObjectEntrySet()) {
                t_watches[term.getIntKey()].remove(r);
            }
            r.l.add(xpr.times(r.l.vars.remove(x_j)));
            for (Int2ObjectMap.Entry<Rational> term : row.l.vars.int2ObjectEntrySet()) {
                t_watches[term.getIntKey()].add(r);
            }
        }

        // we add a new row into the tableau..
        tableau.put(x_j, new Row(this, x_j, xpr));
    }

    private void ensureCapacity(final int minCapacity) {
        int capacity = vals.length;
        while (minCapacity > capacity) {
            capacity = (capacity * 3) / 2 + 1;
            if (minCapacity < capacity) {
                Bound[] c_bounds = new Bound[capacity << 1];
                System.arraycopy(bounds, 0, c_bounds, 0, bounds.length);
                bounds = c_bounds;

                InfRational[] c_vals = new InfRational[capacity];
                System.arraycopy(vals, 0, c_vals, 0, vals.length);
                vals = c_vals;

                AssertionList[] c_assertions = new AssertionList[capacity];
                System.arraycopy(a_watches, 0, c_assertions, 0, a_watches.length);
                a_watches = c_assertions;

                RowSet[] c_rows = new RowSet[capacity];
                System.arraycopy(t_watches, 0, c_rows, 0, t_watches.length);
                t_watches = c_rows;
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < vals.length; i++) {
            sb.append("x").append(i).append(": [").append(bounds[lb_index(i)].value).append(", ")
                    .append(bounds[ub_index(i)].value).append("] ").append(vals[i]).append('\n');
        }
        return sb.toString();
    }

    static int lb_index(final int v) {
        return v << 1;
    }

    static int ub_index(final int v) {
        return (v << 1) ^ 1;
    }

    /**
     * Represents a bound of a variable and the reason for its existence.
     */
    static class Bound {

        final InfRational value; // the value of the bound..
        final Lit reason; // the reason for the value..

        private Bound(InfRational value, Lit reason) {
            this.value = new InfRational(value);
            this.reason = reason;
        }
    }

    static class AssertionList extends ObjectArrayList<Assertion> {
    }

    static class RowSet extends ObjectOpenHashSet<Row> {
    }
}
