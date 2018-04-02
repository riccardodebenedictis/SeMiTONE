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
package it.cnr.istc.pst.semitone.pb;

import static it.cnr.istc.pst.semitone.sat.Sat.FALSE_var;
import static it.cnr.istc.pst.semitone.sat.Sat.TRUE_var;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.List;

import it.cnr.istc.pst.semitone.lra.InfRational;
import it.cnr.istc.pst.semitone.lra.Lin;
import it.cnr.istc.pst.semitone.lra.Rational;
import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;
import it.cnr.istc.pst.semitone.sat.Theory;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap.Entry;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import it.unimi.dsi.fastutil.objects.Object2ObjectMap;
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import it.unimi.dsi.fastutil.objects.ObjectOpenHashSet;

/**
 *
 * @author Riccardo De Benedictis
 */
public class PBTheory implements Theory {

    private final Sat sat;
    private final Int2ObjectMap<Collection<PBConstraint>> c_watches = new Int2ObjectOpenHashMap<>(); // for each variable 'v', a list of pseudo-boolean constraints watching 'v'..
    private final Int2ObjectMap<PBConstraint> v_cnstrs = new Int2ObjectOpenHashMap<>(); // the pseudo-boolean constraints (propositional variable to constraint) used for enforcing (negating) constraints..
    private final Object2IntMap<String> exprs = new Object2IntOpenHashMap<>(); // the already existing expressions (string to variable)..
    private final Deque<Layer> layers = new ArrayDeque<>(); // we store the updated bounds..

    public PBTheory(Sat sat) {
        this.sat = sat;
        sat.addTheory(this);
    }

    public int newLt(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus(), -1);
        l_xpr.known_term = new Rational();

        Rational lb = lb(l_xpr);
        Rational ub = ub(l_xpr);
        if (c_right.geq(ub)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (c_right.lt(lb)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " <= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(ctr, l_xpr, lb, ub, Op.LEq, c_right));
            return ctr;
        });
    }

    public int newLEq(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus());
        l_xpr.known_term = new Rational();

        Rational lb = lb(l_xpr);
        Rational ub = ub(l_xpr);
        if (c_right.gt(ub)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (c_right.leq(lb)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " <= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(ctr, l_xpr, lb, ub, Op.LEq, c_right));
            return ctr;
        });
    }

    public int newEq(final Lin left, final Lin right) {
        return sat.newConj(new Lit(newLEq(left, right)), new Lit(newGEq(left, right)));
    }

    public int newGEq(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus());
        l_xpr.known_term = new Rational();

        Rational lb = lb(l_xpr);
        Rational ub = ub(l_xpr);
        if (c_right.lt(ub)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (c_right.geq(lb)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " >= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(ctr, l_xpr, lb, ub, Op.GEq, c_right));
            return ctr;
        });
    }

    public int newGt(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus(), 1);
        l_xpr.known_term = new Rational();

        Rational lb = lb(l_xpr);
        Rational ub = ub(l_xpr);
        if (c_right.leq(ub)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (c_right.gt(lb)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " >= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(ctr, l_xpr, lb, ub, Op.GEq, c_right));
            return ctr;
        });
    }

    /**
     * Returns the current lower bound of linear expression 'l'.
     *
     * @param l the linear expression whose lower bound we are interested in.
     * @return the lower bound of linear expression 'l'.
     */
    public Rational lb(final Lin l) {
        Rational v = new Rational(l.known_term);
        for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
            if (term.getValue().isPositive()) {
                switch (sat.value(term.getIntKey())) {
                case True:
                    v.add(term.getValue());
                }
            } else {
                switch (sat.value(term.getIntKey())) {
                case True:
                case Undefined:
                    v.add(term.getValue());
                }
            }
        }
        return v;
    }

    /**
     * Returns the current upper bound of linear expression 'l'.
     *
     * @param l the linear expression whose upper bound we are interested in.
     * @return the upper bound of linear expression 'l'.
     */
    public Rational ub(final Lin l) {
        Rational v = new Rational(l.known_term);
        for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
            if (term.getValue().isPositive()) {
                switch (sat.value(term.getIntKey())) {
                case True:
                case Undefined:
                    v.add(term.getValue());
                }
            } else {
                switch (sat.value(term.getIntKey())) {
                case True:
                    v.add(term.getValue());
                }
            }
        }
        return v;
    }

    @Override
    public boolean propagate(final Lit p, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        for (PBConstraint c : c_watches.get(p.v)) {
            // we update the bounds..
            Rational cnst = c.expr.vars.get(p.v);
            if (cnst.isPositive()) {
                if (p.sign) {
                    if (!layers.isEmpty()) {
                        layers.peekFirst().lbs.computeIfAbsent(c, k -> cnst);
                    }
                    // we increase the lower bound..
                    c.lb.add(cnst);
                } else {
                    if (!layers.isEmpty()) {
                        layers.peekFirst().ubs.computeIfAbsent(c, k -> cnst);
                    }
                    // we decrease the upper bound..
                    c.ub.sub(cnst);
                }
            } else {
                if (p.sign) {
                    if (!layers.isEmpty()) {
                        layers.peekFirst().ubs.computeIfAbsent(c, k -> cnst);
                    }
                    // we decrease the upper bound..
                    c.ub.add(cnst);
                } else {
                    if (!layers.isEmpty()) {
                        layers.peekFirst().lbs.computeIfAbsent(c, k -> cnst);
                    }
                    // we increase the lower bound..
                    c.lb.sub(cnst);
                }
            }

            switch (c.op) {
            case LEq:
                switch (sat.value(c.b)) {
                case False:
                    break;
                case True:
                    break;
                case Undefined:
                    if (c.known_term.gt(c.ub)) {
                        // the constraint is already satisfied..
                        final List<Lit> learnt_clause = new ObjectArrayList<>();
                        learnt_clause.add(new Lit(c.b));
                        for (Int2ObjectMap.Entry<Rational> term : c.expr.vars.int2ObjectEntrySet()) {
                            switch (sat.value(term.getIntKey())) {
                            case False:
                                learnt_clause.add(new Lit(term.getIntKey()));
                                break;
                            case True:
                                learnt_clause.add(new Lit(term.getIntKey(), false));
                                break;
                            }
                        }
                        sat.record(learnt_clause.toArray(new Lit[learnt_clause.size()]));
                        for (Entry<Rational> var : c.expr.vars.int2ObjectEntrySet()) {
                            c_watches.get(var.getIntKey()).remove(c);
                            if (!layers.isEmpty()) {
                                layers.peekFirst().cnstrs.add(c);
                            }
                            if (c_watches.get(var.getIntKey()).isEmpty()) {
                                c_watches.remove(var.getIntKey());
                            }
                        }
                    } else if (c.known_term.leq(c.lb)) {
                        // the constraint cannot be satisfied..
                        final List<Lit> learnt_clause = new ObjectArrayList<>();
                        learnt_clause.add(new Lit(c.b, false));
                        for (Int2ObjectMap.Entry<Rational> term : c.expr.vars.int2ObjectEntrySet()) {
                            switch (sat.value(term.getIntKey())) {
                            case False:
                                learnt_clause.add(new Lit(term.getIntKey()));
                                break;
                            case True:
                                learnt_clause.add(new Lit(term.getIntKey(), false));
                                break;
                            }
                        }
                        sat.record(learnt_clause.toArray(new Lit[learnt_clause.size()]));
                        for (Entry<Rational> var : c.expr.vars.int2ObjectEntrySet()) {
                            c_watches.get(var.getIntKey()).remove(c);
                            if (!layers.isEmpty()) {
                                layers.peekFirst().cnstrs.add(c);
                            }
                            if (c_watches.get(var.getIntKey()).isEmpty()) {
                                c_watches.remove(var.getIntKey());
                            }
                        }
                    }
                    break;
                }
                break;
            case GEq:
                switch (sat.value(c.b)) {
                case False:
                    break;
                case True:
                    break;
                case Undefined:
                    if (c.known_term.lt(c.lb)) {
                        // the constraint cannot be satisfied..
                        final List<Lit> learnt_clause = new ObjectArrayList<>();
                        learnt_clause.add(new Lit(c.b, false));
                        for (Int2ObjectMap.Entry<Rational> term : c.expr.vars.int2ObjectEntrySet()) {
                            switch (sat.value(term.getIntKey())) {
                            case False:
                                learnt_clause.add(new Lit(term.getIntKey()));
                                break;
                            case True:
                                learnt_clause.add(new Lit(term.getIntKey(), false));
                                break;
                            }
                        }
                        sat.record(learnt_clause.toArray(new Lit[learnt_clause.size()]));
                        for (Entry<Rational> var : c.expr.vars.int2ObjectEntrySet()) {
                            c_watches.get(var.getIntKey()).remove(c);
                            if (!layers.isEmpty()) {
                                layers.peekFirst().cnstrs.add(c);
                            }
                            if (c_watches.get(var.getIntKey()).isEmpty()) {
                                c_watches.remove(var.getIntKey());
                            }
                        }
                    } else if (c.known_term.geq(c.ub)) {
                        // the constraint is already satisfied..
                        final List<Lit> learnt_clause = new ObjectArrayList<>();
                        learnt_clause.add(new Lit(c.b));
                        for (Int2ObjectMap.Entry<Rational> term : c.expr.vars.int2ObjectEntrySet()) {
                            switch (sat.value(term.getIntKey())) {
                            case False:
                                learnt_clause.add(new Lit(term.getIntKey()));
                                break;
                            case True:
                                learnt_clause.add(new Lit(term.getIntKey(), false));
                                break;
                            }
                        }
                        sat.record(learnt_clause.toArray(new Lit[learnt_clause.size()]));
                        for (Entry<Rational> var : c.expr.vars.int2ObjectEntrySet()) {
                            c_watches.get(var.getIntKey()).remove(c);
                            if (!layers.isEmpty()) {
                                layers.peekFirst().cnstrs.add(c);
                            }
                            if (c_watches.get(var.getIntKey()).isEmpty()) {
                                c_watches.remove(var.getIntKey());
                            }
                        }
                    }
                    break;
                }
                break;
            }
        }
        return true;
    }

    @Override
    public boolean check(final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        return true;
    }

    @Override
    public void push() {
        layers.add(new Layer());
    }

    @Override
    public void pop() {
        Layer layer = layers.pollFirst();
        // we decrease the lower bounds..
        for (java.util.Map.Entry<PBConstraint, Rational> lb : layer.lbs.entrySet()) {
            if (lb.getValue().isPositive()) {
                lb.getKey().lb.add(lb.getValue());
            } else {
                lb.getKey().lb.sub(lb.getValue());
            }
        }
        // we increase the upper bounds..
        for (java.util.Map.Entry<PBConstraint, Rational> ub : layer.ubs.entrySet()) {
            if (ub.getValue().isPositive()) {
                ub.getKey().ub.sub(ub.getValue());
            } else {
                ub.getKey().ub.add(ub.getValue());
            }
        }
        // we restore the removed constraints..
        for (PBConstraint c : layer.cnstrs) {
            for (Entry<Rational> var : c.expr.vars.int2ObjectEntrySet()) {
                c_watches.computeIfAbsent(var.getIntKey(), k -> new ObjectArrayList<>()).add(c);
            }
        }
    }

    private class PBConstraint {

        final int b; // the controlling (propositional) variable..
        final Lin expr;
        final Op op;
        final InfRational known_term;
        final Rational lb, ub;

        PBConstraint(int b, final Lin expr, Rational lb, Rational ub, final Op op, InfRational known_term) {
            this.b = b;
            this.expr = expr;
            this.op = op;
            this.known_term = known_term;
            for (Entry<Rational> var : expr.vars.int2ObjectEntrySet()) {
                c_watches.computeIfAbsent(var.getIntKey(), k -> new ObjectArrayList<>()).add(this);
            }
            this.lb = lb;
            this.ub = ub;
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append("[b").append(b).append("] ");
            sb.append(expr.toString().replace('x', 'b'));
            switch (op) {
            case LEq:
                sb.append(" <= ");
                break;
            case GEq:
                sb.append(" >= ");
                break;
            default:
                throw new AssertionError(op.name());
            }
            sb.append(known_term.toString());
            return sb.toString();
        }
    }

    enum Op {
        LEq, GEq
    }

    private static class Layer {
        private final Object2ObjectMap<PBConstraint, Rational> lbs = new Object2ObjectOpenHashMap<>();
        private final Object2ObjectMap<PBConstraint, Rational> ubs = new Object2ObjectOpenHashMap<>();
        private final ObjectOpenHashSet<PBConstraint> cnstrs = new ObjectOpenHashSet<>();
    }
}
