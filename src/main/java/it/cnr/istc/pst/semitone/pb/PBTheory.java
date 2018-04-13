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
import static it.cnr.istc.pst.semitone.pb.PBConstraint.Op.GEq;
import static it.cnr.istc.pst.semitone.pb.PBConstraint.Op.LEq;
import it.cnr.istc.pst.semitone.sat.LBool;
import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;
import it.cnr.istc.pst.semitone.sat.Theory;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;

/**
 *
 * @author Riccardo De Benedictis
 */
public class PBTheory implements Theory {

    final Sat sat;
    final Int2ObjectMap<Collection<PBConstraint>> c_watches = new Int2ObjectOpenHashMap<>(); // for each variable 'v', a list of pseudo-boolean constraints watching 'v'..
    private final Int2ObjectMap<PBConstraint> v_cnstrs = new Int2ObjectOpenHashMap<>(); // the pseudo-boolean constraints (propositional variable to constraint) used for enforcing (negating) constraints..
    private final Object2IntMap<String> exprs = new Object2IntOpenHashMap<>(); // the already existing expressions (string to variable)..
    final Deque<Layer> layers = new ArrayDeque<>(); // we store the updated bounds..

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
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, lb, ub, LEq, c_right));
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
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, lb, ub, LEq, c_right));
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
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, lb, ub, GEq, c_right));
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
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, lb, ub, GEq, c_right));
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
                if (sat.value(term.getIntKey()) == LBool.True) {
                    v.add(term.getValue()); // we increase the lower bound..
                }
            } else {
                if (sat.value(term.getIntKey()) != LBool.False) {
                    v.add(term.getValue()); // we decrease the lower bound (notice that the term's constant is negative)..
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
                if (sat.value(term.getIntKey()) != LBool.False) {
                    v.add(term.getValue()); // we increase the upper bound..
                }
            } else {
                if (sat.value(term.getIntKey()) == LBool.True) {
                    v.add(term.getValue()); // we decrease the upper bound (notice that the term's constant is negative)..
                }
            }
        }
        return v;
    }

    @Override
    public boolean propagate(final Lit p, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        return c_watches.get(p.v).stream().noneMatch(c -> !c.propagate(p, cnfl));
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
        // we restore the lower bounds..
        layer.lbs.entrySet().forEach(lb -> lb.getKey().lb = lb.getValue());
        // we restore the upper bounds..
        layer.ubs.entrySet().forEach(ub -> ub.getKey().ub = ub.getValue());
    }
}
