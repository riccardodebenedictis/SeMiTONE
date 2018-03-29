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

import it.cnr.istc.pst.semitone.lra.InfRational;
import it.cnr.istc.pst.semitone.lra.Lin;
import it.cnr.istc.pst.semitone.lra.Rational;
import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;
import static it.cnr.istc.pst.semitone.sat.Sat.FALSE_var;
import static it.cnr.istc.pst.semitone.sat.Sat.TRUE_var;
import it.cnr.istc.pst.semitone.sat.Theory;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import java.util.Collection;
import java.util.List;

/**
 *
 * @author Riccardo De Benedictis
 */
public class PBTheory implements Theory {

    private final Sat sat;
    final Int2ObjectMap<Collection<PBConstraint>> c_watches = new Int2ObjectOpenHashMap<>(); // for each variable 'v', a list of pseudo-boolean constraints watching 'v'..
    private final Int2ObjectMap<PBConstraint> v_cnstrs = new Int2ObjectOpenHashMap<>(); // the pseudo-boolean constraints (propositional variable to constraint) used for enforcing (negating) constraints..
    private final Object2IntMap<String> exprs = new Object2IntOpenHashMap<>(); // the already existing expressions (string to variable)..

    public PBTheory(Sat sat) {
        this.sat = sat;
        sat.addTheory(this);
    }

    public int newLt(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus(), -1);
        l_xpr.known_term = new Rational();

        if (ub(l_xpr).leq(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (lb(l_xpr).gt(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " <= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, PBConstraint.Op.LEq, c_right));
            return ctr;
        });
    }

    public int newLEq(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus());
        l_xpr.known_term = new Rational();

        if (ub(l_xpr).leq(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (lb(l_xpr).gt(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " <= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, PBConstraint.Op.LEq, c_right));
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

        if (lb(l_xpr).geq(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (ub(l_xpr).lt(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " >= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, PBConstraint.Op.GEq, c_right));
            return ctr;
        });
    }

    public int newGt(final Lin left, final Lin right) {
        Lin l_xpr = left.minus(right);

        final InfRational c_right = new InfRational(l_xpr.known_term.minus(), 1);
        l_xpr.known_term = new Rational();

        if (lb(l_xpr).geq(c_right)) {
            return TRUE_var; // the constraint is already satisfied..
        } else if (ub(l_xpr).lt(c_right)) {
            return FALSE_var; // the constraint is unsatisfable..
        }

        return exprs.computeIntIfAbsent(l_xpr.toString() + " >= " + c_right.toString(), s_xpr -> {
            final int ctr = sat.newVar();
            sat.bind(ctr, this);
            v_cnstrs.put(ctr, new PBConstraint(this, ctr, l_xpr, PBConstraint.Op.GEq, c_right));
            return ctr;
        });
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
            if (term.getValue().isPositive()) {
                switch (sat.value(term.getIntKey())) {
                case True:
                    v.add(term.getValue());
                }
            } else {
                switch (sat.value(term.getIntKey())) {
                case True:
                case Undefined:
                    v.sub(term.getValue());
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
    public InfRational ub(final Lin l) {
        InfRational v = new InfRational(l.known_term);
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
                    v.sub(term.getValue());
                }
            }
        }
        return v;
    }

    @Override
    public boolean propagate(Lit p, List<Lit> cnfl) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public boolean check(List<Lit> cnfl) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void push() {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

    @Override
    public void pop() {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }
}
