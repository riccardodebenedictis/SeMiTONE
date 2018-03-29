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

import static it.cnr.istc.pst.semitone.lra.LRATheory.lb_index;
import static it.cnr.istc.pst.semitone.lra.LRATheory.ub_index;

import java.util.List;

import it.cnr.istc.pst.semitone.sat.Lit;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;

/**
 * This class is used for representing tableau rows.
 *
 * @author Riccardo De Benedictis
 */
class Row {

    private final LRATheory th;
    final int x; // the basic variable..
    final Lin l; // the linear expression..

    Row(final LRATheory th, final int x, final Lin l) {
        this.th = th;
        this.x = x;
        this.l = l;
        // we watch for theory propagation..
        for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
            th.t_watches[term.getIntKey()].add(this);
        }
    }

    /**
     * Notifies, for propagation purposes, this tableau row that the lower bound
     * of variable {@code x_i} has changed.
     *
     * @param x_i the variable whose lower bound has changed.
     * @param cnfl the conflict clause in case propagation fails.
     * @return {@code true} if propagation succeeds.
     */
    boolean propagate_lb(final int x_i, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        // we make room for the first literal..
        cnfl.add(new Lit(0));
        if (l.vars.get(x_i).isPositive()) {
            InfRational lb = new InfRational();
            for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
                if (term.getValue().isPositive()) {
                    if (th.lb(term.getIntKey()).rat.isNegativeInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        lb.add(th.lb(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[lb_index(term.getIntKey())].reason.not());
                    }
                } else if (term.getValue().isNegative()) {
                    if (th.ub(term.getIntKey()).rat.isPositiveInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        lb.add(th.ub(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[ub_index(term.getIntKey())].reason.not());
                    }
                }
            }

            if (lb.gt(th.lb(x))) {
                for (Assertion c : th.a_watches[x]) {
                    if (lb.gt(c.v)) {
                        switch (c.op) {
                        case LEq: // the assertion is unsatisfable..
                            cnfl.set(0, new Lit(c.b, false));
                            switch (th.sat.value(c.b)) {
                            case True: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        case GEq: // the assertion is satisfied..
                            cnfl.set(0, new Lit(c.b));
                            switch (th.sat.value(c.b)) {
                            case False: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        }
                    }
                }
            }
        } else {
            InfRational ub = new InfRational();
            for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
                if (term.getValue().isPositive()) {
                    if (th.ub(term.getIntKey()).rat.isPositiveInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        ub.add(th.ub(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[ub_index(term.getIntKey())].reason.not());
                    }
                } else if (term.getValue().isNegative()) {
                    if (th.lb(term.getIntKey()).rat.isNegativeInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        ub.add(th.lb(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[lb_index(term.getIntKey())].reason.not());
                    }
                }
            }

            if (ub.lt(th.ub(x))) {
                for (Assertion c : th.a_watches[x]) {
                    if (ub.lt(c.v)) {
                        switch (c.op) {
                        case LEq: // the assertion is satisfied..
                            cnfl.set(0, new Lit(c.b));
                            switch (th.sat.value(c.b)) {
                            case False: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        case GEq: // the assertion is unsatisfable..
                            cnfl.set(0, new Lit(c.b, false));
                            switch (th.sat.value(c.b)) {
                            case True: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        }
                    }
                }
            }
        }

        cnfl.clear();
        return true;
    }

    /**
     * Notifies, for propagation purposes, this tableau row that the upper bound
     * of variable {@code x_i} has changed.
     *
     * @param x_i the variable whose upper bound has changed.
     * @param cnfl the conflict clause in case propagation fails.
     * @return {@code true} if propagation succeeds.
     */
    boolean propagate_ub(final int x_i, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        // we make room for the first literal..
        cnfl.add(new Lit(0));
        if (l.vars.get(x_i).isPositive()) {
            InfRational ub = new InfRational();
            for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
                if (term.getValue().isPositive()) {
                    if (th.ub(term.getIntKey()).rat.isPositiveInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        ub.add(th.ub(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[ub_index(term.getIntKey())].reason.not());
                    }
                } else if (term.getValue().isNegative()) {
                    if (th.lb(term.getIntKey()).rat.isNegativeInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        ub.add(th.lb(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[lb_index(term.getIntKey())].reason.not());
                    }
                }
            }

            if (ub.lt(th.ub(x))) {
                for (Assertion c : th.a_watches[x]) {
                    if (ub.lt(c.v)) {
                        switch (c.op) {
                        case LEq: // the assertion is satisfied..
                            cnfl.set(0, new Lit(c.b));
                            switch (th.sat.value(c.b)) {
                            case False: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        case GEq: // the assertion is unsatisfable..
                            cnfl.set(0, new Lit(c.b, false));
                            switch (th.sat.value(c.b)) {
                            case True: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        }
                    }
                }
            }
        } else {
            InfRational lb = new InfRational();
            for (Int2ObjectMap.Entry<Rational> term : l.vars.int2ObjectEntrySet()) {
                if (term.getValue().isPositive()) {
                    if (th.lb(term.getIntKey()).rat.isNegativeInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        lb.add(th.lb(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[lb_index(term.getIntKey())].reason.not());
                    }
                } else if (term.getValue().isNegative()) {
                    if (th.ub(term.getIntKey()).rat.isPositiveInfinite()) {
                        // nothing to propagate..
                        cnfl.clear();
                        return true;
                    } else {
                        lb.add(th.ub(term.getIntKey()).times(term.getValue()));
                        cnfl.add(th.bounds[ub_index(term.getIntKey())].reason.not());
                    }
                }
            }

            if (lb.gt(th.lb(x))) {
                for (Assertion c : th.a_watches[x]) {
                    if (lb.gt(c.v)) {
                        switch (c.op) {
                        case LEq: // the assertion is unsatisfable..
                            cnfl.set(0, new Lit(c.b, false));
                            switch (th.sat.value(c.b)) {
                            case True: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        case GEq: // the assertion is satisfied..
                            cnfl.set(0, new Lit(c.b));
                            switch (th.sat.value(c.b)) {
                            case False: // we have a propositional inconsistency..
                                return false;
                            case Undefined: // we propagate information to the sat core..
                                th.sat.record(cnfl.toArray(new Lit[cnfl.size()]));
                            }
                            break;
                        }
                    }
                }
            }
        }

        cnfl.clear();
        return true;
    }

    @Override
    public String toString() {
        return "x" + x + " == " + l.toString();
    }
}
