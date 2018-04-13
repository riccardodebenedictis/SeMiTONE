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
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import java.util.List;

/**
 *
 * @author Riccardo De Benedictis
 */
public class PBConstraint {

    private final PBTheory th;
    final int b; // the controlling (propositional) variable..
    final Lin expr;
    final Op op;
    final InfRational known_term;
    Rational lb, ub;

    PBConstraint(PBTheory th, int b, final Lin expr, Rational lb, Rational ub, final Op op, InfRational known_term) {
        this.th = th;
        this.b = b;
        this.expr = expr;
        this.op = op;
        this.known_term = known_term;
        expr.vars.int2ObjectEntrySet()
                .forEach(var -> th.c_watches.computeIfAbsent(var.getIntKey(), k -> new ObjectArrayList<>()).add(this));
        this.lb = lb;
        this.ub = ub;
    }

    boolean propagate(final Lit p, final List<Lit> cnfl) {
        if (p.v != b) {
            // we update the bounds..
            Rational c = expr.vars.get(p.v);
            if (c.isPositive()) {
                if (p.sign) {
                    if (!th.layers.isEmpty()) {
                        th.layers.peekFirst().lbs.computeIfAbsent(this, k -> new Rational(lb));
                    }
                    // we increase the lower bound..
                    lb.add(c);
                } else {
                    if (!th.layers.isEmpty()) {
                        th.layers.peekFirst().ubs.computeIfAbsent(this, k -> new Rational(ub));
                    }
                    // we decrease the upper bound..
                    ub.sub(c);
                }
            } else {
                if (p.sign) {
                    if (!th.layers.isEmpty()) {
                        th.layers.peekFirst().ubs.computeIfAbsent(this, k -> new Rational(ub));
                    }
                    // we decrease the upper bound..
                    ub.add(c);
                } else {
                    if (!th.layers.isEmpty()) {
                        th.layers.peekFirst().lbs.computeIfAbsent(this, k -> new Rational(lb));
                    }
                    // we increase the lower bound..
                    lb.sub(c);
                }
            }
        }

        switch (op) {
            case LEq:
                if (known_term.geq(ub)) {  // the constraint has become satisfied as a consequence of the bound update..
                    switch (th.sat.value(b)) {
                        case False: // inconsistency: the constraint must be not satisfied..
                            // we generate an explanation for the inconsistency..
                            break;
                        case Undefined:
                            break;
                    }
                } else if (known_term.lt(lb)) {  // the constraint has become unsatisfable as a consequence of the bound update..
                    switch (th.sat.value(b)) {
                        case True: // inconsistency: the constraint must be satisfied..
                            // we generate an explanation for the inconsistency..
                            break;
                        case Undefined:
                            break;
                        default:
                            throw new AssertionError(th.sat.value(b).name());
                    }
                } else { // we try to propagate something..
                    switch (th.sat.value(b)) {
                        case False:
                            break;
                        case True:
                            break;
                    }
                }
                break;
            case GEq:
                if (known_term.leq(lb)) {  // the constraint has become satisfied as a consequence of the bound update..
                    switch (th.sat.value(b)) {
                        case False: // inconsistency: the constraint must be not satisfied..
                            // we generate an explanation for the inconsistency..
                            break;
                        case Undefined:
                            break;
                        default:
                            throw new AssertionError(th.sat.value(b).name());
                    }
                } else if (known_term.gt(ub)) {  // the constraint has become unsatisfable as a consequence of the bound update..
                    switch (th.sat.value(b)) {
                        case True: // inconsistency: the constraint must be satisfied..
                            // we generate an explanation for the inconsistency..
                            break;
                        case Undefined:
                            break;
                        default:
                            throw new AssertionError(th.sat.value(b).name());
                    }
                } else { // we try to propagate something..
                    switch (th.sat.value(b)) {
                        case False:
                            break;
                        case True:
                            break;
                    }
                }
                break;
            default:
                throw new AssertionError(op.name());
        }
        return true;
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

    enum Op {
        LEq, GEq
    }
}
