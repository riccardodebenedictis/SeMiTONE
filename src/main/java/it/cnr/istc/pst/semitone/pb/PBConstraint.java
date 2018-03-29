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

/**
 *
 * @author Riccardo De Benedictis
 */
class PBConstraint {

    private final PBTheory th;
    final int b; // the controlling (propositional) variable..
    final Lin expr;
    final Op op;
    final InfRational known_term;

    PBConstraint(PBTheory th, int b, final Lin expr, final Op op, InfRational known_term) {
        this.th = th;
        this.b = b;
        this.expr = expr;
        this.op = op;
        this.known_term = known_term;
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
