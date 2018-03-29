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

import it.unimi.dsi.fastutil.ints.Int2ObjectAVLTreeMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectSortedMap;

/**
 *
 * @author Riccardo De Benedictis
 */
public class Lin {

    public final Int2ObjectSortedMap<Rational> vars = new Int2ObjectAVLTreeMap<>();
    public Rational known_term;

    public Lin() {
        this.known_term = new Rational();
    }

    public Lin(final int v) {
        vars.put(v, new Rational(1));
        this.known_term = new Rational();
    }

    public Lin(final Rational known_term) {
        this.known_term = known_term;
    }

    public Lin(final int v, final Rational c) {
        vars.put(v, c);
        this.known_term = new Rational();
    }

    public void add(final int v, final Rational c) {
        Rational rat = vars.get(v);
        if (rat != null) {
            rat.add(c);
            if (rat.eq(0)) {
                vars.remove(v);
            }
        } else {
            vars.put(v, new Rational(c));
        }
    }

    public void add(final Lin rhs) {
        for (Int2ObjectMap.Entry<Rational> entry : rhs.vars.int2ObjectEntrySet()) {
            Rational rat = vars.get(entry.getIntKey());
            if (rat != null) {
                rat.add(entry.getValue());
            } else {
                vars.put(entry.getIntKey(), new Rational(entry.getValue()));
            }
        }
        vars.int2ObjectEntrySet().removeIf(term -> term.getValue().eq(0));
        known_term.add(rhs.known_term);
    }

    public void sub(final Lin rhs) {
        for (Int2ObjectMap.Entry<Rational> entry : rhs.vars.int2ObjectEntrySet()) {
            Rational rat = vars.get(entry.getIntKey());
            if (rat != null) {
                rat.sub(entry.getValue());
            } else {
                vars.put(entry.getIntKey(), entry.getValue().minus());
            }
        }
        vars.int2ObjectEntrySet().removeIf(term -> term.getValue().eq(0));
        known_term.sub(rhs.known_term);
    }

    public void add(final Rational rhs) {
        known_term.add(rhs);
    }

    public void sub(final Rational rhs) {
        known_term.sub(rhs);
    }

    public void mult(final Rational rhs) {
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            vars.get(entry.getIntKey()).mult(rhs);
        }
        vars.int2ObjectEntrySet().removeIf(term -> term.getValue().eq(0));
        known_term.mult(rhs);
    }

    public void div(final Rational rhs) {
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            vars.get(entry.getIntKey()).div(rhs);
        }
        vars.int2ObjectEntrySet().removeIf(term -> term.getValue().eq(0));
        known_term.div(rhs);
    }

    public void add(final long rhs) {
        known_term.add(rhs);
    }

    public void sub(final long rhs) {
        known_term.sub(rhs);
    }

    public void mult(final long rhs) {
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            vars.get(entry.getIntKey()).mult(rhs);
        }
        vars.int2ObjectEntrySet().removeIf(term -> term.getValue().eq(0));
        known_term.mult(rhs);
    }

    public void div(final long rhs) {
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            vars.get(entry.getIntKey()).div(rhs);
        }
        vars.int2ObjectEntrySet().removeIf(term -> term.getValue().eq(0));
        known_term.div(rhs);
    }

    public Lin plus(final Lin rhs) {
        Lin lin = new Lin(known_term.plus(rhs.known_term));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), new Rational(entry.getValue()));
        }
        for (Int2ObjectMap.Entry<Rational> entry : rhs.vars.int2ObjectEntrySet()) {
            Rational rat = lin.vars.get(entry.getIntKey());
            if (rat != null) {
                rat.add(entry.getIntKey());
            } else {
                lin.vars.put(entry.getIntKey(), new Rational(entry.getValue()));
            }
        }
        return lin;
    }

    public Lin minus(final Lin rhs) {
        Lin lin = new Lin(known_term.minus(rhs.known_term));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), new Rational(entry.getValue()));
        }
        for (Int2ObjectMap.Entry<Rational> entry : rhs.vars.int2ObjectEntrySet()) {
            Rational rat = lin.vars.get(entry.getIntKey());
            if (rat != null) {
                rat.sub(entry.getIntKey());
            } else {
                lin.vars.put(entry.getIntKey(), entry.getValue().minus());
            }
        }
        return lin;
    }

    public Lin plus(final Rational rhs) {
        Lin lin = new Lin(known_term.plus(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), new Rational(entry.getValue()));
        }
        return lin;
    }

    public Lin minus(final Rational rhs) {
        Lin lin = new Lin(known_term.minus(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), new Rational(entry.getValue()));
        }
        return lin;
    }

    public Lin times(final Rational rhs) {
        Lin lin = new Lin(known_term.times(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().times(rhs));
        }
        return lin;
    }

    public Lin divide(final Rational rhs) {
        Lin lin = new Lin(known_term.divide(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().divide(rhs));
        }
        return lin;
    }

    public Lin plus(final long rhs) {
        Lin lin = new Lin(known_term.plus(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().divide(rhs));
        }
        return lin;
    }

    public Lin minus(final long rhs) {
        Lin lin = new Lin(known_term.minus(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().divide(rhs));
        }
        return lin;
    }

    public Lin times(final long rhs) {
        Lin lin = new Lin(known_term.times(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().divide(rhs));
        }
        return lin;
    }

    public Lin divide(final long rhs) {
        Lin lin = new Lin(known_term.divide(rhs));
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().divide(rhs));
        }
        return lin;
    }

    public Lin minus() {
        Lin lin = new Lin(known_term.minus());
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            lin.vars.put(entry.getIntKey(), entry.getValue().minus());
        }
        return lin;
    }

    @Override
    public String toString() {
        if (vars.isEmpty()) {
            return known_term.toString();
        }

        StringBuilder str = new StringBuilder();
        int first_var = vars.firstIntKey();
        for (Int2ObjectMap.Entry<Rational> entry : vars.int2ObjectEntrySet()) {
            if (entry.getIntKey() == first_var) {
                if (entry.getValue().eq(1)) {
                    str.append("x");
                } else if (entry.getValue().eq(-1)) {
                    str.append("-x");
                } else {
                    str.append(entry.getValue().toString()).append("*x");
                }
                str.append(entry.getIntKey());
            } else {
                if (entry.getValue().eq(1)) {
                    str.append(" + x");
                } else if (entry.getValue().eq(-1)) {
                    str.append(" - x");
                } else if (entry.getValue().isPositive()) {
                    str.append(" + ").append(entry.getValue().toString()).append("*x");
                } else {
                    str.append(" - ").append(entry.getValue().minus().toString()).append("*x");
                }
                str.append(entry.getIntKey());
            }
        }
        if (known_term.isPositive()) {
            str.append(" + ").append(known_term.toString());
        }
        if (known_term.isNegative()) {
            str.append(" - ").append(known_term.minus().toString());
        }
        return str.toString();
    }
}
