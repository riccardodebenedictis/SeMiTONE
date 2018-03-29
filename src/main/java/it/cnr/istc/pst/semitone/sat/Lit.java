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

/**
 *
 * @author Riccardo De Benedictis
 */
public class Lit {

    public final int v;
    public final boolean sign;

    public Lit(final int v) {
        this(v, true);
    }

    public Lit(final int v, final boolean sign) {
        this.v = v;
        this.sign = sign;
    }

    public Lit not() {
        return new Lit(v, !sign);
    }

    @Override
    public String toString() {
        return (sign ? "" : "¬") + "b" + v;
    }
}
