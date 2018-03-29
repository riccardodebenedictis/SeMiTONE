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
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

/**
 *
 * @author Riccardo De Benedictis
 */
public class RationalTest {

    @Test
    public void testRational() {
        Rational r0 = new Rational();
        assertEquals(0, r0.num);
        assertEquals(1, r0.den);
        r0.add(1);
        assertEquals(1, r0.num);
        assertEquals(1, r0.den);
        r0.add(new Rational(1, 2));
        assertEquals(3, r0.num);
        assertEquals(2, r0.den);
        r0.add(NEGATIVE_INFINITY);
        assertEquals(-1, r0.num);
        assertEquals(0, r0.den);
        Rational r1 = new Rational(4, 2);
        assertEquals(2, r1.num);
        assertEquals(1, r1.den);
        Rational r2 = r1.divide(r0);
        assertEquals(0, r2.num);
        assertEquals(1, r2.den);
        r2.add(2);
        assertEquals(2, r2.num);
        assertEquals(1, r2.den);
        r2.sub(-2);
        assertEquals(4, r2.num);
        assertEquals(1, r2.den);
        r2.mult(2);
        assertEquals(8, r2.num);
        assertEquals(1, r2.den);
    }

    @Test
    public void testRational1() {
        assertTrue(NEGATIVE_INFINITY.lt(POSITIVE_INFINITY));
        assertTrue(NEGATIVE_INFINITY.leq(POSITIVE_INFINITY));
        assertTrue(POSITIVE_INFINITY.geq(NEGATIVE_INFINITY));
        assertTrue(POSITIVE_INFINITY.gt(NEGATIVE_INFINITY));
    }
}
