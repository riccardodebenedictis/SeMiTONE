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

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import it.cnr.istc.pst.semitone.lra.Lin;
import it.cnr.istc.pst.semitone.lra.Rational;
import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;

/**
 *
 * @author Riccardo De Benedictis
 */
public class PBTheoryTest {

    @Test
    public void testPBTheory() {
        Sat sat = new Sat();
        PBTheory pb = new PBTheory(sat);

        int b2 = sat.newVar();
        int b3 = sat.newVar();
        Lin l0 = new Lin(b2, new Rational(2)).minus(new Lin(b3, new Rational(3)));

        boolean ch = sat.assume(new Lit(b2)) && sat.assume(new Lit(b3)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational(-1)));
        assertTrue(pb.ub(l0).eq(new Rational(-1)));
        sat.pop();
        sat.pop();

        ch = sat.assume(new Lit(b2)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational(-1)));
        assertTrue(pb.ub(l0).eq(new Rational(2)));
        sat.pop();

        ch = sat.assume(new Lit(b2)) && sat.assume(new Lit(b3, false)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational(2)));
        assertTrue(pb.ub(l0).eq(new Rational(2)));
        sat.pop();
        sat.pop();

        ch = sat.assume(new Lit(b3)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational(-3)));
        assertTrue(pb.ub(l0).eq(new Rational(-1)));
        sat.pop();

        assertTrue(pb.lb(l0).eq(new Rational(-3)));
        assertTrue(pb.ub(l0).eq(new Rational(2)));

        ch = sat.assume(new Lit(b3, false)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational()));
        assertTrue(pb.ub(l0).eq(new Rational(2)));
        sat.pop();

        ch = sat.assume(new Lit(b2, false)) && sat.assume(new Lit(b3)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational(-3)));
        assertTrue(pb.ub(l0).eq(new Rational(-3)));
        sat.pop();
        sat.pop();

        ch = sat.assume(new Lit(b2, false)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational(-3)));
        assertTrue(pb.ub(l0).eq(new Rational()));
        sat.pop();

        ch = sat.assume(new Lit(b2, false)) && sat.assume(new Lit(b3, false)) && sat.check();
        assertTrue(ch);
        assertTrue(pb.lb(l0).eq(new Rational()));
        assertTrue(pb.ub(l0).eq(new Rational()));
        sat.pop();
        sat.pop();
    }
}
