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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.Test;

import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;

/**
 *
 * @author Riccardo De Benedictis
 */
public class LRATheoryTest {

    @Test
    public void testLRATheory() {
        Sat sat = new Sat();
        LRATheory lra = new LRATheory(sat);

        int x = lra.newVar();
        int y = lra.newVar();
        int s1 = lra.newVar(new Lin(x, new Rational(-1)).plus(new Lin(y)));
        int s2 = lra.newVar(new Lin(x, new Rational(1)).plus(new Lin(y)));

        // x <= -4
        boolean nc = sat.newClause(new Lit(lra.newLEq(new Lin(x), new Lin(new Rational(-4))))) && sat.check();
        assertTrue(nc);
        // x >= -8
        nc = sat.newClause(new Lit(lra.newGEq(new Lin(x), new Lin(new Rational(-8))))) && sat.check();
        assertTrue(nc);
        // s1 <= 1
        nc = sat.newClause(new Lit(lra.newLEq(new Lin(s1), new Lin(new Rational(1))))) && sat.check();
        assertTrue(nc);

        // s2 >= -3
        boolean asm = sat.assume(new Lit(lra.newGEq(new Lin(s2), new Lin(new Rational(-3)))));
        assertFalse(asm);
    }

    @Test
    public void testInequalities() {
        Sat sat = new Sat();
        LRATheory lra = new LRATheory(sat);

        int x = lra.newVar();
        int y = lra.newVar();

        // x >= y;
        boolean nc = sat.newClause(new Lit(lra.newGEq(new Lin(x), new Lin(y)))) && sat.check();
        assertTrue(nc);

        InfRational x_val = lra.value(x);
        assertTrue(x_val.eq(0));

        InfRational y_val = lra.value(y);
        assertTrue(y_val.eq(0));

        // y >= 1
        nc = sat.newClause(new Lit(lra.newGEq(new Lin(y), new Lin(new Rational(1))))) && sat.check();
        assertTrue(nc);

        x_val = lra.value(x);
        assertTrue(x_val.eq(1));

        y_val = lra.value(y);
        assertTrue(y_val.eq(1));
    }

    @Test
    public void testStrictInequalities() {
        Sat sat = new Sat();
        LRATheory lra = new LRATheory(sat);

        int x = lra.newVar();
        int y = lra.newVar();

        // x > y;
        boolean nc = sat.newClause(new Lit(lra.newGt(new Lin(x), new Lin(y)))) && sat.check();
        assertTrue(nc);

        InfRational x_val = lra.value(x);
        assertTrue(x_val.eq(new InfRational(new Rational(), new Rational(1))));

        InfRational y_val = lra.value(y);
        assertTrue(y_val.eq(0));

        // y >= 1
        nc = sat.newClause(new Lit(lra.newGEq(new Lin(y), new Lin(new Rational(1))))) && sat.check();
        assertTrue(nc);

        x_val = lra.value(x);
        assertTrue(x_val.eq(new InfRational(new Rational(1), new Rational(1))));

        y_val = lra.value(y);
        assertTrue(y_val.eq(1));
    }
}
