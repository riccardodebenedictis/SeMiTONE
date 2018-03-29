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

import static it.cnr.istc.pst.semitone.sat.LBool.False;
import static it.cnr.istc.pst.semitone.sat.LBool.True;
import static it.cnr.istc.pst.semitone.sat.LBool.Undefined;
import static it.cnr.istc.pst.semitone.sat.Sat.FALSE_var;
import static it.cnr.istc.pst.semitone.sat.Sat.TRUE_var;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

/**
 *
 * @author Riccardo De Benedictis
 */
public class SatTest {

    /**
     * Test of index method, of class Sat.
     */
    @Test
    public void testSat() {
        Sat sat = new Sat();
        assertEquals(True, sat.value(TRUE_var));
        assertEquals(False, sat.value(FALSE_var));

        int b2 = sat.newVar();
        assertEquals(Undefined, sat.value(b2));
        int b3 = sat.newVar();
        assertEquals(Undefined, sat.value(b3));
        int b4 = sat.newVar();
        assertEquals(Undefined, sat.value(b4));

        boolean c0 = sat.newClause(new Lit(b2), new Lit(b3));
        assertTrue(c0);
        boolean c1 = sat.newClause(new Lit(b3), new Lit(b4));
        assertTrue(c1);

        boolean assume = sat.assume(new Lit(b3, false));
        assertTrue(assume);
        boolean check = sat.check();
        assertTrue(check);
        assertEquals(True, sat.value(b2));
        assertEquals(False, sat.value(b3));
        assertEquals(True, sat.value(b4));
    }

    @Test
    public void testNoGood() {
        Sat sat = new Sat();

        int b0 = sat.newVar();
        int b1 = sat.newVar();
        int b2 = sat.newVar();
        int b3 = sat.newVar();
        int b4 = sat.newVar();
        int b5 = sat.newVar();
        int b6 = sat.newVar();
        int b7 = sat.newVar();
        int b8 = sat.newVar();

        boolean nc = sat.newClause(new Lit(b0), new Lit(b1));
        assertTrue(nc);
        nc = sat.newClause(new Lit(b0), new Lit(b2), new Lit(b6));
        assertTrue(nc);
        nc = sat.newClause(new Lit(b1, false), new Lit(b2, false), new Lit(b3));
        assertTrue(nc);
        nc = sat.newClause(new Lit(b3, false), new Lit(b4), new Lit(b7));
        assertTrue(nc);
        nc = sat.newClause(new Lit(b3, false), new Lit(b5), new Lit(b8));
        assertTrue(nc);
        nc = sat.newClause(new Lit(b4, false), new Lit(b5, false));
        assertTrue(nc);

        boolean asm = sat.assume(new Lit(b6, false)) && sat.check();
        assertTrue(asm);
        asm = sat.assume(new Lit(b7, false)) && sat.check();
        assertTrue(asm);
        asm = sat.assume(new Lit(b8, false)) && sat.check();
        assertTrue(asm);
        asm = sat.assume(new Lit(b0, false)) && sat.check();
        assertTrue(asm);
    }
}
