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

import org.junit.jupiter.api.Test;

/**
 *
 * @author Riccardo De Benedictis
 */
public class LinTest {

    @Test
    public void testLin() {
        Lin l0 = new Lin();
        l0.add(0, new Rational(1));
        l0.add(1, new Rational(2));

        Lin l1 = new Lin();
        l1.add(1, new Rational(1));
        l1.add(2, new Rational(2));

        Lin l2 = l0.plus(l1);
    }
}
