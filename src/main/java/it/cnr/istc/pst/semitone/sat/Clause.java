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
import static it.cnr.istc.pst.semitone.sat.Sat.index;

import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 *
 * @author Riccardo De Benedictis
 */
public class Clause {

    private final Sat sat;
    Lit[] lits;

    Clause(final Sat sat, final Lit[] lits) {
        assert lits.length >= 2;
        this.sat = sat;
        this.lits = lits;
        sat.watches[index(lits[0].not())].add(this);
        sat.watches[index(lits[1].not())].add(this);
    }

    boolean propagate(final Lit p) {
        // make sure false literal is lits[1]..
        if (lits[0].v == p.v) {
            Lit tmp = lits[0];
            lits[0] = lits[1];
            lits[1] = tmp;
        }

        // if 0th watch is true, the clause is already satisfied..
        if (sat.value(lits[0]) == True) {
            sat.watches[index(p)].add(this);
            return true;
        }

        // we look for a new literal to watch..
        for (int i = 1; i < lits.length; i++) {
            if (sat.value(lits[i]) != False) {
                Lit tmp = lits[1];
                lits[1] = lits[i];
                lits[i] = tmp;
                sat.watches[index(lits[1].not())].add(this);
                return true;
            }
        }

        // clause is unit under assignment..
        sat.watches[index(p)].add(this);
        return sat.enqueue(lits[0], this);
    }

    @Override
    public String toString() {
        return Stream.of(lits).map(l -> l.toString()).collect(Collectors.joining(", "));
    }
}
