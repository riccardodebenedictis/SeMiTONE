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

import java.util.List;

/**
 *
 * @author Riccardo De Benedictis
 */
public interface Theory {

    /**
     * Asks the theory to perform propagation after the given literal has been
     * assigned. Returns true if the propagation succeeds or false if an
     * inconsistency is found. In case of inconsistency, the confl vector is
     * filled with the conflicting constraint.
     *
     * @param p the literal that has been assigned.
     * @param cnfl the vector of literals representing the conflicting
     * constraint.
     * @return true if propagation succeeds or false if an inconsistency is
     * found.
     */
    public boolean propagate(final Lit p, final List<Lit> cnfl);

    /**
     * Checks whether the theory is consistent with the given propositional
     * assignments. Returns true if the theory is consistent or false if an
     * inconsistency is found. In case of inconsistency, the confl vector is
     * filled with the conflicting constraint.
     *
     * @param cnfl the vector of literals representing the conflicting
     * constraint.
     * @return true if the theory is consistent or false if an inconsistency is
     * found.
     */
    public boolean check(final List<Lit> cnfl);

    /**
     * Notifies the theory that some information for subsequent backtracking
     * might need to be stored.
     */
    public void push();

    /**
     * Notifies the theory that a backtracking step is required.
     */
    public void pop();
}
