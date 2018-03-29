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
package it.cnr.istc.pst.semitone.var;

import static it.cnr.istc.pst.semitone.sat.LBool.False;
import it.cnr.istc.pst.semitone.sat.Lit;
import it.cnr.istc.pst.semitone.sat.Sat;
import static it.cnr.istc.pst.semitone.sat.Sat.FALSE_var;
import static it.cnr.istc.pst.semitone.sat.Sat.TRUE_var;
import it.cnr.istc.pst.semitone.sat.Theory;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.Object2IntMap;
import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import it.unimi.dsi.fastutil.objects.ObjectOpenHashSet;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 *
 * @author Riccardo De Benedictis
 */
public class VarTheory implements Theory {

    private static final int DEFAULT_INIT_SIZE = 16;
    private final Sat sat;
    private int n_vars = 0;
    private VarDomain[] domains = new VarDomain[DEFAULT_INIT_SIZE]; // the current assignments (val to bool variable)..
    private final Object2IntMap<String> exprs = new Object2IntOpenHashMap<>(); // the already existing expressions (string to variable)..
    private final Int2ObjectMap<Collection<Integer>> is_contained_in = new Int2ObjectOpenHashMap<>(); // the boolean variable contained in the object variables (bool variable to vector of object variables)..

    public VarTheory(final Sat sat) {
        this.sat = sat;
        sat.addTheory(this);
    }

    /**
     * Creates and returns a new object variable having the {@code vals} allowed
     * values.
     *
     * @param vals the allowed values of the new object variable.
     * @return an integer representing the new object variable.
     */
    public int newVar(final Set<Object> vals) {
        assert !vals.isEmpty();
        final int id = n_vars++;
        ensureCapacity(id);
        domains[id] = new VarDomain();
        if (vals.size() == 1) {
            domains[id].put(vals.iterator().next(), TRUE_var);
        } else {
            for (Object val : vals) {
                int bv = sat.newVar();
                domains[id].put(val, bv);
                sat.bind(bv, this);
                Collection<Integer> ici = is_contained_in.get(bv);
                if (ici == null) {
                    ici = new ObjectArrayList<>();
                    is_contained_in.put(bv, ici);
                }
                ici.add(id);
            }
        }
        return id;
    }

    /**
     * Creates and returns a new object variable having {@code vars} as
     * controlling variables and {@code vals} as allowed values.
     *
     * @param vars an array of integers representing the boolean variables
     * controlling value of the new object variable.
     * @param vals the allowed values of the new object variable.
     * @return an integer representing the new object variable.
     */
    public int newVar(final int[] vars, final Object[] vals) {
        assert vars.length == vals.length;
        assert vars.length > 0;
        assert Arrays.stream(vars).allMatch(v -> is_contained_in.containsKey(v));
        final int id = n_vars++;
        ensureCapacity(id);
        domains[id] = new VarDomain();
        for (int i = 0; i < vars.length; i++) {
            domains[id].put(vals[i], vars[i]);
            is_contained_in.get(vars[i]).add(id);
        }
        return id;
    }

    /**
     * Returns the boolean variable controlling whether the {@code var} variable
     * can assume the {@code val} value.
     *
     * @param var an integer representing an object variable.
     * @param val a possible value for variable {@code var}.
     * @return an integer representing the boolean variable controlling whether
     * the {@code var} variable can assume the {@code val} value.
     */
    public int allows(final int var, final Object val) {
        return domains[var].getOrDefault(val, FALSE_var);
    }

    public int newEq(final int l, final int r) {
        if (l == r) {
            return TRUE_var;
        }
        if (l > r) {
            return newEq(r, l);
        }

        return exprs.computeIntIfAbsent("e" + l + " == e" + r, s_xpr -> {
            Set<Object> intersection = new ObjectOpenHashSet<>();
            Set<Object> l_vals = value(l);
            Set<Object> r_vals = value(r);
            if (l_vals.size() < r_vals.size()) {
                for (Object l_val : l_vals) {
                    if (r_vals.contains(l_val)) {
                        intersection.add(l_val);
                    }
                }
            } else {
                for (Object r_val : r_vals) {
                    if (l_vals.contains(r_val)) {
                        intersection.add(r_val);
                    }
                }
            }
            if (intersection.isEmpty()) {
                return FALSE_var;
            }

            // we need to create a new variable..
            int var = sat.newVar();
            boolean nc;
            for (Object l_val : l_vals) {
                if (!intersection.contains(l_val)) {
                    nc = sat.newClause(new Lit(var, false), new Lit(domains[l].getInt(l_val), false));
                    assert nc;
                }
            }
            for (Object r_val : r_vals) {
                if (!intersection.contains(r_val)) {
                    nc = sat.newClause(new Lit(var, false), new Lit(domains[r].getInt(r_val), false));
                    assert nc;
                }
            }
            for (Object val : intersection) {
                nc = sat.newClause(new Lit(var, false), new Lit(domains[l].getInt(val), false),
                        new Lit(domains[r].getInt(val)));
                assert nc;
                nc = sat.newClause(new Lit(var, false), new Lit(domains[l].getInt(val)),
                        new Lit(domains[r].getInt(val), false));
                assert nc;
                nc = sat.newClause(new Lit(var), new Lit(domains[l].getInt(val), false),
                        new Lit(domains[r].getInt(val), false));
                assert nc;
            }
            return var;
        });
    }

    public final Set<Object> value(final int var) {
        return domains[var].object2IntEntrySet().stream().filter(entry -> sat.value(entry.getIntValue()) != False)
                .map(entry -> entry.getKey()).collect(Collectors.toSet());
    }

    @Override
    public boolean propagate(final Lit p, final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        return true;
    }

    @Override
    public boolean check(final List<Lit> cnfl) {
        assert cnfl.isEmpty();
        return true;
    }

    @Override
    public void push() {
    }

    @Override
    public void pop() {
    }

    private void ensureCapacity(final int minCapacity) {
        int capacity = domains.length;
        while (minCapacity > capacity) {
            capacity = (capacity * 3) / 2 + 1;
            if (minCapacity < capacity) {
                VarDomain[] c_domains = new VarDomain[capacity << 1];
                System.arraycopy(domains, 0, c_domains, 0, domains.length);
                domains = c_domains;
            }
        }
    }

    static class VarDomain extends Object2IntOpenHashMap<Object> {
    }
}
