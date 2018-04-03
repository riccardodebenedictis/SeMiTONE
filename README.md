# SeMiTONE

Satisfiability Modulo Theories (SMT) concerns the satisfiability of formulas with respect to some background theory.
SeMiTONE is a Satisfiability Modulo TheOries NEtwork, allowing the creation of variables and constraints in different underlying theories. Although new theories can be easily integrated, SeMiTONE currently manages a pseudo-boolean theory, a linear real arithmetic theory and an object variable theory.

SeMiTONE maintains backtrackable data structures, allows the creation of variables and constraints, performs constraint propagation and, whenever conflicts arise, performs conflict analysis, learns a no-good and backjumps to the highest level. It is worth noting that SeMiTONE is not an SMT solver. SeMiTONE is, on the contrary, a network on top of which SMT solvers can be built. In this regard, SeMiTONE deliberately neglects all the aspects related to 'search' as, for example, search algorithms and resolution heuristics, demanding to external modules solving SMT problems.

## Usage

At the core of SeMiTONE there is the `Sat` module, allowing the creation of propositional variables and constraints. Propositional variables are identified through integers. The clause creation procedure introduces a new clause, represented by an array of (direct or negated) literals, into the network, returning `false` if some trivial inconsistency is recognized. It is worth noting that in case the clause creation procedure returns `true` there is no guarantee that the network is still consistent since identifying inconsistencies might occur only after a search process.

```java
Sat sat = new Sat();

// we create two propositional variables
int b0 = sat.newVar();
int b1 = sat.newVar();

// we create a propositional constraint (i.e. the (¬b0 ∨ b1) clause)
boolean c0 = sat.newClause(new Lit(b0, false), new Lit(b1));

// the current value of 'b0' (i.e. Undefined)
LBool b0_val = sat.value(b0);
```

Once propositional variables and constraints are created, it is possible to assume values for the variables. Assuming a value for a propositional variable stores the context of the network allowing backtracking (i.e. restoring the context prior of the assignment). Once variables' values are assumed, calling the `check()` procedure entails the propagation of the constraints. While the variable assumption procedure returns `false` if some trivial inconsistency is introduced by the assumption, the checking procedure might recognize an inconsistency, generate a no-good and backtrack at the highest possible level, returning `false` only in case the network becomes definitely inconsistent, independently from possible subsequent assignments.

```java
// we store the context and assume b0
boolean assume = sat.assume(new Lit(b0));

// the current value of 'b0' is now True
b0_val = sat.value(b0);
// the current value of 'b1' is still Undefined
LBool b1_val = sat.value(b1);

// we propagate the constraints
boolean check = sat.check();

// the current value of 'b1' is now True, as a consequence of constraint propagation
b1_val = sat.value(b1);
```

Finally, it is possible to restore the contet prior of the assignment through the `pop()` procedure.

```java
sat.pop();

// the current value of 'b0' and of 'b1' is now back to Undefined
b0_val = sat.value(b0);
b1_val = sat.value(b1);
```