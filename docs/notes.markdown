



Satisfiability Modulo Theories

The Nelson Oppen Method of Combining Decision Procedures

Theories in the Context of Haskell's Type System

XXX: Perhaps this part is too much for this paper...

  - Equations user-defined data types
    - Solve by first-order unification
  - Row types?
  - User-defined type-classes
    - Class instances
    - Super classes
    - Functional dependencies
    - Instance Chains
    - Custom class constraints
      - Typeable
      - Coerciable
      - KnownNat/KnownSymbol
  - Implicit parameters
  - Type families
    - open type families
    - closed type families
    - custom type families:
      - type-level natural numbers
      - units of measure


Integration with an External Decision Procedure

  - Solving Constrinats


Improvement
-----------

An improving substitution some of the variables in a collection of constraints,
withouth changing their satisfiability.
For example, consider the constraint, `(5 + x) ~ 8`.  For this constraint,
`x := 3` is an improving substituion, because `(x ~ 3) iff (5 + x) ~ 8`.


Given, Wanted, and Derived Constraints
--------------------------------------

GHC classifies constraints into three categoris:

  * *Given* constraints are assumptions that may be used in proofs,
  * *Wanted* constraints are goals that need to be proved,
  * *Derived* constraints are implied by the given and wanted constraints.

While given and wanted constraints are fairly standard, derived constraints
are a bit more unusal: they are implied by the givens and wanteds *together*,
so they cannot be used in proofs directly, as this could risk constructing
circular proofs.  On the other hand, we know that information obtains through
derived constraints could be used for improvement, without risk of loosing
generality.  For example, if we encounter a derived constraint `x ~ 3`,
then we know that the only possible way satisfy the current constraint set
is if `x` is 3.  Therefore, if `x` is a unifcation variable, we may simply
replace `x` by 3.


Linear Arithmetic Over the Natural Numbers
------------------------------------------

  * Solver directly
  * Use models to compute improvement:
      - Improve to literal
      - Improve to another variable
      - Improve by linear relation with 1 or more variables.












Citations:

  Simplification by Cooprating Decision Procedures
  Greg Nelson and Derek C. Oppen, Standford University, 1979

  A Simple Algorithm and Proof for Type Inference
  Mitchell Wand, 1987


  Simplifying and Improving Qualified Types

Mark P. Jones, Research Report YALEU/DCS/RR-1040, Yale University, New Haven, Connecticut, USA, June 1994. (Shorter revised version, without proofs, appears in FPCA '95: Conference on Functional Programming Languages and Computer Architecture, La Jolla, CA, June 1995.)



