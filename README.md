# CertifiedDjikstraLanguage

## Which initial problem ?

This work was initiated because we thought that graph algorithms and more generally algorithms (which are often 
encoded in imperative languages) could become a bit tricky to understand once they become more sophisticated.

Moreover, the proofs made on their behaviour often rely on their mathematical definition on not on their precise
implementation, whereas there often are side effects which are easier to deal with on the paper than in the program.

Additionally, to have a more intuitive way to define way, we thought the logical point of view would be quite
appropriate. With this aim in mind, it became clear that Linear Logic would be great to define algorithms,
because it relies on the consumption of hypotheses to produce outputs, which is quite similar to what an
imperative algorithm does.

That is why we decided to encode in Coq a minimal subset of linear logic to describe graph algorithms, with
the example of Djikstra.

## Theories

### Molecules

First, the algorithm's state is represented by a multiplicative conjunction of atoms (which can wrap whatever
information), called **Molecules**. Their definition is not optimised yet, as we prefered for the sake of
intuition to define them in a non-deterministic fashion (Molecule := 1 | atom | M * M) and to focus atoms
in a molecule with rules later on (this could be change for matters of optimisation).

The focus rules are based on a categoric theory on prefixes and suffixes introduced by H.Grall, where we tend
to describe indexing in a monadic fashion.

The second important thing about molecules is to define a notion of molecular equivalence, which is globally
the equality between two sets of atoms up-to-permutation.

Basically, the rules to show **molecular equivalence** are :
  * The molecular and atomistic identities
  * The 1-eliminiation and 1-axiom
  * The cut
  * The left an right conjunction

### Transformations

The goal then is to describe an algorithm as a passage from one molecule to another applying rules.

For this matter, we introduced rules to describe transformations between molecules, and then transformations.
The chosen restriction of linear logic and its rules can be found [here](https://drive.google.com/file/d/1M0zz_e-NL7pd5JiK6T-ITOtcgp3rFt5z/view?usp=sharing).

Basically, using a **shallow embedding** in our transformations, we introduce the rules :
  * Molecular Identity : the transformation is over (with an empty set of rules), we can show the equivalence
  * Linear Implication : if we respect certain conditions and show the left side of the linear implication in the rule we apply, we can assume its conclusion
  * 1st and 2nd order instantiations : we can instantiate a rule's variables thanks to **Coq's forall** operator, to apply the rule for specific variables (either they are atoms or molecules)
  * Cut
  * Rule duplication : a rule can be duplicated indefinitely (!) thanks to **Coq's cofix**, and can be removed only if we respect certain stopping conditions

There are a few other simple rules we introduced on rule's structure, such as conjuction or disjunction. For more detail, it is better to read the report mentionned above (it is in french, but I could translate it quickly).

### Application to graph algorithms

There is a first simple difference in the version (as mentionned in the report above):
  * There is a **straight** version with no intermediate structure, where we generate directly candidates from the graph to the table
  * There is a **intermediate** version, where we introduced a candidate table, which is a simple structure to decide which methods/order of selection we use to generate table's elements, with different push/pop methods (**depth-first/breadth-first search**)
  * There is another intermediate version but without the list structure and without push/pop methods, which is now obsolete.
Thus far, we have two main implementations of graph algorithms with our logical backend :
  * A **free** version, where we can apply rules to transform the graph, and stop whenever we think we reached the final state
  * A **constrained** version, where we need to prove that no more rules are appliable once we decide to stop
  * We are currently still working on a **generic** formulation of the constrained version, where the stopping conditions would be more general (depending on the guards), but it complicates a lot tactics because we then need inversion when we introduce ~.

## Compiler

The initial goal was to introduce a clearer vision of algorithms, but it eventually became (as often in Coq) quite complicated to visualize the simple process. That's why I decided to introduce a small DSL in Xtext to simplify everything a bit.  

The current version if really simple : I introduced a definition of Djikstra's algorithm which is quite close to our logical formulation, which calculates the Djikstra table from a graph and its root (there is a constant overflow parameter to cap its number of iterations, but we could (1) Find and expose a decreasing argument or (2) calculate a sup instead of a constant which would depend on the graph's size and degree).  

The function also returns the order of candidate generation to be able to compute a tactic which will help to prove the generation of the table.

So basically, in the DSL, you juste need to write something like that :
```
Graph := G (1, 2, 4) (1, 4, 1) (1, 5, 2) (4, 5, 2) (4, 6, 3) 
		   (5, 6, 1) (5, 3, 0) (3, 2, 3) (4, 2, 4) // Define the graph Arcs

Root := R 1 // Adds the candidate (1, 1, 0) to begin

Transformation o-> Graph, Root // Generate the table for graph Graph with root Root
```

And the DSL generates a small file which is intended to be compiled straight in theories. I used idtac to display all the information you need to know about the table generation, and all of this ensuring several properties while doing it.

To be continued...
