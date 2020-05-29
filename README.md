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

### Transformations

The goal then is to describe an algorithm as a passage from one molecule to another applying rules.

For this matter, we introduced rules to describe transformations between molecules, and then transformations.
The chosen restriction of linear logic and its rules can be found [here](https://drive.google.com/file/d/1M0zz_e-NL7pd5JiK6T-ITOtcgp3rFt5z/view?usp=sharing).

### Application to graph algorithms

Thus far, we have two main implementations
