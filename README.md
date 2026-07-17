# Cubical

A Lean 4 + mathlib formalization of Ziemiański-Paliga's cube-chain category `Ch(K)` and its properties. The purpose of the Repo is to do research on cubes, not to build something you should actually reference from other developments.

## Results
The main result is to extend `Ch(K)` to a complexified version, call it Ch*(K) (ConcCat(K) in the repo), in the spirit of salvetti's theorem. Like Salvetti's theorem, while the invariant in the `Configuration Spaces` paper trivializes on sculptural sets, this complexified invariant does not collapse!

The construction observes that lines, ([1,...,1] -> serialWedge A -> K) are like topes from hyperplane arrangement theory. We represent them as permutations in the code to make some of the proofs combinatorial giving Claude a prayer at brute forcing them. Following this story through, we build a functor (Lines : Ch(K)^op => Set), which mirrors the construction of the Salvetti poset. Then it's category of elements is exactly Ch*(K), and the salvetti complex of the braid arrangement agrees precisely with Ch*(cube). 

Morphisms in this category have permutations associated with them, so we can lift those to braid words. They compose nicely in a way that respect the braiding rules! So we can build a functor into braids this way.

We prove that this functor agrees with the construction from Salvetti's theorem, and that gives us the first nice result:

pi_1|Ch*(cube n)| = pure braids

Using the covering trick from PZ, we get 

pi_1|Ch*(cube n)/Sigma_n| = braids

From here we want to an _injection_ from braids into pi_1|Ch*(Z)|, the final precubical object (verified, but awfully. Deleted and we're gonna try again a better way). 

However, we have also verified that pi_1|Ch*(Z)| is strictly bigger than Braid.

## Testing
We also have some testing files, since things are computable. We have verified that the boundary of the cube maps to the center of the pure braids. So the invariant is somewhat sensitive to holes. We have also spot-checked out statement of salvetti's theorem (but more could be done there). 

And lastly, we have some next steps to try to figure out what Ch*(K) actually is.

## Axioms
We to take Salvetti's theorem as an axiom: we build a map `pi_1|Sal(braid arrangement)| -> Pure Braids`, and assert that it is injective. We prove surjectivity by hand so avoid a non-computable existential in an axiom.

## AI Usage
Let's be real, claude wrote the vast majority of this slop. It's gonna take some time to unslop it. But the results are good, and the overall proof structure is sensible.
