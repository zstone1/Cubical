# Cubical

A Lean 4 + mathlib formalization of Ziemiański-Paliga's cube-chain category `Ch(K)` and its properties. The purpose of the Repo is to do research on cubes, not to build something you should actually reference from other developments.

## Results
The first foundational result is an expansion of the relationship between 
1. The category CH(K), the wedge maps into K. Called ChainCat
2. The RefineObj(K), the category of sequences of cells with morphisms as refinement 

Ziemiański-Paliga proved some facts about the morphisms between these categories. But I assemble them here into an natural isomorphism of categories. 

The second result is that the Salvetti Complex of the braid arrangement is isomorphic to the category of elements for a nice functor on K. In particular, it sends a map `serialWedge A -> K` to the set of minimal `serialWedge [1,...,1] -> K` that refine it. The morphisms, though, are not just refinement. Given a `f:serialWedge A -> serialWedge B`, f breaks into a series of face embeddings, each of which has a retraction. And a morphism `[1,...,1] -> serialWedge B` flows back along those retractions, and reassembles into a `[1,...,1] - serialWedge A`. 

The the third, most interesting result. Let K be a Higher Dimensional Automata with labels L, with the additional property that every minimal chain of K hits each label at most once. This is called RunInjective. It's weaker than euclidean for reference. Let V \subset R^L be the set of valid schedules of events.

Then there is an adjunction between Ch(K) and open convex subsets of V. Furthermore, the maximal chains in CH(K) induce a good cover of V. So Ch(K) and V are homotopy equivalent!
1. The open convex sets have a close relationship with the braid arrangement. And with COMs over the braid arrangement
2. V is also more-or-less the space of morse functions on K. 

## AI Usage
Let's be real, claude wrote the vast majority of the code. So I can't vouch for the quality of these proofs, but the theorem statements should be the right ones.

## Other junk
There are some partial thoughts on cobordisms between precubical sets, and a few other proofs that were bad.

