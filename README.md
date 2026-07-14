# Cubical

A Lean 4 + mathlib formalization of Ziemiański-Paliga's cube-chain category `Ch(K)` and its properties. The purpose of the Repo is to do research on cubes, not to build something you should actually reference from other developments.

## Results
The main result enhances the fundamental category for a precubical set, using a "complexification" trick inspired by salvetti's theorem
1. The fundamental category for a precubical set K is really a 2-category with 
    - 0-cells as vertices
    - 1-cells as chains between vertices
    - 2-cells as dihomotopies between chains
2. The "complexified" fundamental category is a 2-category with
    - 0-cells as vertices
    - 1-cells as (chains, runs that refine that chain) where a "run" is a chain of all 1-cells in K
    - 2-cells as braids

The magic is that these braids tell us a bunch of useful things about K. For example
> for every point v, and every braid b over Hom(v,v), b is a pure braid <=> K is "special", I.E. K is an HDA

## The proof
The three very useful results:
- As in Ziemiański-Paliga, the category of "chains in K" with refinement and the category of "wedge maps into K, aka Ch(K)" behave nicely. And when K is non-self-linked and admits altitudes, they are naturally isomorphic.
- Sal(braid arrangement) = Ch*(cube), and a whole bunch of composition facts about this.
- Let f be a point in the complexified Ch(K), call it Ch*(K). Then CH*(K)/f ~ Salvetti complex (a braid arrangement depending on f)
- So we can assemble the enrichment locally, exploiting the local braid arrangement structure

## AI Usage
Let's be real, claude wrote the vast majority of the code. So I can't vouch for the quality of these proofs, but the theorem statements should be the right ones.

## Other junk
There are some partial thoughts on cobordisms between precubical sets, and a few other proofs that were bad.

