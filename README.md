# Cubical

A Lean 4 + mathlib formalization of Ziemiański-Paliga's cube-chain category `Ch(K)` and its properties. The purpose of the Repo is to do research on cubes, not to build something you should actually reference from other developments.

## Results
The main result is to extend `Ch(K)` to a complexified version, call it Ch*(K) (ConcCat(K) in the repo), in the spirit of salvetti's theorem. Like Salvetti's theorem, while the invariant in the `Configuration Spaces` paper trivializes on sculptural sets, this complexified invariant does not collapse!

The construction goes as follows:

1. For any Bipointed Precubical Set (BPSet), we can define `IsRun` on a chain `\/a -> K` as `a` having all `1`s. Then we can define `Run(K) := IsRun.FullSubcategory`, that is, the full subcategory of `Ch(K)` whose domains are 1-dimensional. We can define for `K`, the set of EdgeChains, that is sequences of 1-cells in K which form a sequence. Unsurprisingly, these agree with the definition of Run
2. Now, let's think of Precubical as the presheaf topos on Box here. Any precubical map of cubes `[]n -> []m` corresponds to a face map, coming from the Box category. That face map has a corresponding projection: a degenerecy not present in Precubical. However, that degenerecy induces a function `([]n -> []m) -> EdgeChain m -> EdgeChain n` by projecting the chain along the face. This turns out to be a functor from Box to Type, exactly an element of Precubical! We call it `runPresheaf`. Moreover, this thing has a single basepoint.
3. A bit of general machinery in WedgeHom.lean, any such presheaf P, with a unique 0-cell induces an equivalence 
     ((⋁a).toPsh ⟶ P) ≃ ∏ᵢ P.obj (op ▫aᵢ)
   That is, maps into P split over the wedges uniformly. This is yoneda shenanigans
4. Lifting that machinery, we can extend our map `([]m -> []n) -> Run n -> Run m` over wedges in both the inputs and the outputs, 
   giving us a `runRestrict : (\/a -> \/b) -> Run (\/b) -> Run(\/ a). Essentialy just propagating the projection maps along each coordinate, respecting the monoidal wedge structure the whole way (Runs.Lean)
5. That lets us define Lines : Precubical => Type sending 
      K => objects of Run(K)
      (f : \/a -> \/b) => runRestrict f
    Interestingly, we don't use the fact that `f` commutes the maps into K here.
    Instead, we build Ch*(K) := (Lines K).Elements, the category of elements for Lines.
      objects : Pairs of ((a, f : \/a -> K), \/[1,...,1] -> \/ a)
      morphisms are those from Ch in the first coordinate, and in the second it's "compatible paths by coordinates"
Now, a few observations from here. Firstly, 
> The salvetti complex Sal(braidCOM n) ~ Ch*(cube n)

So, by salvetti's theorem,
> The salvetti complex pi_1|Sal(braidCOM n)| ~pi_1|Ch*(cube n)|

Note that we generally use `FreeGroupoid` instead of pi_1, nerve, and geometric realization for ease of computation.
And because mathlib's support for homotopy limits is missing.

Ch*(cube n) also has a Sigma_n free action, so using the covering machinery, and the 5 lemma
> pi_1|Ch*(cube n)/Sigma_n| = braids

Even better, the construction for the braid trick is reproducible from the Ch* side _without_ going through the Sal machinery. Esse

From here we want to an _injection_ from braids into pi_1|Ch*(Z)|, the final precubical object (verified, but awfully. Deleted and we're gonna try again a better way). 

However, we have also verified that pi_1|Ch*(Z)| is strictly bigger than Braid. 

## Testing
We also have some testing files, since things are computable. We have verified that the boundary of the cube maps to the center of the pure braids. So the invariant is somewhat sensitive to holes. We have also spot-checked out statement of salvetti's theorem (but more could be done there). 

And lastly, we have some next steps to try to figure out what Ch*(K) actually is.

## Axioms
We to take Salvetti's theorem as an axiom: we build a map `pi_1|Sal(braid arrangement)| -> Pure Braids`, and assert that it is injective. We prove surjectivity by hand so avoid a non-computable existential in an axiom.

## AI Usage
Let's be real, claude wrote the vast majority of this slop. It's gonna take some time to unslop it. But the results are good, and the overall proof structure is sensible.
