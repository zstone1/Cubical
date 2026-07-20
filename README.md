# Cubical

A Lean 4 + mathlib formalization of Ziemiański-Paliga's cube-chain category `Ch(K)` and its properties. The purpose of the Repo is to do research on cubes, not to build something you should actually reference from other developments.

## Results
The main result is to extend `Ch(K)` to a complexified version, call it Ch*(K) (ConcCat(K) in the repo), in the spirit of salvetti's theorem. Like Salvetti's theorem, while the invariant in the `Configuration Spaces` paper trivializes on sculptural sets, this complexified invariant does not collapse!

The construction goes as follows:

1. For any Bipointed Precubical Set (BPSet), we can define `IsRun` on a chain `\/a -> K` as `a` having all `1`s. Then we can define `Run(K) := IsRun.FullSubcategory`, that is, the full subcategory of `Ch(K)` whose domains are 1-dimensional. We can define for `K`, the set of EdgeChains, that is sequences of 1-cells in K which form a sequence. Unsurprisingly, these agree with the definition of Run
2. Now, let's think of Precubical as the presheaf topos on Box here. Any precubical map of cubes `[]n -> []m` corresponds to a face map by yoneda, coming from the Box category. That face map has a corresponding projection: a degenerecy not present in Precubical. However, that degenerecy induces a function `f:([]n -> []m) -> (EdgeChain m -> EdgeChain n)` by projecting the chain along the face. f turns out to satisfy composition and id laws! So we get a functor Box=>Type, exactly an element of Precubical! We call it `runPresheaf`. Moreover, this thing has a single basepoint.
3. A bit of general machinery in WedgeHom.lean, any such presheaf P, with a unique 0-cell induces an equivalence 
     ((⋁a).toPsh ⟶ P) ≃ ∏ᵢ P.obj (op ▫aᵢ)
   That is, maps into P split over the wedges uniformly. This is yoneda shenanigans, plus the fact that the gluings are forced at the junction points. The upshot here is that it means runPresheaf is a classifier for Runs of wedges.
4. So, we can use the inherited monoidal functors to lift a `([]m -> []n) -> Run n -> Run m` to wedges in both the inputs and the outputs, 
   giving us a `runRestrict : (\/a -> \/b) -> Run (\/b) -> Run(\/ a)`. Essentialy just propagating the projection maps along each coordinate, respecting the monoidal wedge structure the whole way (Runs.Lean)
5. Then we lift it once more to general precubical sets. We define Lines : Precubical => Type sending 
      K => objects of Run(K)
      (f : \/a -> \/b) => runRestrict f
    Interestingly, we don't use the fact that `f` commutes the maps into K here.
    Instead, we build Ch*(K) := (Lines K).Elements, the category of elements for Lines.
      objects : Pairs of ((a, f : \/a -> K), \/[1,...,1] -> \/ a)
      morphisms are those from Ch in the first coordinate, and in the second it's "compatible paths by coordinates"
Now, a few observations from here. Firstly, Lines coincides perfectly with the `Topes` functor from the Salvetti world. That is, sending faces of arrangements to adjacent topes, with the "Paris Ordering". That gives us
> The salvetti complex Sal(braidCOM n) ~ Ch*(cube n)

So, by salvetti's theorem,
> The salvetti complex pi_1|Sal(braidCOM n)| ~pi_1|Ch*(cube n)|

Note that we generally use `FreeGroupoid` instead of pi_1, nerve, and geometric realization for ease of computation.
And because mathlib's support for homotopy limits is missing.

Ch*(cube n) also has a Sigma_n free action, so using the covering machinery, and the 5 lemma
> pi_1|Ch*(cube n)/Sigma_n| = braids

Even better, the construction for the braid trick is reproducible from the Ch* side _without_ going through the Sal machinery. Essentially, every morphism of Ch*(K) is a permutation identifying where two runs disagree. These cannot disagree in the same place twice, so we get composability in the _Garside Germ Presentation_ of the braid group. Which gives us a functor

> ConcPos: Ch*(K) => Braid
> Conc: FreeGroupoid(Ch*(K)) => Braid

From here we build an _injection_ from braids into pi_1|Ch*(Z)|, the final precubical object. However, we have also verified that pi_1|Ch*(Z)| is strictly bigger than Braid. So there is something interesting happening here.

## Testing
We also get the feature that `Conc` is computable, so we can perform verified computations on what groups give which things. For example, we verify that the boundary of (cube 3) gives the center of the braid group. So the functor is at least a little sensitive to the topology. 

## Axioms
We to take Salvetti's theorem as an axiom: we build a map `pi_1|Sal(braid arrangement)| -> Pure Braids`, and assert that it is injective. We prove surjectivity by hand so avoid a non-computable existential in an axiom.

## AI Usage
Let's be real, claude wrote the vast majority of this slop. We're in the middle of unslopping it. It's going well, but it's rough out there.
