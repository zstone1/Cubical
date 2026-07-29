# Cubical

A Lean 4 + mathlib formalization of Ziemiański-Paliga's cube-chain category `Ch(K)` and its properties. The purpose of the Repo is to do research on cubes, not to build something you should actually reference from other developments.

## Results
The main result is to extend `Ch(K)` to a complexified version, call it Ch*(K), in the spirit of salvetti's theorem. Like Salvetti's theorem, while the invariant in the `Configuration Spaces` paper trivializes on sculptural sets, this complexified invariant does not collapse!

The construction goes as follows:

0. Recall that `Ch(K)` is the category of wedgemaps `\/[a_1,...,a_n] -> K`. with maps as commuting triangles over K.
1. For any Precubical Set `K`, we can define `Run(K)` as the full subcategory of `Ch(K)` of one dimensional runs: those like `[1,...,1]`. 
2. Now, let's think of Precubical as the presheaf topos on Box here. Any precubical map of cubes `[]n -> []m` corresponds to a face map by yoneda, coming from the Box category. That face map has a corresponding projection: a degenerecy not present in Precubical. However, that degenerecy induces a function `f:([]n -> []m) -> (Run m -> Run n)` by projecting the chain along the face. This turns out to be a presheaf on Box! We call it `runPresheaf`. Moreover, this thing has a single basepoint.
3. A bit of general machinery in WedgeHom.lean, any such presheaf P, with a unique 0-cell induces an equivalence 
     ((⋁a).toPsh ⟶ P) ≃ ∏ᵢ P.obj (op ▫aᵢ)
   That is, maps into P split over the wedges uniformly. This is yoneda shenanigans, plus the fact that the gluings are forced at the junction points. The upshot here is that it means runPresheaf is a classifier for Runs of wedges.
4. Then we can define a functor Lines as the composition of the forgetful $(\/a -> K) -> \/a$ and the right kan extension of the presheaf above. And then take the category of elements.
5. All this category nonsense gives us a nice category:
      objects : a pair of comosable arrow (\/[1,...,1] -> \/[a_1,...,a_n] -> K)
      morphisms: send `\/[a_1,...,a_n]  -> \/[b_1,...,b_m]` such that the one dimension parts respect the underlying projection.

Now, a few observations from here. Firstly, Lines coincides perfectly with the `Topes` functor from the Salvetti world. That is, sending faces of arrangements to adjacent topes, with the "Paris Ordering". That gives us
> The salvetti complex Sal(braidCOM n) ~ Ch*(cube n)

So, by salvetti's theorem,
> The salvetti complex pi_1|Sal(braidCOM n)| ~pi_1|Ch*(cube n)|

Even better, the construction for the braid trick is reproducible from the Ch* side _without_ going through the Sal machinery. 
Essentially, every morphism of Ch*(K) is a permutation identifying where two runs disagree. 
These cannot disagree in the same place twice, so we get composability in the _Garside Germ Presentation_ of the braid group. Which gives us a functor

> ConcPos: Ch*(K) => Braid
> Conc: FreeGroupoid(Ch*(K)) => Braid

## Testing
We have a nice computational model for Ch* as well, using Ordered Set Partitions, which we have proven equivalent. 
So we can actually compute things

## AI Usage
Let's be real, claude wrote the vast majority of this slop. We're in the middle of unslopping it. It's going well, but it's rough out there.
