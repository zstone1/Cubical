import CubeChains.Testing.H.Merges
import CubeChains.Machinery.Cube.SymPresheaf

/-!
# Testing/H/HTwo — `Ch (H² K)` and its localization at the bead merges

`H`'s restriction is `(σ, y) ↦ (sortPerm (J g) σ, K.map (sortFace (J g) σ) y)`, and on a face
freeing the coordinate set `T` that reads `σ ↦ pattern σ T` (the rank map of `σ` on `T`), with the
new free set `imageOf σ T` — checked against `SHom.sortPerm`/`sortFace` in `sortCheck`.  Composing
it with itself gives `H²`: `(σ, τ) ↦ (pattern σ (imageOf τ T), pattern τ T)`, and *in the sheared
coordinates* `(σ ∘ τ, τ)` the two factors move independently, i.e. `H² K ≅ H K × H 1`.

So an object of `Ch⋆(Hbp K)` is an execution of `K` — its **total** run `σ ∘ τ` — plus one shear
`τ` per bead, and an arrow cuts each coarse bead's ⋆-steps into an ordered set partition.

Not built by `lake build CubeChains`.
-/

open CategoryTheory Opposite StdCube

namespace CubeChains

variable {n : ℕ}

/-! ## The restriction rule, and its validation against `SHom` -/

/-- The rank map of the one-line word `s` on the coordinate set `T` — the candidate for
`SHom.sortPerm (J.map g) σ` where `g` frees exactly `T`. -/
def pattern (s T : List ℕ) : List ℕ :=
  let v := T.map fun i => s.getD i 0
  v.map fun x => v.countP (· < x)

/-- The image of `T` under `s`, increasing — the candidate for the free set of
`SHom.sortFace (J.map g) σ`. -/
def imageOf (s T : List ℕ) : List ℕ :=
  let v := T.map fun i => s.getD i 0
  (List.range s.length).filter (v.contains ·)

/-- One-line word ↦ `Equiv.Perm (Fin d)`; the identity when the word is not a permutation. -/
def permOfList (d : ℕ) (l : List ℕ) : Equiv.Perm (Fin d) :=
  let wrap : Fin d → ℕ → Fin d := fun i k =>
    ⟨k % d, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩
  let f : Fin d → Fin d := fun i => wrap i (l.getD i 0)
  let g : Fin d → Fin d := fun j => wrap j (l.idxOf (j : ℕ))
  if h : (∀ i, g (f i) = i) ∧ (∀ j, f (g j) = j) then ⟨f, g, h.1, h.2⟩ else Equiv.refl _

/-- The box map `▫k ⟶ ▫d` freeing exactly the coordinates `T`. -/
def faceOf (d k : ℕ) (T : List ℕ) : Option (▫k ⟶ ▫d) :=
  let v : Fin d → Option Bool := fun j => if (j : ℕ) ∈ T then none else some false
  if h : (noneSet v).card = k then some (Box.ofSign ⟨v, h⟩) else none

/-- Increasing sublists of `range d` of length `k`. -/
def subsetsOf (d k : ℕ) : List (List ℕ) := (List.range d).sublists.filter (·.length == k)

/-- The faces of `▫d`: each free coordinate set, tagged with its size. -/
def faceCases (d : ℕ) : List (ℕ × List ℕ) :=
  (List.range (d + 1)).flatMap fun k => (subsetsOf d k).map (k, ·)

/-- Fold over every face of `▫d` and every ordered pair of one-line words on `Fin d`. -/
def foldCases {α : Type} (d : ℕ) (f : α → ℕ → List ℕ → List ℕ → List ℕ → α) (init : α) : α :=
  let ps := (List.range d).permutations
  (faceCases d).foldl (fun acc kT =>
    ps.foldl (fun acc sl => ps.foldl (fun acc tl => f acc kT.1 kT.2 sl tl) acc) acc) init

/-- `⟨sortPerm mismatches, sortFace mismatches⟩` over every `σ ∈ S_d` and every face of `▫d`. -/
def sortCheck (d : ℕ) : ℕ × ℕ :=
  (faceCases d).foldl (fun acc kT =>
    match faceOf d kT.1 kT.2 with
    | none => (acc.1 + 1, acc.2)
    | some φ => ((List.range d).permutations).foldl (fun acc sl =>
        let σ := permOfList d sl
        let sp := (List.finRange kT.1).map fun i => ((SHom.sortPerm (J.map φ) σ i : Fin kT.1) : ℕ)
        let sf := (List.finRange kT.1).map fun i =>
          ((faceEmb (SHom.sortFace (J.map φ) σ) i : Fin d) : ℕ)
        ((if sp == pattern sl kT.2 then acc.1 else acc.1 + 1),
         (if sf == imageOf sl kT.2 then acc.2 else acc.2 + 1))) acc) (0, 0)

/-! ## `H²`, and the shear -/

/-- `σ ∘ τ` on one-line words. -/
def compL (s t : List ℕ) : List ℕ := t.map fun i => s.getD i 0

/-- The `H²`-restriction of `(σ, τ)` along the face freeing `T`, with the new free set. -/
def h2Restrict (s t T : List ℕ) : List ℕ × List ℕ × List ℕ :=
  let t' := pattern t T
  let T' := imageOf t T
  (pattern s T', t', imageOf s T')

/-- `⟨μ-mismatches, free-set mismatches, unit `τ = 1` mismatches, unit `σ = 1` mismatches⟩` —
`μ : H² ⟶ H` is `(σ, τ) ↦ σ ∘ τ` and the two units are `τ = 1` and `σ = 1`. -/
def shearCheck (d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  foldCases d (fun acc k T sl tl =>
    let r := h2Restrict sl tl T
    let p := compL sl tl
    ((if compL r.1 r.2.1 == pattern p T then acc.1 else acc.1 + 1),
     (if r.2.2 == imageOf p T then acc.2.1 else acc.2.1 + 1),
     (if (h2Restrict sl (List.range d) T).2.1 == List.range k then acc.2.2.1
        else acc.2.2.1 + 1),
     (if (h2Restrict (List.range d) tl T).1 == List.range k then acc.2.2.2
        else acc.2.2.2 + 1))) (0, 0, 0, 0)

/-! ## `H²`'s restriction is not the naive one

`pattern σ (imageOf τ T)`, not `pattern σ T`: the outer order twists the face the inner pair
restricts along.  The naive rule agrees at `d ≤ 2` and fails from `d = 3`. -/

/-- Arguments on which the naive (untwisted) rule `σ ↦ pattern σ T` differs from `H²`'s. -/
def twistWitnesses (d : ℕ) : ℕ :=
  foldCases d (fun acc _ T sl tl =>
    if (h2Restrict sl tl T).1 == pattern sl T then acc else acc + 1) 0

/-! ## `Ch⋆(Hbp K)`

An object is an execution of `K` — the **total** run `σ ∘ τ`, bead by bead — together with the
shear `τ` of each bead; an arrow cuts each coarse bead's ⋆-steps into an ordered set partition,
the same datum as a `Ch⋆(K)` arrow, and the fine shears are then forced. -/

/-- An object: the execution's beads, and one shear word per bead. -/
abbrev HObj (n : ℕ) := List (List (Fin n)) × List (List ℕ)

/-- The permutations of `Fin k`, as one-line words. -/
def permsOf (k : ℕ) : List (List ℕ) := (List.range k).permutations

/-- The objects of `Ch⋆(Hbp K)`. -/
def hobjs (K : SubCube n) : List (HObj n) :=
  (execs K).flatMap fun X =>
    (cartesian (X.1.map fun b => permsOf b.length)).map fun ds => (X.1, ds)

/-- The shears the refinement `ys` of `bs` forces, given the coarse shears `ds`. -/
def inducedDeco (bs : List (List (Fin n))) (ds : List (List ℕ))
    (ys : List (List (Fin n))) : List (List ℕ) :=
  ((bs.zip ds).zip (groupBeads bs ys)).flatMap fun p =>
    p.2.map fun q => pattern p.1.2 (q.map fun x => p.1.1.idxOf x)

/-- The arrows of `Ch⋆(Hbp K)`, identities included. -/
def harrows (K : SubCube n) : List (HObj n × HObj n) :=
  let xs := execs K
  (hobjs K).flatMap fun o =>
    (xs.filter fun Y => refinesB o.1 Y.1).map fun Y => (o, (Y.1, inducedDeco o.1 o.2 Y.1))

/-! ### Validation -/

/-- Identities act as identities, and the shear rule is functorial: over every composable
`X ⟶ Y ⟶ Z` of `Ch⋆(K)` and every coarse shear, `⟨identity failures, composition failures⟩`. -/
def decoCheck (K : SubCube n) : ℕ × ℕ :=
  let xs := execs K
  (hobjs K).foldl (fun acc o =>
    let acc := if inducedDeco o.1 o.2 o.1 == o.2 then acc else (acc.1 + 1, acc.2)
    xs.foldl (fun acc Y => if refinesB o.1 Y.1 then
        let dY := inducedDeco o.1 o.2 Y.1
        xs.foldl (fun acc Z => if refinesB Y.1 Z.1 then
            (if inducedDeco Y.1 dY Z.1 == inducedDeco o.1 o.2 Z.1 then acc
              else (acc.1, acc.2 + 1))
          else acc) acc
      else acc) acc) (0, 0)

/-- The `H`-word of a bead: `W (τ i) = U i`, i.e. the total run re-indexed by the shear. -/
def hword (U : List (Fin n)) (t : List ℕ) : List (Fin n) :=
  ((t.zip U).mergeSort fun a b => a.1 ≤ b.1).map Prod.snd

/-- Reading a fine bead's `H`-word off the coarse one (`W` restricted to `imageOf τ P`) must give
the same word as reading it off the fine total run — the shear identity, on the model. -/
def hwordCheck (K : SubCube n) : ℕ :=
  let xs := execs K
  (hobjs K).foldl (fun acc o =>
    xs.foldl (fun acc Y => if refinesB o.1 Y.1 then
        let dY := inducedDeco o.1 o.2 Y.1
        let fine := (Y.1.zip dY).map fun q => hword q.1 q.2
        let coarse := ((o.1.zip o.2).zip (groupBeads o.1 Y.1)).flatMap fun p =>
          let W := hword p.1.1 p.1.2
          p.2.map fun q =>
            let Q := imageOf p.1.2 (q.map fun x => p.1.1.idxOf x)
            (W.zipIdx.filter fun z => Q.contains z.2).map Prod.fst
        if fine == coarse then acc else acc + 1
      else acc) acc) 0

/-- The `τ = 1` locus is closed under refinement and is `Ch⋆(K)` — the unit `K ⟶ H K ⟶ H² K`. -/
def unitCheck (K : SubCube n) : ℕ :=
  let xs := execs K
  xs.foldl (fun acc X =>
    let ids := X.1.map fun b => List.range b.length
    xs.foldl (fun acc Y => if refinesB X.1 Y.1 then
        (if inducedDeco X.1 ids Y.1 == Y.1.map (fun b => List.range b.length) then acc
          else acc + 1)
      else acc) acc) 0

/-! ## The categories under test, as index data

`W` is the class whose wedge map is a canonical cut (`isMono`/`inW` of `Testing/H/Merges`), i.e.
whose crossing permutation is trivial — so the **degree** below, the Coxeter length of that
permutation, vanishes exactly on `W` and is additive (`permOf_noDoubleCross`). -/

/-- The Coxeter length of the crossing permutation of `bs ⟶ ys`: how many pairs the refinement
re-orders. -/
def degOf (bs ys : List (List (Fin n))) : ℕ :=
  let u := bs.flatten
  let v := ys.flatten
  let p := u.map fun d => v.idxOf d
  (p.zipIdx.map fun a => (p.zipIdx.countP fun b => a.2 < b.2 && b.1 < a.1)).sum

/-- A finite thin category with an additive degree, as index data. -/
structure FinLoc where
  /-- number of objects -/
  size : ℕ
  /-- `out[a]` — every arrow out of `a`, as `(target, degree)`; identities included. -/
  out : Array (List (ℕ × ℕ))

/-- Index a list of objects and its arrow function. -/
def mkLoc {α : Type} [BEq α] [Hashable α] (objs : List α)
    (arrowsOf : α → List (α × ℕ)) : FinLoc :=
  let idx : Std.HashMap α ℕ := objs.zipIdx.foldl (fun m p => m.insert p.1 p.2) ∅
  { size := objs.length
    out := objs.foldl (fun A x =>
      A.push ((arrowsOf x).map fun q => (idx.getD q.1 0, q.2))) #[] }

/-- `Ch⋆(K)` — the `H`-level category (`Ch (Hbp K) ≌ (Ch⋆ K)ᵒᵖ`). -/
def chStarLoc (K : SubCube n) : FinLoc :=
  let xs := (execs K).map Subtype.val
  mkLoc xs fun bs => (xs.filter (refinesB bs ·)).map fun ys => (ys, degOf bs ys)

/-- `Ch⋆(Hbp K)` — the `H²`-level category (`Ch (Hbp² K) ≌ (Ch⋆ (Hbp K))ᵒᵖ`). -/
def hStarLoc (K : SubCube n) : FinLoc :=
  let xs := (execs K).map Subtype.val
  mkLoc (hobjs K) fun o =>
    (xs.filter (refinesB o.1 ·)).map fun ys => ((ys, inducedDeco o.1 o.2 ys), degOf o.1 ys)

/-- The concatenated `H`-word of an object — the decoration the ⋆-run is a shear of. -/
def hwordAll (o : HObj n) : List (List (Fin n)) := (o.1.zip o.2).map fun q => hword q.1 q.2

/-- `Ch⋆(Hbp K)` graded by the **pair** of crossing permutations, ⋆-run and `H`-word.  This is the
stricter reading of "canonical cut": a merge is canonical when *both* words concatenate, not only
the ⋆-run the wedge map records. -/
def hStarLoc2 (K : SubCube n) : FinLoc :=
  let xs := (execs K).map Subtype.val
  mkLoc (hobjs K) fun o =>
    (xs.filter (refinesB o.1 ·)).map fun ys =>
      let o' : HObj n := (ys, inducedDeco o.1 o.2 ys)
      (o', degOf o.1 ys + degOf (hwordAll o) (hwordAll o'))

/-- Objects of `chStarLoc K` that survive in `∂□ⁿ` — those with more than one bead. -/
def chSubBdry (K : SubCube n) : ℕ → Bool :=
  let A := ((execs K).map fun X => decide (1 < X.1.length)).toArray
  fun i => A.getD i false

/-- Objects of `hStarLoc K` that survive in `∂□ⁿ`. -/
def hSubBdry (K : SubCube n) : ℕ → Bool :=
  let A := ((hobjs K).map fun o => decide (1 < o.1.length)).toArray
  fun i => A.getD i false

/-! ## Invariants of the localization

Inverting `W` makes every object isomorphic to the terminal object of its `W`-component, and
`C` is thin, so `C[W⁻¹]` is presented by: objects the `W`-components, one generator `g f` per
arrow `f` (the identity when `deg f = 0`), and `g (f ≫ h) = g h ∘ g f`.  The degree is additive
and vanishes exactly on `W`, so the presented category is `ℕ`-graded and its degree-`ℓ` part is
finite; degree `0` is the identities and degree `1` is the degree-`1` arrows modulo pre- and
post-composition with `W`. -/

/-- Union–find root, with fuel. -/
def ufFind (p : Array ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => let y := p.getD x x; if y == x then x else ufFind p k y

def ufUnion (fuel : ℕ) (p : Array ℕ) (a b : ℕ) : Array ℕ :=
  let ra := ufFind p fuel a
  let rb := ufFind p fuel b
  if ra == rb then p else p.set! ra rb

/-- The `W`-component of each object — the iso classes of `C[W⁻¹]`. -/
def countDistinct (l : List ℕ) : ℕ := l.eraseDups.length

def compsOf (L : FinLoc) : Array ℕ :=
  let p0 : Array ℕ := (List.range L.size).toArray
  let p := (List.range L.size).foldl (fun p a =>
    (L.out.getD a []).foldl (fun p q => if q.2 == 0 then ufUnion L.size p a q.1 else p) p) p0
  let roots := (List.range L.size).map fun a => ufFind p L.size a
  let rank : Std.HashMap ℕ ℕ := roots.eraseDups.zipIdx.foldl (fun M q => M.insert q.1 q.2) ∅
  roots.foldl (fun A r => A.push (rank.getD r 0)) #[]

/-- Every `W`-component must have a terminal object (its maximal cut) — that is what makes the
presentation below correct.  Counts the components without one. -/
def terminalGaps (L : FinLoc) : ℕ :=
  let comp := compsOf L
  let m := countDistinct comp.toList
  let has : Std.HashSet ℕ := (List.range L.size).foldl (fun S a =>
    (L.out.getD a []).foldl (fun S q => if q.2 == 0 then S.insert (a * L.size + q.1) else S) S) ∅
  (List.range m).countP fun c =>
    let mem := (List.range L.size).filter fun a => comp.getD a 0 == c
    !mem.any fun t => mem.all fun a => has.contains (a * L.size + t)

/-- Composable pairs on which the degree fails to be additive — the grading needs `0`. -/
def degGaps (L : FinLoc) : ℕ :=
  let d : Std.HashMap ℕ ℕ := (List.range L.size).foldl (fun M a =>
    (L.out.getD a []).foldl (fun M q => M.insert (a * L.size + q.1) q.2) M) ∅
  (List.range L.size).foldl (fun acc a =>
    (L.out.getD a []).foldl (fun acc f =>
      (L.out.getD f.1 []).foldl (fun acc h =>
        if d.getD (a * L.size + h.1) 0 == f.2 + h.2 then acc else acc + 1) acc) acc) 0

/-- `⟨objects, arrows, `W`-arrows, iso classes of `C[W⁻¹]`, arrows by degree⟩`. -/
def locCounts (L : FinLoc) : ℕ × ℕ × ℕ × ℕ × List ℕ :=
  let arrs := (List.range L.size).flatMap fun a => (L.out.getD a []).map fun q => (a, q.1, q.2)
  let maxd := arrs.foldl (fun m t => max m t.2.2) 0
  (L.size, arrs.length - L.size, (arrs.countP fun t => t.2.2 == 0) - L.size,
    countDistinct (compsOf L).toList,
    (List.range (maxd + 1)).map fun d => arrs.countP fun t => t.2.2 == d)

/-! ### The graded hom-sets

The presentation's letters are the positive-degree arrows modulo pre- and post-composition with
`W` (`g f = g (u ≫ f) = g (f ≫ u)` for `u ∈ W`, by thinness), and its only relations are
`g (f ≫ h) = g h ∘ g f`.  Both preserve degree, so the degree-`ℓ` part is the finite set of
letter-words of total degree `ℓ` modulo one rewrite `[A, B] ↦ [C]` per composable pair — an
honest, exact count of `Hom` in each degree. -/

/-- The letters: positive-degree arrows of degree `≤ maxDeg`, modulo `W` on either side. -/
structure Letters where
  /-- number of classes -/
  size : ℕ
  /-- the classified arrows, as `(source, target, degree)` -/
  arr : Array (ℕ × ℕ × ℕ)
  /-- the union–find root of each arrow of `arr` -/
  roots : List ℕ
  /-- `(source component, target component, degree)` of each class -/
  info : Array (ℕ × ℕ × ℕ)
  /-- the class of the arrow `a ⟶ b` -/
  cls : Std.HashMap ℕ ℕ

def mkLetters (L : FinLoc) (maxDeg : ℕ) : Letters :=
  let comp := compsOf L
  let arr : Array (ℕ × ℕ × ℕ) := (List.range L.size).foldl (fun A a =>
    (L.out.getD a []).foldl (fun A q =>
      if 1 ≤ q.2 && q.2 ≤ maxDeg then A.push (a, q.1, q.2) else A) A) #[]
  let m := arr.size
  let ix : Std.HashMap ℕ ℕ := (List.range m).foldl (fun M i =>
    let e := arr.getD i (0, 0, 0); M.insert (e.1 * L.size + e.2.1) i) ∅
  let join : Array ℕ → ℕ → ℕ → Array ℕ := fun p a b =>
    match ix[a]?, ix[b]? with
    | some i, some j => ufUnion m p i j
    | _, _ => p
  let p0 : Array ℕ := (List.range m).toArray
  let p := (List.range L.size).foldl (fun p x =>
    (L.out.getD x []).foldl (fun p u =>
      if u.2 == 0 && u.1 != x then
        (L.out.getD u.1 []).foldl (fun p h =>
          if 1 ≤ h.2 && h.2 ≤ maxDeg then
            join p (u.1 * L.size + h.1) (x * L.size + h.1) else p) p
      else p) p) p0
  let p := (List.range L.size).foldl (fun p x =>
    (L.out.getD x []).foldl (fun p h =>
      if 1 ≤ h.2 && h.2 ≤ maxDeg then
        (L.out.getD h.1 []).foldl (fun p u =>
          if u.2 == 0 && u.1 != h.1 then
            join p (x * L.size + h.1) (x * L.size + u.1) else p) p
      else p) p) p
  let roots := (List.range m).map fun i => ufFind p m i
  let rank : Std.HashMap ℕ ℕ := roots.eraseDups.zipIdx.foldl (fun M q => M.insert q.1 q.2) ∅
  { size := roots.eraseDups.length
    arr := arr
    roots := roots
    info := roots.eraseDups.toArray.map fun r =>
      let e := arr.getD r (0, 0, 0); (comp.getD e.1 0, comp.getD e.2.1 0, e.2.2)
    cls := (List.range m).foldl (fun M i =>
      let e := arr.getD i (0, 0, 0)
      M.insert (e.1 * L.size + e.2.1) (rank.getD (roots.getD i 0) 0)) ∅ }

/-- The degree-`1` arrows of `L`, and the class of each: the letters at `maxDeg = 1`. -/
def deg1Roots (L : FinLoc) : Array (ℕ × ℕ) × List ℕ :=
  let Le := mkLetters L 1
  (Le.arr.map fun e => (e.1, e.2.1), Le.roots)

/-- `⟨degree-1 arrows, classes, classes out of each component, classes between each ordered pair of
components⟩`, the last two sorted. -/
def deg1Data (L : FinLoc) : ℕ × ℕ × List ℕ × List ℕ :=
  let comp := compsOf L
  let (d1, roots) := deg1Roots L
  let reps := roots.eraseDups
  let srcOf : ℕ → ℕ := fun r => comp.getD (d1.getD r (0, 0)).1 0
  let tgtOf : ℕ → ℕ := fun r => comp.getD (d1.getD r (0, 0)).2 0
  (d1.size, reps.length,
    ((reps.map fun r => srcOf r).eraseDups.map fun c =>
      (reps.countP fun r => srcOf r == c)).mergeSort (· ≤ ·),
    ((reps.map fun r => srcOf r * L.size + tgtOf r).eraseDups.map fun c =>
      (reps.countP fun r => srcOf r * L.size + tgtOf r == c)).mergeSort (· ≤ ·))

/-- The degree-`1` classes of `L` containing **no** arrow whose source satisfies `sub`.  If `0`,
the full subcategory on `sub` is already degree-`1` full in `L[W⁻¹]`, hence — once `L[W⁻¹]` is
generated in degree `1` — full in every degree. -/
def deg1Missed (L : FinLoc) (sub : ℕ → Bool) : ℕ :=
  let (d1, roots) := deg1Roots L
  let hit : Std.HashSet ℕ := (List.range d1.size).foldl (fun S i =>
    if sub (d1.getD i (0, 0)).1 then S.insert (roots.getD i 0) else S) ∅
  roots.eraseDups.countP fun r => !hit.contains r

/-- `[A, B] ↦ [C]`, one entry per composable pair of positive degree. -/
def relsOf (L : FinLoc) (Le : Letters) (maxDeg : ℕ) : Std.HashMap ℕ (List ℕ) :=
  (List.range L.size).foldl (fun M x =>
    (L.out.getD x []).foldl (fun M f =>
      if 1 ≤ f.2 && f.2 < maxDeg then
        (L.out.getD f.1 []).foldl (fun M h =>
          if 1 ≤ h.2 && f.2 + h.2 ≤ maxDeg then
            let A := Le.cls.getD (x * L.size + f.1) 0
            let B := Le.cls.getD (f.1 * L.size + h.1) 0
            let C := Le.cls.getD (x * L.size + h.1) 0
            let k := A * Le.size + B
            let cur := M.getD k []
            if cur.contains C then M else M.insert k (C :: cur)
          else M) M
      else M) M) ∅

/-- Letter-words of total degree `d` starting at the component `c`; the fuel bounds the length. -/
def wordsOf (Le : Letters) (byStart : Array (List ℕ)) : ℕ → ℕ → ℕ → List (List ℕ)
  | _, 0, _ => [[]]
  | 0, _, _ => []
  | f + 1, d, c => (byStart.getD c []).flatMap fun i =>
      let e := Le.info.getD i (0, 0, 0)
      if 1 ≤ e.2.2 && e.2.2 ≤ d then
        (wordsOf Le byStart f (d - e.2.2) e.2.1).map (i :: ·)
      else []

/-- `⟨words, morphism classes, classes with no all-degree-one word⟩` in degree `d`, counting only
the morphisms out of the components `cs`.  Rewrites never leave the source component, so one
component's words are a self-contained union–find. -/
def homData (L : FinLoc) (maxDeg d : ℕ) (cs : List ℕ) : ℕ × ℕ × ℕ :=
  let comp := compsOf L
  let ncomp := countDistinct comp.toList
  let Le := mkLetters L maxDeg
  let rels := relsOf L Le maxDeg
  let B := Le.size + 1
  let key : List ℕ → ℕ := fun w => w.foldl (fun k i => k * B + (i + 1)) 0
  let byStart : Array (List ℕ) := (List.range Le.size).foldl
    (fun A i => A.modify (Le.info.getD i (0, 0, 0)).1 (i :: ·)) (Array.replicate ncomp [])
  let ws := (cs.flatMap fun c => wordsOf Le byStart d d c).toArray
  let N := ws.size
  let idx : Std.HashMap ℕ ℕ :=
    (List.range N).foldl (fun M i => M.insert (key (ws.getD i [])) i) ∅
  let p := (List.range N).foldl (fun p q =>
    let w := ws.getD q []
    (List.range (w.length - 1)).foldl (fun p i =>
      let A := w.getD i 0
      let C := w.getD (i + 1) 0
      (rels.getD (A * Le.size + C) []).foldl (fun p E =>
        match idx[key (w.take i ++ E :: w.drop (i + 2))]? with
        | some j => ufUnion N p q j
        | none => p) p) p) ((List.range N).toArray)
  let good : Std.HashSet ℕ := (List.range N).foldl (fun S q =>
    if (ws.getD q []).all fun i => (Le.info.getD i (0, 0, 0)).2.2 == 1 then
      S.insert (ufFind p N q) else S) ∅
  let reps := ((List.range N).map (ufFind p N ·)).eraseDups
  (N, reps.length, reps.countP fun r => !good.contains r)

def homCountAt (L : FinLoc) (maxDeg d : ℕ) : ℕ × ℕ :=
  let r := homData L maxDeg d (List.range (countDistinct (compsOf L).toList))
  (r.1, r.2.1)

/-- `Hom` of `C[W⁻¹]` in each degree `0, …, maxDeg`, summed over all source objects. -/
def gradedHoms (L : FinLoc) (maxDeg : ℕ) : List ℕ :=
  (List.range (maxDeg + 1)).map fun d => (homCountAt L d d).2

/-- `Hom` in a single degree — the only one whose cost matters. -/
def gradedHomAt (L : FinLoc) (d : ℕ) : ℕ × ℕ := homCountAt L d d

/-- The number of letters of each degree `1, …, maxDeg`. -/
def letterCounts (L : FinLoc) (maxDeg : ℕ) : List ℕ :=
  let Le := mkLetters L maxDeg
  (List.range maxDeg).map fun d =>
    (List.range Le.size).countP fun i => (Le.info.getD i (0, 0, 0)).2.2 == d + 1

/-- Is every degree-`d` morphism a product of degree-`1` ones?  Reports, per degree, the number of
classes containing **no** word all of whose letters have degree `1`. -/
def genGaps (L : FinLoc) (maxDeg : ℕ) : List ℕ :=
  let cs := List.range (countDistinct (compsOf L).toList)
  (List.range (maxDeg + 1)).map fun d => (homData L d d cs).2.2

/-! ### The positive braid monoid, for calibration

`B n⁺` presented on `σ 1, …, σ (n-1)`: the reference growth series against which the `H`-level
localization is read. -/

/-- The number of elements of `B n⁺` of each length `0, …, maxLen`. -/
def braidGrowth (n maxLen : ℕ) : List ℕ :=
  let gens := List.range (n - 1)
  (List.range (maxLen + 1)).map fun d =>
    let ws := (List.range d).foldl
      (fun acc _ => acc.flatMap fun w => gens.map (· :: w)) [([] : List ℕ)]
    let N := ws.length
    let idx : Std.HashMap (List ℕ) ℕ := ws.zipIdx.foldl (fun M q => M.insert q.1 q.2) ∅
    let p := ws.zipIdx.foldl (fun p q =>
      let w := q.1
      let p := (List.range (max 1 w.length - 1)).foldl (fun p i =>
        let a := w.getD i 0
        let b := w.getD (i + 1) 0
        if a + 2 ≤ b || b + 2 ≤ a then
          match idx[w.take i ++ b :: a :: w.drop (i + 2)]? with
          | some j => ufUnion N p q.2 j
          | none => p
        else p) p
      (List.range (max 2 w.length - 2)).foldl (fun p i =>
        let a := w.getD i 0
        let b := w.getD (i + 1) 0
        let c := w.getD (i + 2) 0
        if a == c && (a + 1 == b || b + 1 == a) then
          match idx[w.take i ++ b :: a :: b :: w.drop (i + 3)]? with
          | some j => ufUnion N p q.2 j
          | none => p
        else p) p) ((List.range N).toArray)
    countDistinct ((List.range N).map (ufFind p N ·))


/-! ## The verdict

`Ch (Hbp K) ≌ (Ch⋆ K)ᵒᵖ` and `Ch (Hbp² K) ≌ (Ch⋆ (Hbp K))ᵒᵖ`, and localizing commutes with
`(-)ᵒᵖ`, so both comparisons are read on the `Ch⋆` side. -/

/-! ### The model

`pattern`/`imageOf` **are** `SHom.sortPerm`/`sortFace`; `μ : H² ⟶ H` and both units behave; and
the twist that separates `H²` from `H × H` is invisible at `d ≤ 2`. -/

#eval (sortCheck 2, sortCheck 3, sortCheck 4)                   -- ((0,0), (0,0), (0,0))
#eval (shearCheck 2, shearCheck 3, shearCheck 4)                -- all zero
#eval (twistWitnesses 2, twistWitnesses 3, twistWitnesses 4)    -- (0, 32, 2488)
#eval (decoCheck (SubCube.full 3), hwordCheck (SubCube.full 3), unitCheck (SubCube.full 4))
                                                                -- ((0,0), 0, 0)
#eval (((hobjs (SubCube.full 4)).length, (harrows (SubCube.full 4)).length),
       ((hobjs (SubCube.boundary 4)).length, (harrows (SubCube.boundary 4)).length))
              -- ⟨Σ_chains ∏ (dⱼ!)², Σ_chains ∏ (dⱼ!)² Fub dⱼ⟩ = ((1128, 48264), (552, 5064))

/-! Both levels are legible: every `W`-component has a terminal object (its maximal cut), so the
presentation `gradedHoms` runs on **is** the localization; and the degree is additive, so the
`W`-components are exactly the iso classes. -/

#eval (terminalGaps (chStarLoc (SubCube.full 4)), terminalGaps (chStarLoc (SubCube.boundary 4)),
       terminalGaps (hStarLoc (SubCube.full 4)), terminalGaps (hStarLoc (SubCube.boundary 4)))
                                                                -- (0, 0, 0, 0)
#eval (degGaps (chStarLoc (SubCube.full 4)), degGaps (hStarLoc (SubCube.full 4)))  -- (0, 0)

/-! ### Calibration at `n = 3`, where the top cell *is* seen

`Ch⋆(□³)[W⁻¹]` is `6 ×` the growth of `B₃⁺`; `Ch⋆(∂□³)[W⁻¹]` is free on two generators per
object — the braid relation lives on the missing `3`-cell.  `H²` separates them too. -/

#eval braidGrowth 3 6                                           -- [1,2,4,7,12,20,33]
#eval (gradedHoms (chStarLoc (SubCube.full 3)) 4,
       gradedHoms (chStarLoc (SubCube.boundary 3)) 4)   -- [6,12,24,42,72] vs [6,12,24,48,96]
#eval (gradedHoms (hStarLoc (SubCube.full 3)) 3,
       gradedHoms (hStarLoc (SubCube.boundary 3)) 3)    -- [6,24,96,348] vs [6,24,96,384]

/-! ### The control: `H` at `n = 4`

`∂□⁴` drops the `24` one-bead executions, i.e. `2688 - 912` arrows and every arrow of degree
`> 3`.  Both localizations still have `24` objects, `3` degree-`1` morphisms out of each (one per
simple transposition), are generated in degree `1`, and have `24 ×` the growth series of `B₄⁺`
for their graded hom-sets — so both **are** the positive braid category on `S₄`. -/

#eval (locCounts (chStarLoc (SubCube.full 4)), locCounts (chStarLoc (SubCube.boundary 4)))
#eval (letterCounts (chStarLoc (SubCube.full 4)) 6,
       letterCounts (chStarLoc (SubCube.boundary 4)) 6)
                                    -- [72,120,144,120,72,24] vs [72,120,48,0,0,0]
#eval (genGaps (chStarLoc (SubCube.full 4)) 5, genGaps (chStarLoc (SubCube.boundary 4)) 5)
                                                                -- all zero
#eval braidGrowth 4 6                                           -- [1,3,8,19,43,94,202]
#eval gradedHoms (chStarLoc (SubCube.full 4)) 6      -- [24,72,192,456,1032,2256,4848]
#eval gradedHoms (chStarLoc (SubCube.boundary 4)) 6  -- [24,72,192,456,1032,2256,4848]

/-! ### `H²` at `n = 4`

`∂□⁴` drops `576` of the `1128` objects and `42624` of the `47136` arrows, and again every arrow
of degree `> 3`.  Both still have `24` objects and `6` degree-`1` morphisms out of each
(`2` per simple transposition), are generated in degree `1`, and agree in every degree computed. -/

#eval (locCounts (hStarLoc (SubCube.full 4)), locCounts (hStarLoc (SubCube.boundary 4)))
#eval (letterCounts (hStarLoc (SubCube.full 4)) 4,
       letterCounts (hStarLoc (SubCube.boundary 4)) 4)
                                    -- [144,672,2592,2880] vs [144,672,288,0]
#eval (genGaps (hStarLoc (SubCube.full 4)) 3, genGaps (hStarLoc (SubCube.boundary 4)) 3)
                                                                -- all zero
#eval gradedHoms (hStarLoc (SubCube.full 4)) 4       -- [24,144,768,3744,17664]
#eval gradedHoms (hStarLoc (SubCube.boundary 4)) 4   -- [24,144,768,3744,17664]


/-! ### Why the comparison is decisive

`∂□⁴ ↪ □⁴` is a full subcategory on both levels, so it induces `Ψ : Ch⋆(∂)[W⁻¹] ⟶ Ch⋆(□)[W⁻¹]`.
`Ψ` is a bijection on iso classes (both are the `24` total-run words), it hits every degree-`1`
morphism, and both sides are generated in degree `1` — so `Ψ` is full in every degree, and equal
graded counts in a degree make it bijective there.  Every relation of the presentation has degree
`deg f + deg h ≤ 6`, the top degree of an arrow, so agreement through degree `6` forces the two
congruences to coincide. -/

#eval (deg1Missed (chStarLoc (SubCube.full 4)) (chSubBdry (SubCube.full 4)),
       deg1Missed (hStarLoc (SubCube.full 4)) (hSubBdry (SubCube.full 4)))     -- (0, 0)

/-! ### The stricter reading of "canonical"

The wedge map of a `Ch (H² K)` arrow records only the **outer** order's cuts, so `isMono` is
"the ⋆-run concatenates".  Asking the `H`-word to concatenate too — the merge that is canonical
in *both* factors — is a strictly smaller `W`, and there the two localizations part company
already on their iso classes: `(4!)²` against `4! · (4! − 13)`, the missing `13` being the
indecomposable permutations of `S₄`. -/

#eval (locCounts (hStarLoc2 (SubCube.full 4)), locCounts (hStarLoc2 (SubCube.boundary 4)))

end CubeChains
