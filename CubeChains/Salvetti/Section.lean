import CubeChains.Salvetti.EventBraid
import CubeChains.Salvetti.Elements
import CubeChains.Chains.Segal
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Salvetti/Section — splitting `π : Ch⋆ K ⥤ (Ch K)ᵒᵖ` at a basepoint

`π` is a discrete opfibration, so it has no canonical section: which run a chain carries is genuine
extra data, and `ConcPos` does not descend along `π`.  A section supplies that data coherently —
`Sect (Lines K)` is `lim (Lines K)` — and composing with `ConcPos` puts the concurrency braid on the
base, `(Ch K)ᵒᵖ ⥤ FullBraid`.

When the base has an initial object, i.e. `Ch K` has a terminal chain, i.e. `K` has a top cell, a
single run over it *is* a section (`Sect.equivOfInitial`): compatibility stops being a constraint
and becomes a definition.
-/

open CategoryTheory Opposite Limits BPSet CubeChain

universe w v₁ u₁

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type w)

/-- A section of `π : P.Elements ⥤ C`, as the compatible family it amounts to — a point of
`lim P`. -/
@[ext]
structure Sect where
  /-- The element chosen over each object. -/
  val : ∀ c, P.obj c
  /-- Transport along every arrow agrees with the choice downstream. -/
  compat : ∀ {c c' : C} (u : c ⟶ c'), P.map u (val c) = val c'

namespace Sect

variable {P}

/-- A section as a functor splitting `π`; `compat` is exactly the `Elements` hom condition. -/
@[simps]
def functor (s : Sect P) : C ⥤ P.Elements where
  obj c := ⟨c, s.val c⟩
  map u := ⟨u, s.compat u⟩
  map_id _ := CategoryOfElements.ext P _ _ rfl
  map_comp _ _ := CategoryOfElements.ext P _ _ rfl

/-- It really is a section — on the nose, no `eqToHom`. -/
theorem functor_comp_π (s : Sect P) : s.functor ⋙ CategoryOfElements.π P = 𝟭 C := rfl

/-- The section obtained by transporting a basepoint out of an initial object. -/
@[simps]
def ofInitial {I : C} (hI : IsInitial I) (x : P.obj I) : Sect P where
  val c := P.map (hI.to c) x
  compat u := by
    rw [← Functor.map_comp_apply, hI.hom_ext (hI.to _ ≫ u) (hI.to _)]

/-- **A basepoint is a section.**  Over an initial object every value is forced by the one at `I`,
so choosing a section is choosing a single element there. -/
@[simps]
def equivOfInitial {I : C} (hI : IsInitial I) : Sect P ≃ P.obj I where
  toFun s := s.val I
  invFun := ofInitial hI
  left_inv s := Sect.ext (funext fun c => s.compat (hI.to c))
  right_inv x := by
    change P.map (hI.to I) x = x
    rw [hI.hom_ext (hI.to I) (𝟙 I), Functor.map_id_apply]

/-- Sections pull back along any change of base. -/
@[simps]
def pullback {D : Type u₁} [Category.{v₁} D] (G : D ⥤ C) (s : Sect P) : Sect (G ⋙ P) where
  val d := s.val (G.obj d)
  compat u := s.compat (G.map u)

end Sect

end CategoryTheory

/-! ## The terminal chain

A chain is terminal as soon as its classifying map is invertible: the triangle `φ ≫ t.map = a.map`
then *solves* for `φ`.  For `□n` that chain is the top cell, `⋁[n] ≅ □n`. -/

namespace ChainCat

/-- A chain classified by an isomorphism is terminal — the triangle *solves* for the wedge map,
`φ = a.map ≫ e.inv`.  Stated on an `Iso` rather than `IsIso` so it stays computable. -/
def isTerminalOfIso {K : BPSet} {d : List ℕ+} (e : (⋁d) ≅ K) :
    IsTerminal (⟨d, e.hom⟩ : Ch K) :=
  IsTerminal.ofUniqueHom (fun a => ⟨a.map ≫ e.inv, by simp⟩)
    (fun a f => Hom.ext <| by
      change f.φ = a.map ≫ e.inv
      rw [← f.w, Category.assoc, e.hom_inv_id, Category.comp_id])

/-- The top cell of `□n` read as a one-bead chain. -/
def topChain (n : ℕ+) : Ch (□(n : ℕ)) := ⟨[n], (serialWedge1 n).hom⟩

/-- **`□n` has a terminal chain** — every chain refines the top cell, uniquely. -/
def isTerminalTopChain (n : ℕ+) : IsTerminal (topChain n) := isTerminalOfIso _

/-- …so the base of `π` has an initial object: the basepoint's home. -/
def isInitialOpTopChain (n : ℕ+) : IsInitial (op (topChain n)) := (isTerminalTopChain n).op

end ChainCat

namespace CubeChains

open ChainCat

/-- **The concurrency braid on the base.**  `ConcPos` lives on `Ch⋆ K` and does not descend; a
section carries it down. -/
def concOfSect {K : BPSet} (s : Sect (Lines K)) : (Ch K)ᵒᵖ ⥤ FullBraid :=
  s.functor ⋙ ConcPos K

/-- **One run of the top cell is a whole section.**  This is why the cube needs a basepoint and not
a coherent family: `Ch (□n)` has a terminal chain. -/
def cubeSectEquiv (n : ℕ+) :
    Sect (Lines (□(n : ℕ))) ≃ (Lines (□(n : ℕ))).obj (op (topChain n)) :=
  Sect.equivOfInitial (isInitialOpTopChain n)

/-! ## Sections restrict — a sculpture borrows the cube's basepoint

`Lines K a` is `(⋁a.dims).toPsh ⟶ runPresheaf`: it reads the *wedge*, never the classifying map.
So `pushforward f`, which alters only that map, leaves `Lines` alone, and `Sect ∘ Lines` is a
presheaf on `BPSet`.  A subcomplex of `□n` has no terminal chain of its own — it does not need one.
-/

/-- `Lines` sees only the wedge, so it is *literally* the pullback of `Lines L` along `Ch f`. -/
theorem lines_pushforward {K L : BPSet} (f : K ⟶ L) :
    (ChainCat.pushforward f).op ⋙ Lines L = Lines K := rfl

/-- **Sections restrict along any map of bi-pointed sets** (typed by `lines_pushforward`). -/
def sectRestrict {K L : BPSet} (f : K ⟶ L) (s : Sect (Lines L)) : Sect (Lines K) :=
  s.pullback (ChainCat.pushforward f).op

/-- The map on executions induced by `f`, over `Ch f` — again typed by `lines_pushforward`. -/
def chStarMap {K L : BPSet} (f : K ⟶ L) : Ch⋆ K ⥤ Ch⋆ L :=
  CategoryOfElements.pre (Lines L) (ChainCat.pushforward f).op

/-- `chStarMap` lies over `Ch f`. -/
theorem chStarMap_comp_π {K L : BPSet} (f : K ⟶ L) :
    chStarMap f ⋙ CategoryOfElements.π (Lines L)
      = CategoryOfElements.π (Lines K) ⋙ (ChainCat.pushforward f).op := rfl

/-- **The braid grading is strictly natural in `K`** — `proj` reads only the wedge and the run
classifier, and `chStarMap` touches neither. -/
theorem chStarMap_comp_concPos {K L : BPSet} (f : K ⟶ L) :
    chStarMap f ⋙ ConcPos L = ConcPos K := rfl

/-- Restricting a section is the same as transporting it across `chStarMap`. -/
theorem sectRestrict_functor {K L : BPSet} (f : K ⟶ L) (s : Sect (Lines L)) :
    (sectRestrict f s).functor ⋙ chStarMap f
      = (ChainCat.pushforward f).op ⋙ s.functor := rfl

@[simp] theorem sectRestrict_id (K : BPSet) (s : Sect (Lines K)) : sectRestrict (𝟙 K) s = s := rfl

@[simp] theorem sectRestrict_comp {K L M : BPSet} (f : K ⟶ L) (g : L ⟶ M) (s : Sect (Lines M)) :
    sectRestrict (f ≫ g) s = sectRestrict f (sectRestrict g s) := rfl

/-- **The standard section of a sculpture** `f : K ⟶ □n`: one run of the ambient top cell hands
every chain of `K` a run, coherently. -/
def stdSect {n : ℕ+} {K : BPSet} (f : K ⟶ □(n : ℕ))
    (w : (Lines (□(n : ℕ))).obj (op (topChain n))) : Sect (Lines K) :=
  sectRestrict f (Sect.ofInitial (isInitialOpTopChain n) w)

/-- The concurrency braid of a sculpture on its own base, from an ambient basepoint. -/
def sculptureConc {n : ℕ+} {K : BPSet} (f : K ⟶ □(n : ℕ))
    (w : (Lines (□(n : ℕ))).obj (op (topChain n))) : (Ch K)ᵒᵖ ⥤ FullBraid :=
  concOfSect (stdSect f w)

/-- **The sculpture's braid functor is the cube's, restricted.**  Nothing is computed downstairs
that was not already computed on `□n`. -/
theorem sculptureConc_eq {n : ℕ+} {K : BPSet} (f : K ⟶ □(n : ℕ))
    (w : (Lines (□(n : ℕ))).obj (op (topChain n))) :
    sculptureConc f w
      = (ChainCat.pushforward f).op ⋙ concOfSect (Sect.ofInitial (isInitialOpTopChain n) w) :=
  rfl

end CubeChains
