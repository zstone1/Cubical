import CubeChains.Salvetti.ConcGroupoid
import CubeChains.Salvetti.SalBraidChamberRank
import CubeChains.Schedule.Atlas
import Mathlib.Data.Prod.Lex
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Salvetti/Normalize — every execution is isomorphic to a run

A **run** is a cube chain all of whose beads are edges (`IsRun`).  `Chamber 1` is a subsingleton,
so a run carries a unique line (`runLine`) and is canonically an object of `ConcCat K`.

The **sequentialization** of an execution `(a, L)` splits every bead of `a` into its `dᵢ` edges, in
the order the chamber `L i` prescribes (bead first, then the chamber's rank — `evKey`):

      seq (a,L)  --seqRefine-->  a                     in `Ch K`     (fine ⟶ coarse)
      (a,L)      --seqHom---->   (seq (a,L), runLine)  in `ConcCat K` (coarse ⟶ fine)

The refinement is the tie-block chain of `Schedule/Atlas` (`pchain`/`prefine`) for the ordered
partition of `a`'s events into singletons given by the line; blocks are singletons, so its beads
are edges.  In `ConcGrpd K = FreeGroupoid (ConcCat K)` that morphism becomes invertible, whence

      concGrpdRunEquiv : ConcGrpd K ≌ (full subgroupoid on the runs).

Gotcha: the compatibility of `seqHom` with the chamber presheaf is *free* — the target's lines form
a subsingleton — so the chamber only chooses **which** run, never whether the square commutes.

Consequence: every 1-cell of `ConcGrpd K` is a word in the edges of `K`, so `K` is a presentation
of `ConcGrpd K` — vertices ↦ objects, edges ↦ generating 1-cells, squares ↦ generating 2-cells,
3-cubes ↦ relations.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace CubeChains

/-! ## Chambers of a `≤ 1`-dimensional cube -/

/-- The only chamber of `□ᵈ` for `d ≤ 1`: there is nothing to order. -/
def Chamber.trivial {d : ℕ} (hd : d ≤ 1) : Chamber d where
  lt _ _ := False
  sto :=
    haveI : Subsingleton (Fin d) := Fin.subsingleton_iff_le_one.mpr hd
    { trichotomous := fun a b _ _ => Subsingleton.elim a b
      irrefl := fun _ h => h
      trans := fun _ _ _ h _ => h.elim }

/-- A `≤ 1`-dimensional cube has a unique chamber. -/
theorem Chamber.subsingleton {d : ℕ} (hd : d ≤ 1) : Subsingleton (Chamber d) := by
  haveI : Subsingleton (Fin d) := Fin.subsingleton_iff_le_one.mpr hd
  refine ⟨fun c₁ c₂ => Chamber.ext (funext fun a => funext fun b => ?_)⟩
  obtain rfl : a = b := Subsingleton.elim a b
  haveI := c₁.sto
  haveI := c₂.sto
  have h₁ : ¬ c₁.lt a a := Std.Irrefl.irrefl (r := c₁.lt) a
  have h₂ : ¬ c₂.lt a a := Std.Irrefl.irrefl (r := c₂.lt) a
  simp only [eq_iff_iff]
  exact ⟨fun h => absurd h h₁, fun h => absurd h h₂⟩

/-! ## Runs -/

variable {K : BPSet}

/-- A **run**: a cube chain all of whose beads are edges (equivalently `nbeads a = dimSum a`). -/
def IsRun (a : Ch K) : Prop := ∀ i : ChainCat.Bead a, ChainCat.beadDim a i = 1

/-- The unique line of a run. -/
def runLine (a : Ch K) (h : IsRun a) : LinesObj a :=
  fun i => Chamber.trivial (le_of_eq (h i))

/-- A run has only one line. -/
theorem linesObj_subsingleton {a : Ch K} (h : IsRun a) : Subsingleton (LinesObj a) :=
  ⟨fun L L' => funext fun i => (Chamber.subsingleton (le_of_eq (h i))).elim (L i) (L' i)⟩

/-- A run, as an execution. -/
def runExec (a : Ch K) (h : IsRun a) : ConcCat K := ⟨op a, runLine a h⟩

/-! ## The rank of a finite type under an injective key

An injective key `f : α → γ` into a linear order enumerates `α`: `keyRank f` counts the strictly
smaller keys, and is a bijection onto `Fin (card α)`.  (Kept instance-free — `EventObj a` already
carries a *different* `LinearOrder` instance, `eventObjLinearOrder`.) -/

section KeyRank

variable {α : Type} [Fintype α] {γ : Type} [LinearOrder γ] (f : α → γ)

/-- The number of elements with a strictly smaller key. -/
noncomputable def keyRank (x : α) : ℕ := (Finset.univ.filter (fun y => f y < f x)).card

theorem keyRank_lt_card (x : α) : keyRank f x < Fintype.card α := by
  have hne : (Finset.univ.filter (fun y => f y < f x)) ≠ Finset.univ := by
    intro h
    have hx : x ∈ Finset.univ.filter (fun y => f y < f x) := by
      rw [h]; exact Finset.mem_univ x
    exact absurd (Finset.mem_filter.mp hx).2 (lt_irrefl _)
  have hss : (Finset.univ.filter (fun y => f y < f x)) ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr hne
  calc keyRank f x < Finset.univ.card := Finset.card_lt_card hss
    _ = Fintype.card α := Finset.card_univ

theorem keyRank_strictMono {x y : α} (h : f x < f y) : keyRank f x < keyRank f y := by
  have hsub : (Finset.univ.filter (fun z => f z < f x))
      ⊆ Finset.univ.filter (fun z => f z < f y) := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 h⟩
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ⟨x, ?_, ?_⟩)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h⟩
  · exact fun hx => absurd (Finset.mem_filter.mp hx).2 (lt_irrefl _)

theorem keyRank_injective (hf : Function.Injective f) : Function.Injective (keyRank f) := by
  intro x y h
  rcases lt_trichotomy (f x) (f y) with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (keyRank_strictMono f hlt))
  · exact hf heq
  · exact absurd h.symm (Nat.ne_of_lt (keyRank_strictMono f hgt))

/-- The key ranking is a bijection `α ≃ Fin (card α)`. -/
noncomputable def keyEquiv (hf : Function.Injective f) : α ≃ Fin (Fintype.card α) :=
  Equiv.ofBijective (fun x => (⟨keyRank f x, keyRank_lt_card f x⟩ : Fin (Fintype.card α)))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => keyRank_injective f hf (congrArg Fin.val h), by simp⟩)

@[simp] theorem keyEquiv_val (hf : Function.Injective f) (x : α) :
    ((keyEquiv f hf x : Fin (Fintype.card α)) : ℕ) = keyRank f x := rfl

end KeyRank

/-! ## The sequentialization of an execution -/

/-- The **event key** of a line: bead first, then the bead chamber's rank. -/
noncomputable def evKey {a : Ch K} (L : LinesObj a) (e : EventObj a) : ℕ ×ₗ ℤ :=
  toLex ((e.1 : ℕ), chamberRank (L e.1) e.2)

theorem evKey_injective {a : Ch K} (L : LinesObj a) : Function.Injective (evKey L) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have h1 : (i : ℕ) = (j : ℕ) := congrArg (fun p : ℕ ×ₗ ℤ => (ofLex p).1) h
  obtain rfl : i = j := Fin.ext h1
  have h2 : chamberRank (L i) x = chamberRank (L i) y :=
    congrArg (fun p : ℕ ×ₗ ℤ => (ofLex p).2) h
  exact congrArg (Sigma.mk i) (chamberRank_injective (L i) h2)

/-- The ordered partition of `a`'s events into singletons, in the order of the line `L`. -/
noncomputable def seqBeta {a : Ch K} (L : LinesObj a) :
    EventObj a → Fin (Fintype.card (EventObj a)) :=
  keyEquiv (evKey L) (evKey_injective L)

theorem seqBeta_injective {a : Ch K} (L : LinesObj a) : Function.Injective (seqBeta L) :=
  (keyEquiv (evKey L) (evKey_injective L)).injective

theorem seqBeta_surjective {a : Ch K} (L : LinesObj a) : Function.Surjective (seqBeta L) :=
  (keyEquiv (evKey L) (evKey_injective L)).surjective

/-- The singleton partition respects `a`'s bead order (all of bead `i` fires before bead `i+1`). -/
theorem seqBeta_mono {a : Ch K} (L : LinesObj a) (e e' : EventObj a)
    (h : (e.1 : ℕ) < (e'.1 : ℕ)) : seqBeta L e < seqBeta L e' := by
  have hkey : evKey L e < evKey L e' := by
    rw [evKey, evKey, Prod.Lex.toLex_lt_toLex]
    exact Or.inl h
  exact Fin.lt_def.mpr (keyRank_strictMono (evKey L) hkey)

/-! ### Singleton blocks: the tie-block chain of an injective partition is a run -/

/-- An injective ordered partition has singleton blocks. -/
theorem psz_eq_one {a : Ch K} {m : ℕ} (β : EventObj a → Fin m)
    (hβ : Function.Surjective β) (hinj : Function.Injective β) (j : Fin m) :
    ((psz β hβ j : ℕ+) : ℕ) = 1 := by
  have hle : (Finset.univ.filter
      (fun p => bslice β (pbead β hβ j) p = j)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    rw [Finset.mem_filter] at hp hq
    have hpq : β (⟨pbead β hβ j, p⟩ : EventObj a) = β ⟨pbead β hβ j, q⟩ :=
      hp.2.trans hq.2.symm
    exact eq_of_heq (congr_arg_heq Sigma.snd (hinj hpq))
  have hpos := psz_pos β hβ j
  change (Finset.univ.filter (fun p => bslice β (pbead β hβ j) p = j)).card = 1
  omega

/-- The tie-block chain of an injective ordered partition is a run. -/
theorem isRun_pchain {a : Ch K} {m : ℕ} (β : EventObj a → Fin m)
    (hβ : Function.Surjective β) (hinj : Function.Injective β)
    (hmo : ∀ e e' : EventObj a, (e.1 : ℕ) < (e'.1 : ℕ) → β e < β e') :
    IsRun (pchain β hβ hmo) := by
  intro i
  have hmem : (pchain β hβ hmo).dims.get i
      ∈ (pcubes β hβ).map (fun c : Σ n : ℕ+, (⋁a.dims).cells (n : ℕ) => c.1) :=
    List.get_mem _ _
  rw [List.mem_map] at hmem
  obtain ⟨c, hc, hcv⟩ := hmem
  rw [pcubes] at hc
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hc
  change (((pchain β hβ hmo).dims.get i : ℕ+) : ℕ) = 1
  rw [← hcv]
  exact psz_eq_one β hβ hinj j

/-! ### The run of an execution -/

/-- The **sequentialization** of `(a, L)`: `a` refined so that every bead is a single event, the
events of a bead firing in the order of its chamber. -/
noncomputable def seqChain {a : Ch K} (L : LinesObj a) : Ch K :=
  pchain (seqBeta L) (seqBeta_surjective L) (seqBeta_mono L)

theorem seqChain_isRun {a : Ch K} (L : LinesObj a) : IsRun (seqChain L) :=
  isRun_pchain (seqBeta L) (seqBeta_surjective L) (seqBeta_injective L) (seqBeta_mono L)

/-- The refinement `seq (a,L) ⟶ a` in `Ch K`. -/
noncomputable def seqRefine {a : Ch K} (L : LinesObj a) : seqChain L ⟶ a :=
  prefine (seqBeta L) (seqBeta_surjective L) (seqBeta_mono L)

/-! ## The sequentialization in `ConcCat K` -/

/-- The chain underlying an execution. -/
abbrev ConcCat.chain (x : ConcCat K) : Ch K := x.1.unop

/-- The line of an execution. -/
def ConcCat.line (x : ConcCat K) : LinesObj x.chain := x.2

/-- The run of an execution. -/
noncomputable def seq (x : ConcCat K) : Ch K := seqChain x.line

theorem seq_isRun (x : ConcCat K) : IsRun (seq x) := seqChain_isRun x.line

/-- The sequentialized execution (a run with its unique line). -/
noncomputable def seqExec (x : ConcCat K) : ConcCat K := runExec (seq x) (seq_isRun x)

/-- **The sequentialization morphism** `(a, L) ⟶ (seq (a,L), runLine)` of `ConcCat K` (whose
morphisms go coarse ⟶ fine).  The chamber-restriction condition is free: a run has a unique
line. -/
noncomputable def seqHom (x : ConcCat K) : x ⟶ seqExec x :=
  ⟨(seqRefine x.line).op, @Subsingleton.elim _ (linesObj_subsingleton (seq_isRun x)) _ _⟩

/-! ## Normalization: `ConcGrpd K` is its full subgroupoid on the runs -/

/-- The object property "is a run" on `ConcGrpd K`. -/
def RunProp (K : BPSet) : ObjectProperty (ConcGrpd K) :=
  fun X => IsRun (ConcCat.chain (K := K) X.as.as)

/-- The full subgroupoid of `ConcGrpd K` on the runs. -/
abbrev RunGrpd (K : BPSet) : Type _ := (RunProp K).FullSubcategory

noncomputable instance : Groupoid (RunGrpd K) :=
  inferInstanceAs (Groupoid (InducedCategory _ ObjectProperty.FullSubcategory.obj))

/-- **Normalization.**  Every execution is isomorphic, in `ConcGrpd K`, to a run: the
sequentialization morphism is invertible in the free groupoid. -/
noncomputable def runIso (x : ConcCat K) :
    FreeGroupoid.mk (seqExec x) ≅ (FreeGroupoid.mk x : ConcGrpd K) :=
  (asIso (FreeGroupoid.homMk (seqHom x))).symm

instance : (RunProp K).ι.EssSurj :=
  ⟨fun X => ⟨⟨FreeGroupoid.mk (seqExec X.as.as), seq_isRun X.as.as⟩, ⟨runIso X.as.as⟩⟩⟩

instance : (RunProp K).ι.IsEquivalence where

/-- **The normalization theorem**: `ConcGrpd K` is equivalent to its full subgroupoid on the
runs.  (Fully faithfulness of a full-subcategory inclusion + essential surjectivity, which is
`runIso`.) -/
noncomputable def concGrpdRunEquiv (K : BPSet) : ConcGrpd K ≌ RunGrpd K :=
  (RunProp K).ι.asEquivalence.symm

end CubeChains
