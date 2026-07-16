import CubeChains.Braid.SalvettiConstruction
import CubeChains.Braid.CubeIso
import CubeChains.Salvetti.BraidSalObj
import CubeChains.Salvetti.BraidIso
import CubeChains.Salvetti.SalBraidTope
import CubeChains.Salvetti.Normalize
import CubeChains.Events.EventLocalSystem

/-!
# Braid/SalvettiBridge — the cube frame-difference of a Salvetti cell is its tope rank

`cubeFrameDiff (braidSalEquiv.obj a)` (cube side, `Braid/CubeIso`) equals `topePerm a`
(Salvetti side, `Braid/SalvettiConstruction`): both read the *same* linear order on the `n`
events — the tope's rank order — through two frames.  The cube axis naming (`cubeName`) matches
the height function (`heightOf`) once the `evKey` lexicographic key `(bead, chamberRank)` and the
height `n·bead + chamberRank` are seen to induce the same order (the chamber rank is `< n`).
-/

open CategoryTheory Opposite CubeChain StdCube SignType

namespace CubeChains

open SignVec

variable {n : ℕ}

/-- `nones` depends only on the `none`-set and the (natural) index, not the cell's dimension. -/
theorem nones_congr {N k k' : ℕ} (w : Cell N k) (w' : Cell N k')
    (hset : noneSet w.val = noneSet w'.val) {a : Fin k} {a' : Fin k'} (ha : (a : ℕ) = (a' : ℕ)) :
    nones w a = nones w' a' := by
  change (noneSet w.val).orderEmbOfFin w.prop a = (noneSet w'.val).orderEmbOfFin w'.prop a'
  simp only [hset]
  exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr ha

/-- Applying a dependent function at equal arguments gives heterogeneously-equal values. -/
theorem heq_apply {α : Type*} {β : α → Type*} (L : (i : α) → β i) {i i' : α} (h : i = i') :
    HEq (L i) (L i') := by subst h; rfl

/-- `chamberRank` is invariant under heterogeneous transport of the chamber and index. -/
theorem chamberRank_heq {d d' : ℕ} (hdd : d = d') {ch : Chamber d} {ch' : Chamber d'}
    (hch : HEq ch ch') {i : Fin d} {i' : Fin d'} (hi : (i : ℕ) = (i' : ℕ)) :
    chamberRank ch i = chamberRank ch' i' := by
  subst hdd
  obtain rfl := eq_of_heq hch
  obtain rfl := Fin.ext hi
  rfl

/-- The lexicographic order on `(bead, rank)` and the height order `n·bead + rank` agree when the
ranks are bounded by `n` (the `n·bead` term dominates). -/
theorem lexLt_iff_height {i i' : ℕ} {r r' : ℤ}
    (hr : 0 ≤ r) (hrn : r < (n : ℤ)) (hr' : 0 ≤ r') (hr'n : r' < (n : ℤ)) :
    (toLex (i, r) < toLex (i', r')
      ↔ (n : ℤ) * (i : ℤ) + r < (n : ℤ) * (i' : ℤ) + r') := by
  rw [Prod.Lex.toLex_lt_toLex]
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have hexp : (n : ℤ) * ((i : ℤ) + 1) = (n : ℤ) * (i : ℤ) + (n : ℤ) := by ring
    have hle : (n : ℤ) * ((i : ℤ) + 1) ≤ (n : ℤ) * (i' : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hlt) (by positivity)
    constructor
    · intro _; omega
    · intro _; exact Or.inl hlt
  · subst heq
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact absurd h (lt_irrefl _)
      · omega
    · intro h; exact Or.inr ⟨rfl, by omega⟩
  · have hexp : (n : ℤ) * ((i' : ℤ) + 1) = (n : ℤ) * (i' : ℤ) + (n : ℤ) := by ring
    have hle : (n : ℤ) * ((i' : ℤ) + 1) ≤ (n : ℤ) * (i : ℤ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hgt) (by positivity)
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact absurd h (by omega)
      · exact absurd h (by omega)
    · intro h; exfalso; omega

/-- **The height of a cube event, via `heightOf`.**  For the cube chain
`(cubeChainRefineEquiv n).obj x` realising the ordered set partition `x`, the height (under the
chamber tuple `L`) of the coordinate `cubeName` assigns to an event `⟨bead, dir⟩` is
`n·bead + chamberRank (L bead) dir`. -/
theorem heightOf_cubeName (x : RefineObj (□n).init (□n).final)
    (L : (RefineLines n).obj (op x))
    (e : EventObj ((cubeChainRefineEquiv n).functor.obj x)) :
    heightOf x L (cubeName ((cubeChainRefineEquiv n).functor.obj x) e)
      = (n : ℤ) * ((e.1 : ℕ) : ℤ) + chamberRank (L e.1) e.2 := by
  have hji : Fin.cast (dseqLen x).symm (Fin.cast (dseqLen x) e.1) = e.1 := by
    apply Fin.ext; simp only [Fin.val_cast]
  have hd : ChainCat.beadDim ((cubeChainRefineEquiv n).functor.obj x) e.1
      = ((x.cubes.get (Fin.cast (dseqLen x) e.1)).1 : ℕ) := by
    have h := dseqGetNat x (Fin.cast (dseqLen x) e.1)
    rw [hji] at h
    exact h
  have hWTC : CubeChain.wedgeToCubes
      ⟨((cubeChainRefineEquiv n).functor.obj x).dims,
        ((cubeChainRefineEquiv n).functor.obj x).map.hom⟩ = x.cubes :=
    congrArg (fun r => r.cubes) (CubeChain.wedgeToRefineObj_refineToWedgeObj x)
  have hj_lt : (e.1 : ℕ) < (CubeChain.wedgeToCubes
      ⟨((cubeChainRefineEquiv n).functor.obj x).dims,
        ((cubeChainRefineEquiv n).functor.obj x).map.hom⟩).length := by
    rw [CubeChain.wedgeToCubes_length]; exact e.1.isLt
  have hsig : x.cubes.get (Fin.cast (dseqLen x) e.1)
      = ⟨((cubeChainRefineEquiv n).functor.obj x).dims.get e.1,
          beadCell ((cubeChainRefineEquiv n).functor.obj x) e.1⟩ := by
    have h1 : (CubeChain.wedgeToCubes
          ⟨((cubeChainRefineEquiv n).functor.obj x).dims,
            ((cubeChainRefineEquiv n).functor.obj x).map.hom⟩).get ⟨(e.1 : ℕ), hj_lt⟩
        = ⟨((cubeChainRefineEquiv n).functor.obj x).dims.get e.1,
            yonedaEquiv (ιᵂ ((cubeChainRefineEquiv n).functor.obj x).dims e.1
              ≫ ((cubeChainRefineEquiv n).functor.obj x).map.hom)⟩ := by
      rw [CubeChain.wedgeToCubes_get]
      have hcast : Fin.cast (CubeChain.wedgeToCubes_length
          ((cubeChainRefineEquiv n).functor.obj x).dims
          ((cubeChainRefineEquiv n).functor.obj x).map.hom) ⟨(e.1 : ℕ), hj_lt⟩ = e.1 :=
        Fin.ext rfl
      rw [hcast]
    have h2 : x.cubes.get (Fin.cast (dseqLen x) e.1)
        = (CubeChain.wedgeToCubes
            ⟨((cubeChainRefineEquiv n).functor.obj x).dims,
              ((cubeChainRefineEquiv n).functor.obj x).map.hom⟩).get ⟨(e.1 : ℕ), hj_lt⟩ := by
      rw [List.get_of_eq hWTC.symm]
      congr 1
    exact h2.trans h1
  have hset : noneSet (toStar (beadCell ((cubeChainRefineEquiv n).functor.obj x) e.1)).val
      = noneSet (toStar (x.cubes.get (Fin.cast (dseqLen x) e.1)).2).val := by
    rw [hsig]
  have hname : cubeName ((cubeChainRefineEquiv n).functor.obj x) e
      = nones (toStar (x.cubes.get (Fin.cast (dseqLen x) e.1)).2) (Fin.cast hd e.2) := by
    change nones (toStar (beadCell ((cubeChainRefineEquiv n).functor.obj x) e.1)) e.2
        = nones (toStar (x.cubes.get (Fin.cast (dseqLen x) e.1)).2) (Fin.cast hd e.2)
    exact nones_congr _ _ hset (by simp only [Fin.val_cast])
  rw [hname, heightOf_nones x L (Fin.cast (dseqLen x) e.1) (Fin.cast hd e.2)]
  refine congrArg₂ (· + ·) ?_ ?_
  · congr 1
  · apply chamberRank_heq
    · exact congrArg (ChainCat.beadDim ((cubeChainRefineEquiv n).functor.obj x)) hji
    · exact heq_apply L hji
    · simp only [Fin.val_cast]

/-- **The cube frame-difference of a Salvetti cell is the tope rank permutation.** -/
theorem cubeFrameDiff_braidSalEquiv (n : ℕ) (a : Sal (braidCOM n)) :
    cubeFrameDiff ((braidSalEquiv n).functor.obj a) = topePerm a := by
  obtain ⟨y, hle, hfaceEq, hobj⟩ := braidSalEquiv_functor_obj a
  have htope : a.tope = braidSign (heightOf y (toLines y ⟨a.tope, a.2.2.1, hle⟩)) :=
    (congrArg Subtype.val (ofLines_toLines y ⟨a.tope, a.2.2.1, hle⟩)).symm
  rw [hobj]
  set L' := toLines y ⟨a.tope, a.2.2.1, hle⟩ with hL'
  -- `chamberRank (L' e.1) e.2 ∈ [0, n)`
  have hrb : ∀ e : EventObj ((cubeChainRefineEquiv n).functor.obj y),
      0 ≤ chamberRank (L' e.1) e.2 ∧ chamberRank (L' e.1) e.2 < (n : ℤ) := by
    intro e
    refine ⟨(chamberRank_bounded (L' e.1) e.2).1, ?_⟩
    have h1 : chamberRank (L' e.1) e.2
        < (ChainCat.beadDim ((cubeChainRefineEquiv n).functor.obj y) e.1 : ℤ) :=
      (chamberRank_bounded (L' e.1) e.2).2
    have h2 : ChainCat.beadDim ((cubeChainRefineEquiv n).functor.obj y) e.1 ≤ n := by
      calc ChainCat.beadDim ((cubeChainRefineEquiv n).functor.obj y) e.1
          = ((y.cubes.get (Fin.cast (dseqLen y) e.1)).1 : ℕ) := by
            have hh := dseqGetNat y (Fin.cast (dseqLen y) e.1)
            rw [show Fin.cast (dseqLen y).symm (Fin.cast (dseqLen y) e.1) = e.1 from by
              apply Fin.ext; simp only [Fin.val_cast]] at hh
            exact hh
        _ ≤ n := beadDim_le y _
    have h3 : (ChainCat.beadDim ((cubeChainRefineEquiv n).functor.obj y) e.1 : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast h2
    linarith [h1, h3]
  -- the two frames induce the same order on events
  have order : ∀ e e' : EventObj ((cubeChainRefineEquiv n).functor.obj y),
      evKey L' e < evKey L' e'
        ↔ heightOf y L' (cubeName ((cubeChainRefineEquiv n).functor.obj y) e)
            < heightOf y L' (cubeName ((cubeChainRefineEquiv n).functor.obj y) e') := by
    intro e e'
    rw [heightOf_cubeName y L' e, heightOf_cubeName y L' e']
    simp only [evKey]
    exact lexLt_iff_height (hrb e).1 (hrb e).2 (hrb e').1 (hrb e').2
  -- the cube axis is a bijection recovering `cubeName`
  have hsymm : ∀ z : Fin n,
      cubeName ((cubeChainRefineEquiv n).functor.obj y)
        ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm z) = z := by
    intro z; rw [← cubeAxis_apply]; exact Equiv.apply_symm_apply _ _
  apply Equiv.ext
  intro p
  apply Fin.ext
  rw [topePerm_apply, topeRank_eq_card htope p]
  have hval : (cubeFrameDiff
        (⟨op ((cubeChainRefineEquiv n).functor.obj y), L'⟩ : ConcCat (□n)) p).val
      = keyRank (evKey L') ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm p) := by
    change (finCongr (eventObj_card_cube ((cubeChainRefineEquiv n).functor.obj y))
          (keyEquiv (evKey L') (evKey_injective L')
            ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm p))).val = _
    rw [finCongr_apply, Fin.val_cast, keyEquiv_val]
  rw [hval]
  change (Finset.univ.filter (fun z => evKey L' z
        < evKey L' ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm p))).card
      = (Finset.univ.filter (fun q => heightOf y L' q < heightOf y L' p)).card
  refine Finset.card_bij'
    (fun e _ => cubeAxis ((cubeChainRefineEquiv n).functor.obj y) e)
    (fun q _ => (cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm q) ?_ ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [cubeAxis_apply]
    have h2 := (order e ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm p)).mp he
    rwa [hsymm p] at h2
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    apply (order ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm q)
      ((cubeAxis ((cubeChainRefineEquiv n).functor.obj y)).symm p)).mpr
    rw [hsymm q, hsymm p]
    exact hq
  · intro e _; exact Equiv.symm_apply_apply _ _
  · intro q _; exact Equiv.apply_symm_apply _ _

end CubeChains
