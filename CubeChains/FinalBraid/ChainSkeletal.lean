import CubeChains.FinalBraid.Lines
import CubeChains.Chains.SegalAltitude
import CubeChains.Chains.Correspondence

/-!
# FinalBraid/ChainSkeletal — `Ch(K)` is an acyclic, skeletal category (unconditional)

For **every** bi-pointed precubical set `K`, the cube-chain category `Ch(K)` has only
identity endomorphisms and is skeletal.  No `NonSelfLinked`, no `AdmitsAltitude K`, no
thinness is required: the proof uses only the **serial wedge's own** `trueCount`
prefix-sum altitude (`serialWedge_admitsAltitude`), which always exists.

* `serialWedge_bipointed_endo_id` — every bi-pointed **endomorphism** of a serial wedge is
  the identity.  This is the whole content.
* `ChainCat.endo_eq_id` — every endomorphism of `Ch(K)` is the identity.
* `ChainCat.eq_of_hom_hom` — `Ch(K)` is skeletal: `a ⟶ b` and `b ⟶ a` force `a = b`.
* Antisymmetry corollaries: thin + skeletal = poset.

**Layer:** FinalBraid.  **Imports:** `FinalBraid/Lines`, `Chains/SegalAltitude`.

The key altitude computation (`serialWedge_blockIdx_prefix_bound`) mirrors the
`case mono` of `Chains/Correspondence.wedgeToRefineMap`, but discharges the altitude
input with `serialWedge_admitsAltitude` instead of `K.AdmitsAltitude`.
-/

open CategoryTheory Opposite CubeChain StdCube

namespace FinalBraid

/-! ### Altitude of a bead read off a wedge map -/

/-- The altitude of the `k`-th read-off cube of a wedge map `hom : □^∨(ed) ⟶ □^∨(cd)`
whose source-init lands on `cd`'s init: it is the dimension prefix-sum of the earlier
cubes.  A packaging of `isCubeChain_alt_get` through `wedgeToCubes_get`. -/
theorem serialWedge_bead_alt {ed cd : List ℕ+}
    (alt : ∀ n, (BPSet.serialWedge cd).toPsh.cells n → ℤ)
    (hax : PrecubicalSet.IsAltitude (BPSet.serialWedge cd).toPsh alt)
    (h0 : alt 0 (BPSet.serialWedge cd).init = 0)
    (hom : (BPSet.serialWedge ed).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (q : (BPSet.serialWedge cd).toPsh.cells 0)
    (hci : IsCubeChain (BPSet.serialWedge cd).init (wedgeToCubes ⟨ed, hom⟩) q)
    (k : Fin ed.length) :
    alt (ed.get k : ℕ) (yonedaEquiv (BPSet.serialWedge.ι ed k ≫ hom))
      = dimPrefixSum (wedgeToCubes ⟨ed, hom⟩) k.val := by
  have hlt : k.val < (wedgeToCubes ⟨ed, hom⟩).length := by
    rw [wedgeToCubes_length]; exact k.isLt
  have hcast : (⟨k.val, hlt⟩ : Fin (wedgeToCubes ⟨ed, hom⟩).length).cast
      (wedgeToCubes_length ed hom) = k := Fin.ext rfl
  have hget := wedgeToCubes_get ed hom ⟨k.val, hlt⟩
  have hg := isCubeChain_alt_get alt hax (wedgeToCubes ⟨ed, hom⟩)
    (BPSet.serialWedge cd).init q hci k.val hlt
  rw [h0, zero_add] at hg
  rw [hget, hcast] at hg
  exact hg

/-! ### Block prefix-sum bounds (only the serial wedge's altitude) -/

/-- **Prefix-sum sandwich for `blockIdx`.**  For a wedge map `φ : □^∨(ad) ⟶ □^∨(cd)`
sending `ad`-init to `cd`-init, the block of source bead `i` (`blockIdx φ i`) is pinned
by the dimension prefix sums: its `cd`-prefix is `≤` bead `i`'s `ad`-prefix, which in
turn is `<` the next `cd`-prefix.  Uses **only** `serialWedge_admitsAltitude cd`. -/
theorem serialWedge_blockIdx_prefix_bound {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init)
    (i : Fin ad.length) :
    dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩) (blockIdx φ i).val
        ≤ dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      ∧ dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
        < dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩)
            ((blockIdx φ i).val + 1) := by
  obtain ⟨alt, hax, h0⟩ := BPSet.serialWedge_admitsAltitude cd
  -- The taut (identity) chain of `□^∨(cd)`.
  have hciT : IsCubeChain (BPSet.serialWedge cd).init
      (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩) (BPSet.serialWedge cd).final := by
    have h := wedgeToCubes_isCubeChain (K := BPSet.serialWedge cd) cd
      (𝟙 (BPSet.serialWedge cd).toPsh)
    simpa using h
  -- The pushed chain (`φ` read off) in `□^∨(cd)`.
  have hciP : IsCubeChain (BPSet.serialWedge cd).init (wedgeToCubes ⟨ad, φ⟩)
      (φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).final) := by
    have h := wedgeToCubes_isCubeChain (K := BPSet.serialWedge cd) ad φ
    rwa [hinit] at h
  -- Bead altitudes.
  have hP_i := serialWedge_bead_alt alt hax h0 φ _ hciP i
  have hT_j := serialWedge_bead_alt alt hax h0 (𝟙 (BPSet.serialWedge cd).toPsh) _ hciT
    (blockIdx φ i)
  rw [Category.comp_id] at hT_j
  -- The pushed bead `i` is the `cd`-bead `blockIdx φ i` pulled back along `blockFace φ i`.
  have hce : yonedaEquiv (BPSet.serialWedge.ι ad i ≫ φ)
      = (BPSet.serialWedge cd).toPsh.map (blockFace φ i).op
          (yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ i))) :=
    (congrArg yonedaEquiv (blockFace_spec φ i)).trans
      (yonedaEquiv_naturality (BPSet.serialWedge.ι cd (blockIdx φ i)) (blockFace φ i)).symm
  have hc := PrecubicalSet.alt_cubeMap alt hax
    (yonedaEquiv (BPSet.serialWedge.ι cd (blockIdx φ i))) (blockFace φ i)
  rw [PrecubicalSet.cubeMap, yonedaEquiv_symm_app_apply] at hc
  -- The key equation of prefix sums.
  have haltrel : dimPrefixSum (wedgeToCubes ⟨ad, φ⟩) i.val
      = dimPrefixSum (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩) (blockIdx φ i).val
        + (StdCube.trueCount (StdCube.ev (blockFace φ i)) : ℤ) := by
    rw [← hP_i, ← hT_j, hce]; exact hc
  -- The `(blockIdx φ i)`-th successor of the taut prefix sum.
  have hjlt : (blockIdx φ i).val < (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩).length := by
    rw [wedgeToCubes_length]; exact (blockIdx φ i).isLt
  have hgetfst : ((wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩).get
      ⟨(blockIdx φ i).val, hjlt⟩).1 = cd.get (blockIdx φ i) := by
    rw [wedgeToCubes_get]; exact congrArg cd.get (Fin.ext rfl)
  have hsucc := dimPrefixSum_succ (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩) hjlt
  rw [hgetfst] at hsucc
  -- trueCount bounds: `0 ≤ tc < cd.get (blockIdx φ i)`.
  have hle : (ad.get i : ℕ) ≤ (cd.get (blockIdx φ i) : ℕ) :=
    StdCube.cells_card_le (StdCube.ev (blockFace φ i))
  have htle : StdCube.trueCount (StdCube.ev (blockFace φ i))
      ≤ (cd.get (blockIdx φ i) : ℕ) - (ad.get i : ℕ) :=
    StdCube.trueCount_le (StdCube.ev (blockFace φ i))
  have hipos : 0 < (ad.get i : ℕ) := (ad.get i).2
  have htN : StdCube.trueCount (StdCube.ev (blockFace φ i)) < (cd.get (blockIdx φ i) : ℕ) := by
    omega
  have htlt : (StdCube.trueCount (StdCube.ev (blockFace φ i)) : ℤ)
      < ((cd.get (blockIdx φ i) : ℕ) : ℤ) := by exact_mod_cast htN
  have hnn : (0 : ℤ) ≤ (StdCube.trueCount (StdCube.ev (blockFace φ i)) : ℤ) :=
    Int.natCast_nonneg _
  refine ⟨by omega, ?_⟩
  rw [hsucc]
  omega

/-! ### The core rigidity lemma -/

/-- **Every bi-pointed endomorphism of a serial wedge is the identity.**  Unconditional.

For each bead `i`, `blockIdx φ i = i` (the prefix-sum sandwich collapses since both chains
have dimension list `dims`), so bead `i`'s image is a *full-dimensional* `Box`-face of bead
`i`, hence the identity face — thus `ι_i ≫ φ = ι_i`.  `serialWedge_hom_ext` then gives
`φ = 𝟙`.  Uses only the serial wedge's altitude. -/
theorem serialWedge_bipointed_endo_id (dims : List ℕ+)
    (φ : BPSet.serialWedge dims ⟶ BPSet.serialWedge dims) :
    φ = 𝟙 (BPSet.serialWedge dims) := by
  -- Same dimension list on both sides ⟹ the two prefix sums coincide.
  have hdps : ∀ n : ℕ, dimPrefixSum (wedgeToCubes ⟨dims, φ.hom⟩) n
      = dimPrefixSum (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩) n := by
    intro n
    have hmap : (wedgeToCubes ⟨dims, φ.hom⟩).map (·.1)
        = (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).map (·.1) := by
      rw [wedgeToCubes_dims, wedgeToCubes_dims]
    have key : (wedgeToCubes ⟨dims, φ.hom⟩).map (fun x => (x.1 : ℕ))
        = (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).map (fun x => (x.1 : ℕ)) := by
      rw [show (fun x : Σ n : ℕ+, (BPSet.serialWedge dims).toPsh.cells (n : ℕ) => (x.1 : ℕ))
            = (fun p : ℕ+ => (p : ℕ)) ∘ (fun x => x.1) from rfl,
          ← List.map_map, ← List.map_map, hmap]
    simp only [dimPrefixSum]
    rw [List.map_take, List.map_take, key]
  -- The block-agreement, per bead.
  have hblock : ∀ i : Fin dims.length,
      BPSet.serialWedge.ι dims i ≫ φ.hom = BPSet.serialWedge.ι dims i := by
    intro i
    obtain ⟨r, incl, hincl⟩ := wedgeMap_block φ.hom i
    have hbound := serialWedge_blockIdx_prefix_bound φ.hom φ.app_init i
    rw [hdps] at hbound
    obtain ⟨hb1, hb2⟩ := hbound
    -- The sandwich pins `blockIdx φ.hom i = i`.
    have hilt : i.val < (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).length := by
      rw [wedgeToCubes_length]; exact i.isLt
    have hidx : blockIdx φ.hom i = i := by
      by_contra hne
      rcases Nat.lt_or_ge (blockIdx φ.hom i).val i.val with hlt | hge
      · -- blockIdx < i : then `PT(blockIdx+1) ≤ PT(i)`, contradicting the strict bound.
        have hmono := dimPrefixSum_mono
          (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩)
          (show (blockIdx φ.hom i).val + 1 ≤ i.val by omega)
        omega
      · -- blockIdx ≥ i, but ≠ i, so blockIdx > i : `PT(i+1) ≤ PT(blockIdx)`.
        have hgt : i.val < (blockIdx φ.hom i).val := by
          rcases Nat.lt_or_ge i.val (blockIdx φ.hom i).val with h | h
          · exact h
          · exact absurd (Fin.ext (le_antisymm hge h)).symm hne
        have hsucc := dimPrefixSum_succ
          (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩) hilt
        have hgetfst : ((wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩).get
            ⟨i.val, hilt⟩).1 = dims.get i := by
          rw [wedgeToCubes_get]; exact congrArg dims.get (Fin.ext rfl)
        rw [hgetfst] at hsucc
        have hmono := dimPrefixSum_mono
          (wedgeToCubes ⟨dims, 𝟙 (BPSet.serialWedge dims).toPsh⟩)
          (show i.val + 1 ≤ (blockIdx φ.hom i).val by omega)
        have hpos : 0 < (dims.get i : ℕ) := (dims.get i).2
        omega
    -- Hence `r = i` and the face `incl` is a `Box`-endo, so the identity.
    have hr : r = i := (blockIdx_eq_of_factor φ.hom i r incl hincl).trans hidx
    subst r
    have hincl_id : incl = 𝟙 (Box.ob (dims.get i : ℕ)) := by
      have htop : StdCube.ev incl = StdCube.topCell (dims.get i : ℕ) :=
        StdCube.eq_topCell (StdCube.ev incl)
      calc incl = StdCube.canonicalMap (StdCube.ev incl) :=
            ((StdCube.cubeRepr (stdPre (dims.get i : ℕ)) (dims.get i : ℕ)).left_inv incl).symm
        _ = StdCube.canonicalMap (StdCube.topCell (dims.get i : ℕ)) := by rw [htop]
        _ = 𝟙 (Box.ob (dims.get i : ℕ)) := StdCube.canonicalMap_topCell (dims.get i : ℕ)
    rw [hincl_id, CategoryTheory.Functor.map_id, Category.id_comp] at hincl
    exact hincl
  -- Assemble via the serial-wedge uniqueness.
  apply BPSet.hom_ext
  rw [BPSet.id_hom]
  refine serialWedge_hom_ext dims φ.hom (𝟙 (BPSet.serialWedge dims).toPsh) (fun i => ?_) ?_
  · rw [Category.comp_id]; exact hblock i
  · rw [φ.app_init]; rfl

/-! ### Consequences for `Ch(K)` -/

/-! ### Skeletality helpers -/

/-- `blockIdx` of an identity map is the identity. -/
theorem blockIdx_id {dims : List ℕ+} (i : Fin dims.length) :
    blockIdx (𝟙 (BPSet.serialWedge dims).toPsh) i = i :=
  (blockIdx_eq_of_factor (𝟙 (BPSet.serialWedge dims).toPsh) i i
    (𝟙 (Box.ob (dims.get i : ℕ))) (by
      rw [Category.comp_id, CategoryTheory.Functor.map_id, Category.id_comp])).symm

/-- **`blockIdx` of a bi-pointed wedge map is monotone** — from the prefix-sum sandwich,
using only the serial wedge's altitude. -/
theorem serialWedge_blockIdx_monotone {ad cd : List ℕ+}
    (φ : (BPSet.serialWedge ad).toPsh ⟶ (BPSet.serialWedge cd).toPsh)
    (hinit : φ.app (op (Box.ob 0)) (BPSet.serialWedge ad).init = (BPSet.serialWedge cd).init) :
    Monotone (blockIdx φ) := by
  intro i i' hii
  rw [Fin.le_def]
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨hb1, _⟩ := serialWedge_blockIdx_prefix_bound φ hinit i
  obtain ⟨_, hb2'⟩ := serialWedge_blockIdx_prefix_bound φ hinit i'
  have hmA := dimPrefixSum_mono (wedgeToCubes ⟨ad, φ⟩) (Fin.le_def.mp hii)
  have hmB := dimPrefixSum_mono (wedgeToCubes ⟨cd, 𝟙 (BPSet.serialWedge cd).toPsh⟩)
    (show (blockIdx φ i').val + 1 ≤ (blockIdx φ i).val by omega)
  omega

/-- Helper: a monotone bijection of `Fin`s (with the target length equal to the source
length) is the length-cast, so it fixes every index value. -/
theorem monotone_bij_fin_cast {m n : ℕ} (hmn : m = n) {R : Fin m → Fin n} {S : Fin n → Fin m}
    (hR : Monotone R) (hS : Monotone S) (h1 : ∀ i, S (R i) = i) (h2 : ∀ i, R (S i) = i)
    (i : Fin m) : (R i).val = i.val := by
  let e : Fin m ≃o Fin n :=
    { toEquiv := ⟨R, S, h1, h2⟩
      map_rel_iff' := by
        intro a b
        refine ⟨fun h => ?_, fun h => hR h⟩
        have h' : R a ≤ R b := h
        have := hS h'
        rwa [h1, h1] at this }
  have he : e = Fin.castOrderIso hmn := Subsingleton.elim _ _
  calc (R i).val = (e i).val := rfl
    _ = (Fin.castOrderIso hmn i).val := by rw [he]
    _ = i.val := by simp

end FinalBraid

open FinalBraid

/-! ### Consequences for the chain category `Ch(K)` -/

/-- **Every endomorphism of `Ch(K)` is the identity** — for every `K`, unconditionally. -/
theorem ChainCat.endo_eq_id {K : BPSet} {a : ChainCat.Obj K} (f : a ⟶ a) : f = 𝟙 a := by
  apply ChainCat.hom_ext'
  rw [ChainCat.id_φ]
  exact serialWedge_bipointed_endo_id a.dims f.φ

/-- **`Ch(K)` is skeletal**: any pair of morphisms `a ⟶ b`, `b ⟶ a` forces `a = b`.
Unconditional.  The two composites are identities (`endo_eq_id`), so `blockIdx f.φ` is a
monotone bijection — hence the identity, giving `a.dims = b.dims` — and then `f.φ` is a
bi-pointed endo, so the identity, giving `a.map = b.map`. -/
theorem ChainCat.eq_of_hom_hom {K : BPSet} {a b : ChainCat.Obj K}
    (f : a ⟶ b) (g : b ⟶ a) : a = b := by
  -- The two composites are identities.
  have hfg : f.φ.hom ≫ g.φ.hom = 𝟙 (BPSet.serialWedge a.dims).toPsh := by
    have h := congrArg (fun m : a ⟶ a => (ChainCat.Hom.φ m).hom) (ChainCat.endo_eq_id (f ≫ g))
    simpa only [ChainCat.comp_φ, BPSet.comp_hom, ChainCat.id_φ, BPSet.id_hom] using h
  have hgf : g.φ.hom ≫ f.φ.hom = 𝟙 (BPSet.serialWedge b.dims).toPsh := by
    have h := congrArg (fun m : b ⟶ b => (ChainCat.Hom.φ m).hom) (ChainCat.endo_eq_id (g ≫ f))
    simpa only [ChainCat.comp_φ, BPSet.comp_hom, ChainCat.id_φ, BPSet.id_hom] using h
  -- `blockIdx f.φ.hom` and `blockIdx g.φ.hom` are mutually inverse.
  have hSR : ∀ i, blockIdx g.φ.hom (blockIdx f.φ.hom i) = i := by
    intro i
    have h := blockIdx_comp f.φ.hom g.φ.hom i
    rw [hfg, blockIdx_id] at h
    exact h.symm
  have hRS : ∀ j, blockIdx f.φ.hom (blockIdx g.φ.hom j) = j := by
    intro j
    have h := blockIdx_comp g.φ.hom f.φ.hom j
    rw [hgf, blockIdx_id] at h
    exact h.symm
  -- Length equality, monotonicity, and hence the index identity.
  have hlen : a.dims.length = b.dims.length :=
    Fin.equiv_iff_eq.mp ⟨⟨blockIdx f.φ.hom, blockIdx g.φ.hom, hSR, hRS⟩⟩
  have hmonoR := serialWedge_blockIdx_monotone f.φ.hom f.φ.app_init
  have hmonoS := serialWedge_blockIdx_monotone g.φ.hom g.φ.app_init
  have hReq : ∀ i, (blockIdx f.φ.hom i).val = i.val := fun i =>
    monotone_bij_fin_cast hlen hmonoR hmonoS hSR hRS i
  -- Dimension preservation (full-dimensional faces both ways).
  have hdimpres : ∀ i, a.dims.get i = b.dims.get (blockIdx f.φ.hom i) := by
    intro i
    have hle1 : (a.dims.get i : ℕ) ≤ (b.dims.get (blockIdx f.φ.hom i) : ℕ) :=
      StdCube.cells_card_le (StdCube.ev (blockFace f.φ.hom i))
    have hle2 : (b.dims.get (blockIdx f.φ.hom i) : ℕ)
        ≤ (a.dims.get (blockIdx g.φ.hom (blockIdx f.φ.hom i)) : ℕ) :=
      StdCube.cells_card_le (StdCube.ev (blockFace g.φ.hom (blockIdx f.φ.hom i)))
    rw [hSR i] at hle2
    have : (a.dims.get i : ℕ) = (b.dims.get (blockIdx f.φ.hom i) : ℕ) := le_antisymm hle1 hle2
    exact_mod_cast this
  -- `a.dims = b.dims`.
  have hdimseq : a.dims = b.dims := by
    apply List.ext_getElem hlen
    intro k h1 h2
    change a.dims.get ⟨k, h1⟩ = b.dims.get ⟨k, h2⟩
    rw [hdimpres ⟨k, h1⟩]
    exact congrArg b.dims.get (Fin.ext (hReq ⟨k, h1⟩))
  -- Conclude `a = b`.
  clear hfg hgf hSR hRS hlen hmonoR hmonoS hReq hdimpres g
  cases a with
  | mk da ma =>
    cases b with
    | mk db mb =>
      obtain rfl : da = db := hdimseq
      have hφ : f.φ = 𝟙 (BPSet.serialWedge da) := serialWedge_bipointed_endo_id da f.φ
      have hmap : ma = mb := by
        have hw := f.w
        rw [hφ, Category.id_comp] at hw
        exact hw.symm
      rw [hmap]

/-- **Antisymmetry of the chain order** (`a ≤ b` := a morphism `a ⟶ b` exists),
unconditional.  With thinness (`chainCat_hom_subsingleton`, under `NonSelfLinked` +
`AdmitsAltitude`), `Ch(K)` is therefore a **poset**: the objects with `≤` form a partial
order and the category is thin, i.e. is that poset. -/
theorem ChainCat.le_antisymm {K : BPSet} {a b : ChainCat.Obj K}
    (hab : Nonempty (a ⟶ b)) (hba : Nonempty (b ⟶ a)) : a = b :=
  ChainCat.eq_of_hom_hom hab.some hba.some
