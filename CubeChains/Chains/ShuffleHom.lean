import CubeChains.Braid.Blocks
import CubeChains.Chains.TotalMerge
import CubeChains.Chains.WedgeBraid
import CubeChains.Salvetti.ChainBraidFace
import CubeChains.Salvetti.RunSegal

/-!
# Chains/ShuffleHom — a wedge map **is** its coordinate bijection

`coordMapEquiv : (⋁a ⟶ ⋁b) → (beadEvent a ≃ beadEvent b)` is injective with image the
**shuffles**: bijections whose bead component is monotone and which preserve the order inside each
source bead.  Every serial wedge maps into a cube (`nonempty_toCube`), so the statement is read off
`Ch (□m)`, where a chain is its ordered partition (`eq_of_beadOf`, `blockChain`) and the descent map
is a mono.  `serialWedgeInclusion` (`Chains/MergeClass`) is fully faithful, so everything here is a
statement about the hom-sets of `Ch Zbp`.
-/

open CategoryTheory CubeChains CubeChain BPSet StdCube

namespace CubeChains

variable {a b d : List ℕ+} {m : ℕ}

/-! ## Every serial wedge sits in a cube -/

/-- **Total merge**: a serial wedge maps into the cube of its own total dimension — absorb the
leading bead with `cubeMerge`, recurse on the tail. -/
theorem nonempty_toCube : ∀ b : List ℕ+, Nonempty (⋁b ⟶ □(dimSum b))
  | [] => ⟨𝟙 _⟩
  | p :: rest => (nonempty_toCube rest).map fun χ =>
      ChainCat.wedge2Map (𝟙 (□(p : ℕ))) χ ≫ ChainCat.cubeMerge (p : ℕ) (dimSum rest)

/-! ## Charts: a wedge map into a cube, read as a bijection on coordinates -/

/-- `coordFlip` of a composite, as an equality of equivalences. -/
theorem coordFlip_trans (φ : ⋁a ⟶ ⋁b) (χ : ⋁b ⟶ □m) :
    coordFlip (φ ≫ χ) = (coordMapEquiv φ).trans (coordFlip χ) :=
  Equiv.ext fun p => coordFlip_comp φ χ p

/-- Inside one bead a chart is the order embedding `faceEmb`, so it reads the event order. -/
theorem coordFlip_lt_of_pos_lt (χ : ⋁b ⟶ □m) {u v : beadEvent b} (h : u.1 = v.1)
    (hlt : pos u < pos v) : coordFlip χ u < coordFlip χ v := by
  obtain ⟨j, l⟩ := u
  obtain ⟨j', l'⟩ := v
  obtain rfl : j = j' := h
  rw [coordFlip_eq, coordFlip_eq]
  exact (faceEmb (beadFace χ.hom j)).strictMono (pos_lt_iff_of_fst_eq.mp hlt)

/-- A chart is strictly monotone on each bead. -/
theorem coordFlip_strictMono (χ : ⋁d ⟶ □m) (i : Fin d.length) :
    StrictMono fun k : Fin (d.get i : ℕ) => coordFlip χ ⟨i, k⟩ := fun _ _ h =>
  coordFlip_lt_of_pos_lt χ rfl (pos_lt_iff_of_fst_eq.mpr h)

/-- The bead of a chain classified by `χ` is the first component of the chart's inverse. -/
theorem beadOf_mk (χ : ⋁d ⟶ □m) (q : Fin m) :
    beadOf (⟨d, χ⟩ : Ch (□m)) q = ((coordFlip χ).symm q).1 := rfl

/-- **A wedge map into a cube is determined by its chart.** -/
theorem toCube_ext {χ χ' : ⋁d ⟶ □m} (h : coordFlip χ = coordFlip χ') : χ = χ' := by
  have hobj : (⟨d, χ⟩ : Ch (□m)) = ⟨d, χ'⟩ :=
    eq_of_beadOf fun q => congrArg Fin.val (by rw [beadOf_mk, beadOf_mk, h])
  obtain ⟨hd, hm⟩ := ChainCat.Obj.eq_mk_of_eq hobj
  rw [hm, Subsingleton.elim hd rfl]
  simp

/-- **The bead fibre of a chart has the bead's dimension.**  `faceEmb` enumerates exactly the
coordinates whose bead is `i` (`mem_range_iff_beadOf`). -/
theorem card_beadFibre (A : Ch (□m)) (i : Fin A.dims.length) :
    (Finset.univ.filter fun q => beadOf A q = i).card = (A.dims.get i : ℕ) := by
  refine ((Finset.card_bij (s := (Finset.univ : Finset (Fin (A.dims.get i : ℕ))))
    (t := Finset.univ.filter fun q => beadOf A q = i)
    (fun k _ => coordFlip A.map ⟨i, k⟩) ?_ ?_ ?_).symm.trans (Finset.card_fin _))
  · intro k _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [beadOf_eq, Equiv.symm_apply_apply]
  · intro k _ k' _ h
    simpa using (coordFlip A.map).injective h
  · intro q hq
    obtain ⟨k, hk⟩ := (mem_range_iff_beadOf A i q).mpr (Finset.mem_filter.mp hq).2
    exact ⟨k, Finset.mem_univ _, by simp only [coordFlip_eq]; exact hk⟩

/-- The same count on the source side, where it is the bead's own coordinate set. -/
theorem card_fibre_beadEvent (d : List ℕ+) (i : Fin d.length) :
    (Finset.univ.filter fun p : beadEvent d => p.1 = i).card = (d.get i : ℕ) := by
  refine ((Finset.card_bij (s := (Finset.univ : Finset (Fin (d.get i : ℕ))))
    (t := Finset.univ.filter fun p : beadEvent d => p.1 = i)
    (fun k _ => ⟨i, k⟩) ?_ ?_ ?_).symm.trans (Finset.card_fin _))
  · exact fun k _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro k _ k' _ h; simpa using h
  · rintro ⟨j, k⟩ hp
    obtain rfl : j = i := (Finset.mem_filter.mp hp).2
    exact ⟨k, Finset.mem_univ _, rfl⟩

/-- Transporting `card_fibre_beadEvent` along an arbitrary chart. -/
theorem card_fibre_chart (c : beadEvent d ≃ Fin m) (i : Fin d.length) :
    (Finset.univ.filter fun q : Fin m => (c.symm q).1 = i).card = (d.get i : ℕ) :=
  (Finset.card_equiv c.symm fun q => by simp).trans (card_fibre_beadEvent d i)

/-! ## Charts classify wedge maps into a cube

A chain of `□m` is its ordered partition (`eq_of_beadOf`), and inside a bead the chart enumerates
that bead's block in increasing order — so the chart is the *unique* bead-monotone bijection with
the given partition, and every one of them occurs. -/

/-- **A chart is pinned by its partition.**  Two bead-monotone bijections enumerating the same
blocks are the same enumeration (`Finset.orderEmbOfFin_unique`). -/
theorem coordFlip_eq_of_beadOf (A : Ch (□m)) (c : beadEvent A.dims ≃ Fin m)
    (hc : ∀ i, StrictMono fun k : Fin (A.dims.get i : ℕ) => c ⟨i, k⟩)
    (hbead : ∀ q, (c.symm q).1 = beadOf A q) : coordFlip A.map = c := by
  refine Equiv.ext fun p => ?_
  obtain ⟨i, k⟩ := p
  have hcard : (Finset.univ.filter fun q => beadOf A q = i).card = (A.dims.get i : ℕ) :=
    card_beadFibre A i
  have hmem₁ : ∀ k : Fin (A.dims.get i : ℕ),
      coordFlip A.map ⟨i, k⟩ ∈ Finset.univ.filter fun q => beadOf A q = i := fun k =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [beadOf_eq, Equiv.symm_apply_apply]⟩
  have hmem₂ : ∀ k : Fin (A.dims.get i : ℕ),
      c ⟨i, k⟩ ∈ Finset.univ.filter fun q => beadOf A q = i := fun k =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hbead, Equiv.symm_apply_apply]⟩
  exact congrFun ((Finset.orderEmbOfFin_unique hcard hmem₁ (coordFlip_strictMono A.map i)).trans
    (Finset.orderEmbOfFin_unique hcard hmem₂ (hc i)).symm) k

/-- **Every bead-monotone bijection is a chart.**  Its blocks reconstruct the chain
(`blockChain`), whose bead dimensions are the block sizes. -/
theorem exists_coordFlip_eq (c : beadEvent d ≃ Fin m)
    (hc : ∀ i : Fin d.length, StrictMono fun k : Fin (d.get i : ℕ) => c ⟨i, k⟩) :
    ∃ χ : ⋁d ⟶ □m, coordFlip χ = c := by
  have hβ : Function.Surjective fun q : Fin m => (c.symm q).1 := fun i =>
    ⟨c ⟨i, ⟨0, (d.get i).2⟩⟩, congrArg Sigma.fst (c.symm_apply_apply _)⟩
  obtain ⟨A, hd, hbead⟩ : ∃ A : Ch (□m), A.dims = d ∧
      ∀ q, ((c.symm q).1 : ℕ) = (beadOf A q : ℕ) := by
    refine ⟨blockChain _ hβ, ?_, fun q => (beadOf_blockChain _ hβ q).symm⟩
    refine List.ext_get (length_blockChain _ hβ) fun i h₁ h₂ => ?_
    refine PNat.coe_injective ?_
    rw [← card_beadFibre (blockChain _ hβ) ⟨i, h₁⟩, ← card_fibre_chart c ⟨i, h₂⟩]
    refine congrArg Finset.card (Finset.filter_congr fun q _ => ?_)
    rw [Fin.ext_iff, Fin.ext_iff, beadOf_blockChain _ hβ q]
  subst hd
  exact ⟨A.map, coordFlip_eq_of_beadOf A c hc fun q => Fin.ext (hbead q)⟩

/-! ## Shuffles: the image of `coordMapEquiv` -/

/-- A **shuffle** of `a` into `b`: a bijection of events whose bead component is monotone and which
preserves the event order inside each source bead. -/
structure IsShuffle {a b : List ℕ+} (e : beadEvent a ≃ beadEvent b) : Prop where
  /-- Beads move monotonically — `blockIdx` of a wedge map is monotone. -/
  bead : ∀ p q : beadEvent a, p.1 ≤ q.1 → (e p).1 ≤ (e q).1
  /-- Inside a bead the event order survives — there a wedge map is `faceEmb`. -/
  inner : ∀ p q : beadEvent a, p.1 = q.1 → pos p < pos q → pos (e p) < pos (e q)

theorem IsShuffle.bead_eq {e : beadEvent a ≃ beadEvent b} (he : IsShuffle e) {p q : beadEvent a}
    (h : p.1 = q.1) : (e p).1 = (e q).1 :=
  le_antisymm (he.bead p q h.le) (he.bead q p h.ge)

theorem isShuffle_coordMapEquiv (φ : ⋁a ⟶ ⋁b) : IsShuffle (coordMapEquiv φ) where
  bead _ _ h := coordMap_fst_monotone φ h
  inner _ _ h hlt := coordMap_pos_lt_of_fst_eq φ h hlt

/-- **A bi-pointed wedge map is its coordinate bijection.**  Both maps agree after the total merge
into a cube, where the descent map is a monomorphism (`descent_mono`). -/
theorem wedgeHom_ext {φ ψ : ⋁a ⟶ ⋁b} (h : coordMapEquiv φ = coordMapEquiv ψ) : φ = ψ := by
  obtain ⟨χ⟩ := nonempty_toCube b
  haveI : Mono χ.hom :=
    descent_mono (cube_nonSelfLinked _) (cube_admitsAltitude _) ⟨b, χ⟩
  have hc : φ ≫ χ = ψ ≫ χ := toCube_ext (by rw [coordFlip_trans, coordFlip_trans, h])
  exact BPSet.hom_ext ((cancel_mono χ.hom).mp (congrArg BPSet.Hom.hom hc))

/-- **Every shuffle is realised.**  Push the shuffle through a chart of `⋁b` to get a chart of
`⋁a`; the two charts' partitions are then comparable, and `reflectHom` supplies the wedge map. -/
theorem exists_coordMapEquiv_eq {e : beadEvent a ≃ beadEvent b} (he : IsShuffle e) :
    ∃ φ : ⋁a ⟶ ⋁b, coordMapEquiv φ = e := by
  obtain ⟨χ⟩ := nonempty_toCube b
  set m := dimSum b
  obtain ⟨χ', hχ'⟩ := exists_coordFlip_eq (e.trans (coordFlip χ)) fun i k k' hk =>
    coordFlip_lt_of_pos_lt χ (he.bead_eq rfl) (he.inner _ _ rfl (pos_lt_iff_of_fst_eq.mpr hk))
  have hface : (chFace (⟨b, χ⟩ : Ch (□m))).1 ⊑ (chFace (⟨a, χ'⟩ : Ch (□m))).1 := by
    rw [chFace_faceLE_iff]
    intro p q hne
    have hA : ∀ r : Fin m,
        beadOf (⟨a, χ'⟩ : Ch (□m)) r = (e.symm ((coordFlip χ).symm r)).1 := by
      intro r; rw [beadOf_mk, hχ']; rfl
    have hkey : ∀ r s : Fin m,
        (e.symm ((coordFlip χ).symm r)).1 ≤ (e.symm ((coordFlip χ).symm s)).1 →
          ((coordFlip χ).symm r).1 ≤ ((coordFlip χ).symm s).1 := by
      intro r s h
      simpa only [Equiv.apply_symm_apply] using he.bead _ _ h
    rw [hA, hA]
    constructor
    · intro hlt
      by_contra hcon
      exact absurd (hkey q p (not_lt.mp hcon)) (not_le.mpr hlt)
    · intro hlt
      exact lt_of_le_of_ne (hkey p q hlt.le) hne
  refine ⟨ChainCat.Hom.φ (reflectHom hface), ?_⟩
  have h1 : coordFlip (ChainCat.Hom.φ (reflectHom hface) ≫ χ) = coordFlip χ' := by
    rw [(reflectHom hface).w]
  rw [coordFlip_trans, hχ'] at h1
  exact Equiv.ext fun p => (coordFlip χ).injective (congrArg (fun E => E p) h1)

/-- **The hom-sets of serial wedges are the shuffles.** -/
theorem coordMapEquiv_bijective (a b : List ℕ+) :
    Function.Bijective fun φ : ⋁a ⟶ ⋁b =>
      (⟨coordMapEquiv φ, isShuffle_coordMapEquiv φ⟩ :
        {e : beadEvent a ≃ beadEvent b // IsShuffle e}) :=
  ⟨fun _ _ h => wedgeHom_ext (congrArg Subtype.val h),
   fun e => (exists_coordMapEquiv_eq e.2).imp fun _ h => Subtype.ext h⟩

/-- `coordMapEquiv` as an equivalence onto the shuffles. -/
noncomputable def wedgeHomEquiv (a b : List ℕ+) :
    (⋁a ⟶ ⋁b) ≃ {e : beadEvent a ≃ beadEvent b // IsShuffle e} :=
  Equiv.ofBijective _ (coordMapEquiv_bijective a b)

end CubeChains

namespace ChainCat

open CubeChains

variable {a b : List ℕ+}

/-! ## `Ch Zbp`: a morphism is its crossing permutation -/

/-- **A chain morphism is its crossing permutation.** -/
theorem hom_ext_of_crossPerm {K : BPSet} {x y : Ch K} {f g : x ⟶ y}
    (h : crossPerm f = crossPerm g) : f = g := by
  refine hom_ext' (wedgeHom_ext (Equiv.ext fun p => ?_))
  have hf := crossPerm_strand f p
  rw [h, crossPerm_strand g p] at hf
  exact (strand y).injective (Fin.ext hf.symm)

theorem crossPerm_injective {K : BPSet} {x y : Ch K} :
    Function.Injective fun f : x ⟶ y => crossPerm f := fun _ _ h => hom_ext_of_crossPerm h

/-- **A chain morphism is its crossing permutation**, read at a fixed strand count — the rigidity
every hom-set classification below is a refinement of. -/
theorem crossPermAt_injective {K : BPSet} {x y : Ch K} {N : ℕ} (h : dimSum x.dims = N) :
    Function.Injective fun f : x ⟶ y => crossPermAt h f := fun _ _ hfg =>
  crossPerm_injective ((Equiv.permCongr (finCongr h)).injective hfg)

/-- A coordinate bijection read through the flattenings — the recipe `crossPerm` follows. -/
def permOfShuffle (h : dimSum a = dimSum b) :
    (beadEvent a ≃ beadEvent b) ≃ Equiv.Perm (Fin (dimSum a)) :=
  Equiv.equivCongr (strand (zObj a)) ((strand (zObj b)).trans (finCongr h).symm)

@[simp] theorem permOfShuffle_coordMapEquiv (φ : ⋁a ⟶ ⋁b) (h : dimSum a = dimSum b) :
    permOfShuffle h (coordMapEquiv φ) = crossPerm (zHom φ) := Equiv.ext fun _ => rfl

/-- **`crossPerm` classifies the hom-sets of `Ch Zbp`**: with `crossPerm_injective`, a permutation
of the strands is realised exactly when the bijection of events it names is a shuffle. -/
theorem exists_crossPerm_eq (h : dimSum a = dimSum b) (σ : Equiv.Perm (Fin (dimSum a))) :
    (∃ f : zObj a ⟶ zObj b, crossPerm f = σ) ↔ IsShuffle ((permOfShuffle h).symm σ) := by
  constructor
  · rintro ⟨f, rfl⟩
    rw [show (permOfShuffle h).symm (crossPerm f) = coordMapEquiv (Hom.φ f) from
      (permOfShuffle h).symm_apply_eq.mpr (permOfShuffle_coordMapEquiv (Hom.φ f) h).symm]
    exact isShuffle_coordMapEquiv _
  · intro hs
    obtain ⟨φ, hφ⟩ := exists_coordMapEquiv_eq hs
    exact ⟨zHom φ, by rw [← permOfShuffle_coordMapEquiv φ h, hφ, Equiv.apply_symm_apply]⟩

/-- **The braid grading is faithful** — for every `K`, since it factors through `Ch Zbp` and a
serial-wedge morphism is its coordinate bijection. -/
instance chBraid_faithful (K : BPSet) : (chBraid K).Faithful where
  map_injective {_ _ f g} h :=
    hom_ext_of_crossPerm (by
      have := congrArg (fun u => permHom _ (GradedHom.val u)) h
      simpa only [chBraid, permHom_ofPerm] using this)

end ChainCat

namespace CubeChains

open ChainCat

/-! ## Monotone maps out of `Fin N`

A monotone map is pinned by its fibre sizes, so precomposing one with a permutation can only stay
monotone by changing nothing.  This is what turns "beads move monotonically" into "blocks are
preserved" for the all-ones source. -/

/-- A down-set of `Fin N` is an initial segment. -/
theorem mem_iff_lt_card_of_downClosed {N : ℕ} {s : Finset (Fin N)}
    (hs : ∀ i j : Fin N, i ≤ j → j ∈ s → i ∈ s) (i : Fin N) : i ∈ s ↔ (i : ℕ) < s.card := by
  constructor
  · intro hi
    have hle := Finset.card_le_card (fun j hj => hs j i (Finset.mem_Iic.mp hj) hi)
    rw [Fin.card_Iic] at hle
    omega
  · intro hlt
    by_contra hi
    have hle := Finset.card_le_card (s := s) (t := Finset.Iio i) fun j hj =>
      Finset.mem_Iio.mpr (lt_of_not_ge fun hij => hi (hs i j hij hj))
    rw [Fin.card_Iio] at hle
    omega

/-- **A monotone map out of `Fin N` is determined by its fibre sizes.** -/
theorem eq_of_monotone_of_card_fibre {N : ℕ} {α : Type*} [LinearOrder α]
    [LocallyFiniteOrderBot α] {u v : Fin N → α}
    (hu : Monotone u) (hv : Monotone v)
    (h : ∀ j : α, (Finset.univ.filter fun i => u i = j).card
       = (Finset.univ.filter fun i => v i = j).card) : u = v := by
  have hcum : ∀ (w : Fin N → α) (j : α),
      (Finset.univ.filter fun i => w i ≤ j).card
        = ∑ j' ∈ Finset.Iic j, (Finset.univ.filter fun i => w i = j').card := by
    intro w j
    rw [Finset.card_eq_sum_card_fiberwise (f := w) (t := Finset.Iic j)
      fun i hi => Finset.mem_Iic.mpr (Finset.mem_filter.mp hi).2]
    refine Finset.sum_congr rfl fun j' hj' => congrArg Finset.card ?_
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun i _ =>
      ⟨fun hh => hh.2, fun hh => ⟨hh ▸ Finset.mem_Iic.mp hj', hh⟩⟩
  have hcard : ∀ j : α, (Finset.univ.filter fun i => u i ≤ j).card
      = (Finset.univ.filter fun i => v i ≤ j).card := fun j => by
    rw [hcum, hcum]; exact Finset.sum_congr rfl fun j' _ => h j'
  have key : ∀ (w : Fin N → α), Monotone w → ∀ (i : Fin N) (j : α),
      (w i ≤ j ↔ (i : ℕ) < (Finset.univ.filter fun i' => w i' ≤ j).card) := fun w hw i j => by
    simpa using mem_iff_lt_card_of_downClosed
      (s := Finset.univ.filter fun i' => w i' ≤ j)
      (fun p q hpq hq => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        le_trans (hw hpq) (Finset.mem_filter.mp hq).2⟩) i
  exact funext fun i => _root_.le_antisymm
    ((key u hu i (v i)).mpr (by rw [hcard]; exact (key v hv i (v i)).mp le_rfl))
    ((key v hv i (u i)).mpr (by rw [← hcard]; exact (key u hu i (u i)).mp le_rfl))

/-- **A permutation that keeps a monotone map monotone changes nothing.** -/
theorem comp_perm_eq_of_monotone {N : ℕ} {α : Type*} [LinearOrder α] [LocallyFiniteOrderBot α]
    {u : Fin N → α} (hu : Monotone u)
    (σ : Equiv.Perm (Fin N)) (h : Monotone (u ∘ σ)) : u ∘ σ = u :=
  eq_of_monotone_of_card_fibre h hu fun j => Finset.card_equiv σ fun i => by simp

/-! ## The bead of a strand -/

/-- The bead of `d` a strand belongs to. -/
def strandBead (d : List ℕ+) (q : Fin (dimSum d)) : Fin d.length :=
  ((strand (zObj d)).symm q).1

@[simp] theorem strandBead_strand (d : List ℕ+) (p : beadEvent d) :
    strandBead d (strand (zObj d) p) = p.1 := by rw [strandBead, Equiv.symm_apply_apply]

/-- **`blockOfPos` names the bead of the flattening** — the `Braid/Blocks` block index, on raw
naturals, is the first component of `pos⁻¹`. -/
theorem blockOfPos_pos : ∀ (d : List ℕ+) (p : beadEvent d),
    blockOfPos (d.map fun x : ℕ+ => (x : ℕ)) (pos p : ℕ) = (p.1 : ℕ)
  | [], p => p.1.elim0
  | c :: rest, ⟨i, k⟩ => by
      induction i using Fin.cases with
      | zero =>
          rw [List.map_cons, pos_cons_zero, Fin.val_zero]
          exact blockOfPos_cons_of_lt _ (by simp)
      | succ j =>
          rw [List.map_cons, pos_cons_succ, blockOfPos_cons_add,
            blockOfPos_pos rest ⟨j, k⟩, Fin.val_succ]

theorem strandBead_val (d : List ℕ+) (q : Fin (dimSum d)) :
    (strandBead d q : ℕ) = blockOfPos (d.map fun x : ℕ+ => (x : ℕ)) (q : ℕ) :=
  (blockOfPos_pos d ((strand (zObj d)).symm q)).symm.trans
    (congrArg (blockOfPos (d.map fun x : ℕ+ => (x : ℕ)))
      (congrArg Fin.val ((strand (zObj d)).apply_symm_apply q)))

theorem strandBead_monotone (d : List ℕ+) : Monotone (strandBead d) := fun i j h => by
  by_contra hc
  have hlt := (strand_lt_iff (zObj d) _ _).mpr (pos_lt_of_fst_lt (not_le.mp hc))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at hlt
  exact absurd h (not_le.mpr hlt)

/-! ## The all-ones chain and the one-bead chain -/

@[simp] theorem dimSum_single (n : ℕ+) : dimSum [n] = (n : ℕ) := by simp [dimSum]

/-- Every bead of an all-edges shape is one event, so an event **is** its bead (`pos_ones`). -/
theorem eq_of_fst_of_ones {dims : List ℕ+} (h : ∀ d ∈ dims, d = 1) {p q : beadEvent dims}
    (hpq : p.1 = q.1) : p = q :=
  pos.injective (Fin.ext (by rw [pos_ones h p, pos_ones h q, hpq]))

theorem ones_replicate (N : ℕ) : ∀ d ∈ 𝟙^N, d = 1 := fun _ hd => List.eq_of_mem_replicate hd

/-- The flattening of the all-ones chain: its strands are its beads. -/
def onesStrand (N : ℕ) : beadEvent (𝟙^N) ≃ Fin N :=
  (strand (zObj _)).trans (finCongr (dimSum_replicate N))

@[simp] theorem onesStrand_val {N : ℕ} (p : beadEvent (𝟙^N)) :
    (onesStrand N p : ℕ) = (p.1 : ℕ) := pos_ones (ones_replicate N) p

/-! ## (1) Into one bead: the Young-coset representatives -/

/-- Into a single bead the bead clause is vacuous: a shuffle is exactly a coordinate enumeration
increasing on each bead of the source. -/
theorem isShuffle_single {a : List ℕ+} {n : ℕ+} (e : beadEvent a ≃ beadEvent [n]) :
    IsShuffle e ↔ ∀ p q : beadEvent a, p.1 = q.1 → pos p < pos q → pos (e p) < pos (e q) :=
  ⟨fun he => he.inner, fun h => ⟨fun p q _ => le_of_eq (Fin.ext (by
    have h1 := (e p).1.isLt
    have h2 := (e q).1.isLt
    simp only [List.length_cons, List.length_nil] at h1 h2
    omega)), h⟩⟩

/-- **The top hom-set**: a wedge map into one bead is exactly an enumeration of the cube's
coordinates increasing on each bead of `a` — the minimal-length representatives of the Young
subgroup's cosets. -/
noncomputable def toSingleHomEquiv (a : List ℕ+) (n : ℕ+) :
    (⋁a ⟶ ⋁[n]) ≃ {e : beadEvent a ≃ beadEvent [n] //
      ∀ p q : beadEvent a, p.1 = q.1 → pos p < pos q → pos (e p) < pos (e q)} :=
  (wedgeHomEquiv a [n]).trans (Equiv.subtypeEquivRight fun e => isShuffle_single e)

/-- Out of the all-ones chain the inner clause is vacuous. -/
theorem isShuffle_of_ones {N : ℕ} {b : List ℕ+}
    (e : beadEvent (𝟙^N) ≃ beadEvent b)
    (hb : ∀ p q, p.1 ≤ q.1 → (e p).1 ≤ (e q).1) : IsShuffle e :=
  ⟨hb, fun _ _ h hlt =>
    absurd (congrArg pos (eq_of_fst_of_ones (ones_replicate N) h)) (ne_of_lt hlt)⟩

/-! ## (2) Out of the all-ones chain: the parabolic subgroup -/

/-- Out of the all-ones chain a shuffle is a permutation of the strands preserving each bead of
`b`: the bead clause makes `strandBead b ∘ σ` monotone, and a monotone map is pinned by its fibre
sizes. -/
theorem isShuffle_ones_iff {b : List ℕ+}
    (e : beadEvent (𝟙^(dimSum b)) ≃ beadEvent b) :
    IsShuffle e ↔ strandBead b ∘ ((onesStrand (dimSum b)).symm.trans
      (e.trans (strand (zObj b)))) = strandBead b := by
  have hkey : ∀ i, strandBead b ((onesStrand (dimSum b)).symm.trans
      (e.trans (strand (zObj b))) i) = (e ((onesStrand (dimSum b)).symm i)).1 := fun i =>
    strandBead_strand b _
  have hle : ∀ p q : beadEvent (𝟙^(dimSum b)),
      p.1 ≤ q.1 ↔ onesStrand (dimSum b) p ≤ onesStrand (dimSum b) q := fun p q => by
    rw [Fin.le_def, Fin.le_def, onesStrand_val, onesStrand_val]
  constructor
  · refine fun he => comp_perm_eq_of_monotone (strandBead_monotone b) _ fun i j h => ?_
    have hb := he.bead ((onesStrand (dimSum b)).symm i) ((onesStrand (dimSum b)).symm j)
      ((hle _ _).mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply]))
    rw [← hkey i, ← hkey j] at hb
    exact hb
  · refine fun h => isShuffle_of_ones e fun p q hpq => ?_
    have hp := hkey (onesStrand (dimSum b) p)
    have hq := hkey (onesStrand (dimSum b) q)
    rw [Equiv.symm_apply_apply] at hp hq
    rw [← hp, ← hq, ← Function.comp_apply (f := strandBead b), ← Function.comp_apply
      (f := strandBead b), h]
    exact strandBead_monotone b ((hle p q).mp hpq)

/-- **`1ᴺ ⟶ b` is the parabolic subgroup**: out of the all-ones chain the realised permutations of
the strands are exactly those preserving each bead of `b`. -/
noncomputable def onesHomEquiv (b : List ℕ+) :
    (⋁(𝟙^(dimSum b)) ⟶ ⋁b) ≃
      {σ : Equiv.Perm (Fin (dimSum b)) // strandBead b ∘ σ = strandBead b} :=
  (wedgeHomEquiv _ b).trans
    (Equiv.subtypeEquiv (Equiv.equivCongr (onesStrand (dimSum b)) (strand (zObj b)))
      fun e => isShuffle_ones_iff e)

/-- Preserving every bead of `b` is membership in the Young subgroup of `b`'s composition. -/
theorem mem_parabolic_iff {b : List ℕ+} (σ : Equiv.Perm (Fin (dimSum b))) :
    σ ∈ parabolic (dimSum b) (b.map fun x : ℕ+ => (x : ℕ)) ↔ strandBead b ∘ σ = strandBead b :=
  ⟨fun h => funext fun i => Fin.ext (by
      rw [Function.comp_apply, strandBead_val, strandBead_val, h i]),
   fun h i => by
     rw [← strandBead_val, ← strandBead_val]
     exact congrArg Fin.val (congrFun h i)⟩

/-- **(3), as a subgroup**: the crossing permutations out of the all-ones chain are the parabolic
subgroup `S_{b₁} × ⋯ × S_{b_k}`. -/
noncomputable def onesHomEquivParabolic (b : List ℕ+) :
    (⋁(𝟙^(dimSum b)) ⟶ ⋁b) ≃
      parabolic (dimSum b) (b.map fun x : ℕ+ => (x : ℕ)) :=
  (onesHomEquiv b).trans (Equiv.subtypeEquivRight fun σ => (mem_parabolic_iff σ).symm)

end CubeChains
