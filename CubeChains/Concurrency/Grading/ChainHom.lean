import CubeChains.Concurrency.Merge.TotalMerge
import CubeChains.Concurrency.Grading.WedgeBraid
import CubeChains.Concurrency.Executions.RunPerm

/-!
# Concurrency/Grading/ChainHom — a wedge map is a chain refining a chain

A serial wedge maps into the cube of its own total dimension (`nonempty_toCube`), and a chain of
the cube is a coordinate system on its events (`coordFlip`), so a wedge map is pinned by the chain
it induces (`wedgeHom_ext_chain`).

A chain's shape is then read as a mathlib `Composition` (`dimComp`), whose `index` is `beadOf`
under the firing order (`beadOf_eq_index`); the hom-sets come off `boundaries` alone.
-/

open CategoryTheory BPSet CubeChain ChainCat

namespace CubeChains

variable {a b d d' : List ℕ+}

/-! ## Chains -/

/-- An all-edges chain has one bead per event. -/
theorem ones_dims_eq {X : BPSet} {n : ℕ} {A : Ch X} (h : ∀ c ∈ A.dims, c = 1)
    (hn : dimSum A.dims = n) : A.dims = 𝟙^n :=
  (eq_replicate_of_ones h).trans
    (congrArg (List.replicate · (1 : ℕ+)) ((dimSum_eq_length_of_ones h).symm.trans hn))

/-- **A chain map out of the all-edges chain is a run of the target**, whenever the target has
`n` events along every chain. -/
def onesHomEquivRun {X : BPSet} {n : ℕ} (hn : ∀ {d : List ℕ+} (_ : ⋁d ⟶ X), dimSum d = n) :
    (⋁(𝟙^n) ⟶ X) ≃ Run X where
  toFun φ := ⟨⟨𝟙^n, φ⟩, fun _ hx => List.eq_of_mem_replicate hx⟩
  invFun r := ⋁≡ (ones_dims_eq r.ones (hn r.map)).symm ≫ r.map
  left_inv φ := Category.id_comp φ
  right_inv r := Run.ext (Obj.mk_eq_mk (ones_dims_eq r.ones (hn r.map)).symm rfl)

/-- **The all-edges chain of a cube is a run of it** — the cube has `N` events along every
chain, so `onesHomEquivRun` applies. -/
def onesChainEquiv (N : ℕ) : (⋁(𝟙^N) ⟶ □N) ≃ Run (□N) :=
  onesHomEquivRun fun φ => wedgeDimSum_eq φ

/-! ## Realising a firing order

A chain of shape `d` fires its coordinates in an order that rises inside each block of `d` — and
every such order occurs, the beads being the blocks of `d` read through it.  The order itself
(`flatten`) and its comparison with the partition (`beadOf`) live in
`Concurrency/Grading/OrderedPartition`; here only `dimComp` enters. -/

/-- **A block map realises the shape its down-sets count out**: the chain assembled from `β` has
shape `d` exactly when the coordinates below each block have the shape's prefix sums for counts. -/
theorem dims_blockChain {N : ℕ} {d : List ℕ+} (hd : dimSum d = N)
    {β : Fin N → Fin (dimComp d hd).length} (hsurj : Function.Surjective β)
    (hcard : ∀ j ≤ d.length,
      (Finset.univ.filter fun r : Fin N => (β r : ℕ) < j).card = beadStart d j) :
    (blockChain β hsurj).dims = d := by
  have hlen : (blockChain β hsurj).dims.length = d.length := by
    rw [length_blockChain, dimComp_length]
  refine eq_of_beadStart_eq hlen fun j hj => ?_
  rw [← card_beadOf_lt, ← hcard j (hlen ▸ hj)]
  exact congrArg Finset.card (Finset.filter_congr fun r _ => by rw [beadOf_blockChain])

/-- **Every order that rises inside each block of `d` is the firing order of a chain of shape
`d`** — its beads are the blocks of `d`, read through the order. -/
theorem exists_chain_flatten {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (ρ : Equiv.Perm (Fin N))
    (hrise : ∀ q q' : Fin N, (dimComp d hd).index (ρ q) = (dimComp d hd).index (ρ q') →
      q < q' → ρ q < ρ q') :
    ∃ χ : ⋁d ⟶ □N, flatten (⟨d, χ⟩ : Ch (□N)) = ρ := by
  suffices hex : ∃ A : Ch (□N), A.dims = d ∧ flatten A = ρ by
    obtain ⟨A, hAdims, hAflat⟩ := hex
    obtain ⟨Ad, Amap⟩ := A
    subst hAdims
    exact ⟨Amap, hAflat⟩
  have hsurj : Function.Surjective (fun q : Fin N => (dimComp d hd).index (ρ q)) := fun j =>
    ⟨ρ.symm ((dimComp d hd).embedding j ⟨0, (dimComp d hd).one_le_blocksFun j⟩), by
      simp only [Equiv.apply_symm_apply, Composition.index_embedding]⟩
  set β : Fin N → Fin (dimComp d hd).length := fun q => (dimComp d hd).index (ρ q) with hβ
  refine ⟨blockChain β hsurj, ?_, ?_⟩
  · refine dims_blockChain hd hsurj fun j _ => ?_
    rw [show beadStart d j = (dimComp d hd).sizeUpTo j from (dimComp_sizeUpTo d hd j).symm,
      ← Composition.sizeUpTo_eq_card]
    exact Finset.card_equiv ρ fun r => by simp [hβ]
  · refine Equiv.ext fun q => ?_
    have key := flatten_apply (blockChain β hsurj) ρ.symm (fun x y hlt => ?_) (ρ q)
    · rwa [Equiv.symm_apply_apply] at key
    have hρ : ρ (ρ.symm x) < ρ (ρ.symm y) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hlt
    rw [beadOf_blockChain, beadOf_blockChain]
    rcases eq_or_lt_of_le ((dimComp d hd).index_monotone (Fin.le_def.mp hρ.le)) with heq | hblt
    · refine Or.inr ⟨Fin.ext (by rw [beadOf_blockChain, beadOf_blockChain]; exact heq), ?_⟩
      by_contra hc
      rcases eq_or_lt_of_le (not_lt.mp hc) with heq2 | hgt
      · exact absurd hρ (by rw [heq2]; exact lt_irrefl _)
      · exact absurd (hrise _ _ (Fin.ext heq.symm) hgt) (asymm hρ)
    · exact Or.inl hblt

/-- **A coordinate's bead is the block its rank falls in** — the dictionary between a chain's
partition and its shape's blocks. -/
theorem beadOf_eq_index {N : ℕ} (A : Ch (□N)) (q : Fin N) :
    (beadOf A q : ℕ) = ((dimComp A.dims (wedgeDimSum_eq A.map)).index (flatten A q) : ℕ) :=
  (index_eq_of_beadStart _ (flatten A q) (flatten_mem_bead A q).1 (flatten_mem_bead A q).2).symm

/-- **A chain is pinned by its shape and its firing order** — `beadOf` reads back off `flatten`
through the shape's own blocks. -/
theorem chain_ext_of_flatten {N : ℕ} {A A' : Ch (□N)} (hd : A.dims = A'.dims)
    (h : flatten A = flatten A') : A = A' := by
  obtain ⟨d, χ⟩ := A
  obtain ⟨d', χ'⟩ := A'
  cases hd
  exact eq_of_beadOf fun q => by rw [beadOf_eq_index, beadOf_eq_index, h]

/-- The **standard chain** of a shape — beads in order, coordinates in order: the chain whose
firing order is the identity. -/
noncomputable def stdChain {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) : ⋁d ⟶ □N :=
  (exists_chain_flatten hd 1 fun _ _ _ h => h).choose

@[simp] theorem flatten_stdChain {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) :
    flatten (⟨d, stdChain hd⟩ : Ch (□N)) = 1 :=
  (exists_chain_flatten hd 1 fun _ _ _ h => h).choose_spec

theorem beadOf_stdChain {N : ℕ} {d : List ℕ+} (hd : dimSum d = N) (q : Fin N) :
    (beadOf (⟨d, stdChain hd⟩ : Ch (□N)) q : ℕ) = ((dimComp d hd).index q : ℕ) := by
  rw [beadOf_eq_index, flatten_stdChain]
  rfl

/-! ## Coarsening -/

/-- `d'` **coarsens** `d`: the same events, and every junction of `d'` is one of `d`. -/
def Coarser (d d' : List ℕ+) : Prop :=
  dimSum d = dimSum d' ∧ boundaries d' ⊆ boundaries d

end CubeChains

namespace ChainCat

open CubeChains

variable {d d' : List ℕ+}

/-! ### `crossPerm` on chains -/

/-- **A chain morphism is the comparison of the two chains' firing orders** — `crossPerm_mul_chart`
at the chart `coordFlip χ`, which `coordFlip_comp` pulls back along the wedge map. -/
theorem crossPerm_mul_flatten {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (χ : ⋁b.dims ⟶ □N) :
    crossPerm h f * flatten (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□N))
      = flatten (⟨b.dims, χ⟩ : Ch (□N)) :=
  (congrArg (crossPerm h f * conjPerm · (strand a.dims h) (Equiv.refl _))
      (coordFlip_comp (Hom.φ f) χ)).trans (crossPerm_mul_chart h f (coordFlip χ))

theorem crossPerm_flatten {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (χ : ⋁b.dims ⟶ □N) (q : Fin N) :
    crossPerm h f (flatten (⟨a.dims, Hom.φ f ≫ χ⟩ : Ch (□N)) q)
      = flatten (⟨b.dims, χ⟩ : Ch (□N)) q :=
  Equiv.ext_iff.mp (crossPerm_mul_flatten h f χ) q

/-- **A chain morphism is its crossing permutation.**  `crossPerm` pins the source chain's firing
order, and a chain is pinned by its shape and firing order (`chain_ext_of_flatten`). -/
theorem hom_ext_of_crossPerm {K : BPSet} {x y : Ch K} {N : ℕ} {h : dimSum x.dims = N} {f g : x ⟶ y}
    (hfg : crossPerm h f = crossPerm h g) : f = g := by
  obtain ⟨χ⟩ := nonempty_toCube y.dims
  have hM : dimSum x.dims = dimSum y.dims := dimSum_eq_of_hom f
  have hfg' : crossPerm hM f = crossPerm hM g := by
    rw [crossPerm_recount h hM f, crossPerm_recount h hM g, hfg]
  have hA : (⟨x.dims, Hom.φ f ≫ χ⟩ : Ch (□(dimSum y.dims))) = ⟨x.dims, Hom.φ g ≫ χ⟩ := by
    refine chain_ext_of_flatten rfl (Equiv.ext fun q => ?_)
    have h1 := crossPerm_flatten hM f χ q
    have h2 := crossPerm_flatten hM g χ q
    rw [hfg'] at h1
    exact (crossPerm hM g).injective (h1.trans h2.symm)
  obtain ⟨hd, hmap⟩ := Obj.eq_mk_of_eq hA
  rw [Subsingleton.elim hd rfl] at hmap
  exact hom_ext' (wedgeHom_ext_chain (χ := χ) (by simpa using hmap))

/-- **Realising a crossing permutation.**  Read the target in its standard chain: `σ` is realised
by an arrow `a ⟶ b` when `σ⁻¹` rises inside each bead of `a` and the beads it induces on the
coordinates sit inside `b`'s (`reflectHom`). -/
theorem exists_crossPerm_of_blocks {a b : List ℕ+} {N : ℕ} (ha : dimSum a = N) (hb : dimSum b = N)
    (σ : Equiv.Perm (Fin N))
    (hrise : ∀ p q : Fin N,
        (dimComp a ha).index (σ⁻¹ p) = (dimComp a ha).index (σ⁻¹ q) →
        p < q → (σ⁻¹ p : Fin N) < (σ⁻¹ q : Fin N))
    (hface : ∀ p q : Fin N,
        ((dimComp b hb).index p : ℕ) ≠ ((dimComp b hb).index q : ℕ) →
        (((dimComp b hb).index p : ℕ) < ((dimComp b hb).index q : ℕ)
            ↔ ((dimComp a ha).index (σ⁻¹ p) : ℕ) < ((dimComp a ha).index (σ⁻¹ q) : ℕ))) :
    ∃ f : zObj a ⟶ zObj b, crossPerm ha f = σ := by
  obtain ⟨x, hx⟩ := exists_chain_flatten ha σ⁻¹ hrise
  set A : Ch (□N) := ⟨a, x⟩ with hA
  have hbeadA : ∀ q, (beadOf A q : ℕ) = ((dimComp a ha).index (σ⁻¹ q) : ℕ) := fun q => by
    rw [beadOf_eq_index, hx]
  have hle : BeadRefines A (⟨b, stdChain hb⟩ : Ch (□N)) := fun p q hpq => by
    rw [beadOf_stdChain, beadOf_stdChain]
    rw [hbeadA, hbeadA] at hpq
    exact not_lt.mp fun hc => absurd ((hface q p (Nat.ne_of_lt hc)).mp hc) (by omega)
  obtain ⟨φ, hφ⟩ : ∃ z : ⋁a ⟶ ⋁b, z ≫ stdChain hb = x := ⟨_, (reflectHom hle).w⟩
  obtain ⟨f, hfφ⟩ : ∃ f : zObj a ⟶ zObj b, Hom.φ f = φ := ⟨⟨φ, Subsingleton.elim _ _⟩, rfl⟩
  refine ⟨f, Equiv.ext fun q => ?_⟩
  have h0 : (⟨(zObj a).dims, Hom.φ f ≫ stdChain hb⟩ : Ch (□N)) = A := by
    rw [hA, hfφ]; exact congrArg _ hφ
  have h2 : flatten (⟨(zObj b).dims, stdChain hb⟩ : Ch (□N)) = 1 := flatten_stdChain hb
  have h1 := crossPerm_flatten ha f (stdChain hb) (σ q)
  rw [h0, hx, h2] at h1
  simpa using h1

/-- **A hom exists exactly at a coarsening** — every wedge map only deletes junctions
(`boundaries_subset_of_wedgeHom`), and every deletion is a bead merge (`exists_W_of_coarser`). -/
theorem nonempty_wedgeHom_iff_coarser : Nonempty (⋁d ⟶ ⋁d') ↔ Coarser d d' :=
  ⟨fun ⟨φ⟩ => ⟨serialWedge_dimSum_eq φ, boundaries_subset_of_wedgeHom φ⟩,
   fun h => (exists_W_of_coarser _ (a := zObj d) (b := zObj d') rfl h.1 h.2).elim
     fun u _ => ⟨Hom.φ u⟩⟩

/-- **The hom-sets of `Ch Zbp` are exactly the coarsenings.** -/
theorem nonempty_hom_iff {a b : Ch Zbp} :
    Nonempty (a ⟶ b) ↔ dimSum a.dims = dimSum b.dims ∧ boundaries b.dims ⊆ boundaries a.dims :=
  ⟨fun ⟨f⟩ => ⟨dimSum_eq_of_hom f, boundaries_subset_of_hom f⟩,
   fun h => (nonempty_wedgeHom_iff_coarser.mpr h).map fun φ => ⟨φ, Subsingleton.elim _ _⟩⟩

end ChainCat
