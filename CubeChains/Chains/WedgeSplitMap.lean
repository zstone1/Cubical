import CubeChains.Chains.WedgeSplit

/-!
# Chains/WedgeSplitMap — the computable morphism split and Segal equivalence

The morphism half of the computable inverse of `chConcat`, and the resulting **computable**
`chSegalC : Ch X × Ch Y ≌ Ch (X ∨ Y)`.

* `leftFactor`/`rightFactor` — factor a map landing in one block through `wedgeInclL`/`wedgeInclR`
  (`wedgeDesc` of the `appendProj`-projected beads, chain via `isCubeChain_of_map_injective`).
* `splitHomData` — `chConcat_map_surjective` as data: `leftFactor`/`rightFactor` for the
  choice-based `factorThruMono`, endpoints derived up-front from `himg` + `append_inter`.
* `chSplit` / `chSegalC` — the inverse functor and the choice-free equivalence.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet CubeChain

namespace ChainCat

variable {a' b' : List ℕ+}

/-- Project each cube of `⋁(a'++b')` to its `⋁a'`-preimage (dropping `db`-block cubes). -/
def leftCubes (l : List (Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ))) :
    List (Σ n : ℕ+, (⋁a').cells (n : ℕ)) :=
  l.filterMap fun c => (appendProjL a' b' c.1 c.1.pos c.2).map fun r => ⟨c.1, r⟩

/-- If every cube projects (lands in the `a'`-block), re-including recovers the original list. -/
theorem leftCubes_push (l : List (Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ)))
    (hall : ∀ c ∈ l, (appendProjL a' b' c.1 c.1.pos c.2).isSome) :
    (leftCubes l).map (fun c => (⟨c.1, (wedgeInclL a' b')⟪(c.1 : ℕ)⟫ c.2⟩ :
        Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ))) = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [leftCubes, List.filterMap_cons]
    rcases hc : appendProjL a' b' c.1 c.1.pos c.2 with _ | r
    · exact absurd hc (by have := hall c (List.mem_cons_self ..); rw [hc] at this; simp at this)
    · rw [Option.map_some, List.map_cons]
      refine congrArg₂ _ ?_ (ih fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))
      have := appendProjL_spec a' b' c.1 c.1.pos c.2 r hc
      exact Sigma.ext rfl (heq_of_eq this)

/-- Projection preserves the dimension list. -/
theorem leftCubes_dims (l : List (Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ)))
    (hall : ∀ c ∈ l, (appendProjL a' b' c.1 c.1.pos c.2).isSome) :
    (leftCubes l).map (·.1) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [leftCubes, List.filterMap_cons]
    rcases hc : appendProjL a' b' c.1 c.1.pos c.2 with _ | r
    · exact absurd hc (by have := hall c (List.mem_cons_self ..); rw [hc] at this; simp at this)
    · rw [Option.map_some, List.map_cons, List.map_cons]
      exact congrArg (c.1 :: ·) (ih fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

variable {da : List ℕ+} (ρ : (⋁da).toPsh ⟶ (⋁(a' ++ b')).toPsh)

/-- Projected beads recover the original dimension list. -/
theorem leftCubes_hdims
    (hall : ∀ c ∈ wedgeToCubes ⟨da, ρ⟩, (appendProjL a' b' c.1 c.1.pos c.2).isSome) :
    (leftCubes (wedgeToCubes ⟨da, ρ⟩)).map (·.1) = da :=
  (leftCubes_dims (wedgeToCubes ⟨da, ρ⟩) hall).trans (wedgeToCubes_dims da ρ)

/-- The projected beads form a chain in `⋁a'` (reflection of the pushed chain). -/
theorem leftCubes_isChain
    (hall : ∀ c ∈ wedgeToCubes ⟨da, ρ⟩, (appendProjL a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclL a' b')⟪0⟫ (⋁a').init = ρ⟪0⟫ (⋁da).init)
    (hfinal : (wedgeInclL a' b')⟪0⟫ (⋁a').final = ρ⟪0⟫ (⋁da).final) :
    IsCubeChain (⋁a').init (leftCubes (wedgeToCubes ⟨da, ρ⟩)) (⋁a').final := by
  refine isCubeChain_of_map_injective (wedgeInclL a' b')
    (fun k => wedgeInclL_app_injective a' b' k) _ (⋁a').init (⋁a').final ?_
  rw [leftCubes_push (wedgeToCubes ⟨da, ρ⟩) hall, hinit, hfinal]
  exact wedgeToCubes_isCubeChain da ρ

theorem wedgeToCubes_eqToHom' {K : BPSet} {d₁ d₂ : List ℕ+} (h : d₁ = d₂)
    (φ : (⋁d₂).toPsh ⟶ K.toPsh) :
    wedgeToCubes ⟨d₁, eqToHom (congrArg (fun l => (⋁l).toPsh) h) ≫ φ⟩ = wedgeToCubes ⟨d₂, φ⟩ := by
  subst h; simp

theorem serialWedge_eqToHom_init' {d₁ d₂ : List ℕ+} (hd : d₂ = d₁) :
    (eqToHom (congrArg (fun d => (⋁d).toPsh) hd.symm))⟪0⟫ (⋁d₁).init = (⋁d₂).init := by
  subst hd; simp

/-- **Computable factorization through `wedgeInclL`.**  For `ρ` whose beads land in the `a'`-block,
`leftFactor` is the unique `⋁da ⟶ ⋁a'` with `leftFactor ≫ wedgeInclL = ρ`, built by `wedgeDesc`
from the projected beads (vertices rebuilt for free). -/
def leftFactor
    (hall : ∀ c ∈ wedgeToCubes ⟨da, ρ⟩, (appendProjL a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclL a' b')⟪0⟫ (⋁a').init = ρ⟪0⟫ (⋁da).init)
    (hfinal : (wedgeInclL a' b')⟪0⟫ (⋁a').final = ρ⟪0⟫ (⋁da).final) :
    (⋁da).toPsh ⟶ (⋁a').toPsh :=
  eqToHom (congrArg (fun l => (⋁l).toPsh) (leftCubes_hdims ρ hall).symm)
    ≫ (wedgeDesc (⋁a').init (⋁a').final _ (leftCubes_isChain ρ hall hinit hfinal)).map

theorem leftFactor_comp
    (hall : ∀ c ∈ wedgeToCubes ⟨da, ρ⟩, (appendProjL a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclL a' b')⟪0⟫ (⋁a').init = ρ⟪0⟫ (⋁da).init)
    (hfinal : (wedgeInclL a' b')⟪0⟫ (⋁a').final = ρ⟪0⟫ (⋁da).final) :
    leftFactor ρ hall hinit hfinal ≫ wedgeInclL a' b' = ρ := by
  refine wedgeToCubes_inj da _ ρ ?_ ?_
  · simp only [leftFactor, Category.assoc]
    rw [wedgeToCubes_eqToHom' (leftCubes_hdims ρ hall).symm,
      wedgeToCubes_comp, wedgeToCubes_wedgeDesc, leftCubes_push (wedgeToCubes ⟨da, ρ⟩) hall]
  · have key : (leftFactor ρ hall hinit hfinal)⟪0⟫ (⋁da).init = (⋁a').init := by
      change (wedgeDesc (⋁a').init (⋁a').final _ (leftCubes_isChain ρ hall hinit hfinal)).map⟪0⟫
          ((eqToHom (congrArg (fun l => (⋁l).toPsh) (leftCubes_hdims ρ hall).symm))⟪0⟫
            (⋁da).init) = (⋁a').init
      rw [serialWedge_eqToHom_init' (leftCubes_hdims ρ hall)]
      exact (wedgeDesc _ _ _ _).init_spec
    change (wedgeInclL a' b')⟪0⟫ ((leftFactor ρ hall hinit hfinal)⟪0⟫ (⋁da).init) = ρ⟪0⟫ (⋁da).init
    rw [key]; exact hinit

/-! ### The symmetric right projection / factorization -/

/-- Positive-dim right projection: recover the `db`-block cell (peel `da` via `inr`). -/
def appendProjR : (da db : List ℕ+) → (m : ℕ) → 1 ≤ m →
    (⋁(da ++ db)).cells m → Option ((⋁db).cells m)
  | [], _, _, _, z => some z
  | n :: da', db, m, hm, z =>
      match wedge2CellSide (□(n : ℕ)) (⋁(da' ++ db)) hm z with
      | Sum.inl _ => none
      | Sum.inr w => appendProjR da' db m hm w

theorem appendProjR_spec : ∀ (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m)
    (z : (⋁(da ++ db)).cells m) (r : (⋁db).cells m),
    appendProjR da db m hm z = some r → (wedgeInclR da db)⟪m⟫ r = z
  | [], db, m, hm, z, r, h => by
      rw [appendProjR] at h
      obtain rfl := Option.some_inj.mp h
      exact wedgeInclR_nil_left_app db m z
  | n :: da', db, m, hm, z, r, h => by
      have hz := wedge2CellSide_elim (□(n : ℕ)) (⋁(da' ++ db)) hm z
      rw [appendProjR] at h
      split at h
      · rename_i x hcs; simp only [reduceCtorEq] at h
      · rename_i w hcs
        rw [hcs, Sum.elim_inr] at hz
        have ih := appendProjR_spec da' db m hm w r h
        rw [← hz, ← ih]
        exact wedgeInclR_cons_app n da' db m r

theorem appendProjR_wedgeInclR : ∀ (da db : List ℕ+) (m : ℕ) (hm : 1 ≤ m) (r : (⋁db).cells m),
    appendProjR da db m hm ((wedgeInclR da db)⟪m⟫ r) = some r
  | [], db, m, hm, r => by rw [appendProjR, wedgeInclR_nil_left_app]
  | n :: da', db, m, hm, r => by
      rw [appendProjR, wedgeInclR_cons_app n da' db m r]
      simp only [wedge2CellSide_inr, appendProjR_wedgeInclR da' db m hm r]

/-- Project each cube of `⋁(a'++b')` to its `⋁b'`-preimage (dropping `da`-block cubes). -/
def rightCubes (l : List (Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ))) :
    List (Σ n : ℕ+, (⋁b').cells (n : ℕ)) :=
  l.filterMap fun c => (appendProjR a' b' c.1 c.1.pos c.2).map fun r => ⟨c.1, r⟩

theorem rightCubes_push (l : List (Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ)))
    (hall : ∀ c ∈ l, (appendProjR a' b' c.1 c.1.pos c.2).isSome) :
    (rightCubes l).map (fun c => (⟨c.1, (wedgeInclR a' b')⟪(c.1 : ℕ)⟫ c.2⟩ :
        Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ))) = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [rightCubes, List.filterMap_cons]
    rcases hc : appendProjR a' b' c.1 c.1.pos c.2 with _ | r
    · exact absurd hc (by have := hall c (List.mem_cons_self ..); rw [hc] at this; simp at this)
    · rw [Option.map_some, List.map_cons]
      refine congrArg₂ _ ?_ (ih fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))
      exact Sigma.ext rfl (heq_of_eq (appendProjR_spec a' b' c.1 c.1.pos c.2 r hc))

theorem rightCubes_dims (l : List (Σ n : ℕ+, (⋁(a' ++ b')).cells (n : ℕ)))
    (hall : ∀ c ∈ l, (appendProjR a' b' c.1 c.1.pos c.2).isSome) :
    (rightCubes l).map (·.1) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [rightCubes, List.filterMap_cons]
    rcases hc : appendProjR a' b' c.1 c.1.pos c.2 with _ | r
    · exact absurd hc (by have := hall c (List.mem_cons_self ..); rw [hc] at this; simp at this)
    · rw [Option.map_some, List.map_cons, List.map_cons]
      exact congrArg (c.1 :: ·) (ih fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

variable {dc : List ℕ+} (σ : (⋁dc).toPsh ⟶ (⋁(a' ++ b')).toPsh)

theorem rightCubes_hdims
    (hall : ∀ c ∈ wedgeToCubes ⟨dc, σ⟩, (appendProjR a' b' c.1 c.1.pos c.2).isSome) :
    (rightCubes (wedgeToCubes ⟨dc, σ⟩)).map (·.1) = dc :=
  (rightCubes_dims (wedgeToCubes ⟨dc, σ⟩) hall).trans (wedgeToCubes_dims dc σ)

theorem rightCubes_isChain
    (hall : ∀ c ∈ wedgeToCubes ⟨dc, σ⟩, (appendProjR a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclR a' b')⟪0⟫ (⋁b').init = σ⟪0⟫ (⋁dc).init)
    (hfinal : (wedgeInclR a' b')⟪0⟫ (⋁b').final = σ⟪0⟫ (⋁dc).final) :
    IsCubeChain (⋁b').init (rightCubes (wedgeToCubes ⟨dc, σ⟩)) (⋁b').final := by
  refine isCubeChain_of_map_injective (wedgeInclR a' b')
    (fun k => wedgeInclR_app_injective a' b' k) _ (⋁b').init (⋁b').final ?_
  rw [rightCubes_push (wedgeToCubes ⟨dc, σ⟩) hall, hinit, hfinal]
  exact wedgeToCubes_isCubeChain dc σ

/-- Computable factorization through `wedgeInclR`. -/
def rightFactor
    (hall : ∀ c ∈ wedgeToCubes ⟨dc, σ⟩, (appendProjR a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclR a' b')⟪0⟫ (⋁b').init = σ⟪0⟫ (⋁dc).init)
    (hfinal : (wedgeInclR a' b')⟪0⟫ (⋁b').final = σ⟪0⟫ (⋁dc).final) :
    (⋁dc).toPsh ⟶ (⋁b').toPsh :=
  eqToHom (congrArg (fun l => (⋁l).toPsh) (rightCubes_hdims σ hall).symm)
    ≫ (wedgeDesc (⋁b').init (⋁b').final _ (rightCubes_isChain σ hall hinit hfinal)).map

theorem rightFactor_comp
    (hall : ∀ c ∈ wedgeToCubes ⟨dc, σ⟩, (appendProjR a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclR a' b')⟪0⟫ (⋁b').init = σ⟪0⟫ (⋁dc).init)
    (hfinal : (wedgeInclR a' b')⟪0⟫ (⋁b').final = σ⟪0⟫ (⋁dc).final) :
    rightFactor σ hall hinit hfinal ≫ wedgeInclR a' b' = σ := by
  refine wedgeToCubes_inj dc _ σ ?_ ?_
  · simp only [rightFactor, Category.assoc]
    rw [wedgeToCubes_eqToHom' (rightCubes_hdims σ hall).symm,
      wedgeToCubes_comp, wedgeToCubes_wedgeDesc, rightCubes_push (wedgeToCubes ⟨dc, σ⟩) hall]
  · have key : (rightFactor σ hall hinit hfinal)⟪0⟫ (⋁dc).init = (⋁b').init := by
      change (wedgeDesc (⋁b').init (⋁b').final _ (rightCubes_isChain σ hall hinit hfinal)).map⟪0⟫
          ((eqToHom (congrArg (fun l => (⋁l).toPsh) (rightCubes_hdims σ hall).symm))⟪0⟫
            (⋁dc).init) = (⋁b').init
      rw [serialWedge_eqToHom_init' (rightCubes_hdims σ hall)]
      exact (wedgeDesc _ _ _ _).init_spec
    change (wedgeInclR a' b')⟪0⟫ ((rightFactor σ hall hinit hfinal)⟪0⟫ (⋁dc).init) = σ⟪0⟫ (⋁dc).init
    rw [key]; exact hinit

/-! ### The computable morphism split -/

variable {X Y : BPSet}

/-- **The computable morphism split of `chConcat`** (data form of `chConcat_map_surjective`):
`leftFactor`/`rightFactor` in place of the choice-based `factorThruMono`. -/
def splitHomData {ab ab' : Obj X × Obj Y}
    (hh : (chConcat X Y).obj ab ⟶ (chConcat X Y).obj ab') :
    Σ' fg : ab ⟶ ab', (chConcat X Y).map fg = hh := by
  obtain ⟨a, b⟩ := ab
  obtain ⟨a', b'⟩ := ab'
  let hh2 : (⟨a.dims ++ b.dims, concatChainMap X Y a b⟩ : Obj (wedge2 X Y))
      ⟶ ⟨a'.dims ++ b'.dims, concatChainMap X Y a' b'⟩ := hh
  set ρL := wedgeInclL a.dims b.dims ≫ hh2ᵂ with hρL
  set ρR := wedgeInclR a.dims b.dims ≫ hh2ᵂ with hρR
  have hwhom : hh2ᵂ ≫ (concatChainMap X Y a' b').hom = (concatChainMap X Y a b).hom := by
    have hw := congrArg BPSet.Hom.hom hh2.w
    simpa only [comp_hom] using hw
  have hcompL : ρL ≫ (concatChainMap X Y a' b').hom
      = a.map.hom ≫ Glue.inl X.finalVertex Y.initVertex := by
    rw [hρL]; simp only [Category.assoc, hwhom]; exact concatChainMap_inclL X Y a b
  have hcompR : ρR ≫ (concatChainMap X Y a' b').hom
      = b.map.hom ≫ Glue.inr X.finalVertex Y.initVertex := by
    rw [hρR]; simp only [Category.assoc, hwhom]; exact concatChainMap_inclR X Y a b
  have hposL : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (⋁a.dims).cells m),
      ∃ w, (wedgeInclL a'.dims b'.dims)⟪m⟫ w = ρL⟪m⟫ z := by
    intro m hm z
    rcases Types.eq_or_eq_of_isPushout (append_isPushout_app a'.dims b'.dims m)
        (ρL⟪m⟫ z) with ⟨u, hu⟩ | ⟨w, hw⟩
    · exfalso
      have hL : (concatChainMap X Y a' b').hom⟪m⟫ ((wedgeInclR a'.dims b'.dims)⟪m⟫ u)
          = (Glue.inr X.finalVertex Y.initVertex)⟪m⟫ (b'.map.hom⟪m⟫ u) := by
        have hc := congrArg (fun t : (⋁b'.dims).toPsh ⟶ (wedge2 X Y).toPsh => t⟪m⟫ u)
          (concatChainMap_inclR X Y a' b')
        simp only [NatTrans.comp_app, types_comp_apply] at hc
        rw [hc]
        change (b'.map.hom ≫ Glue.inr X.finalVertex Y.initVertex)⟪m⟫ u = _
        simp only [NatTrans.comp_app, types_comp_apply]
      have hR : (concatChainMap X Y a' b').hom⟪m⟫ (ρL⟪m⟫ z)
          = (Glue.inl X.finalVertex Y.initVertex)⟪m⟫ (a.map.hom⟪m⟫ z) := by
        have hc := congrArg (fun t : (⋁a.dims).toPsh ⟶ (wedge2 X Y).toPsh => t⟪m⟫ z) hcompL
        simpa only [NatTrans.comp_app, types_comp_apply] using hc
      exact CubeChain.wedge2_inl_ne_inr X Y hm _ _ (hR.symm.trans (hu ▸ hL))
    · exact ⟨w, hw⟩
  have hposR : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (⋁b.dims).cells m),
      ∃ w, (wedgeInclR a'.dims b'.dims)⟪m⟫ w = ρR⟪m⟫ z := by
    intro m hm z
    rcases Types.eq_or_eq_of_isPushout (append_isPushout_app a'.dims b'.dims m)
        (ρR⟪m⟫ z) with ⟨u, hu⟩ | ⟨w, hw⟩
    · exact ⟨u, hu⟩
    · exfalso
      have hR : (concatChainMap X Y a' b').hom⟪m⟫ (ρR⟪m⟫ z)
          = (Glue.inr X.finalVertex Y.initVertex)⟪m⟫ (b.map.hom⟪m⟫ z) := by
        have hc := congrArg (fun t : (⋁b.dims).toPsh ⟶ (wedge2 X Y).toPsh => t⟪m⟫ z) hcompR
        simpa only [NatTrans.comp_app, types_comp_apply] using hc
      have hL : (concatChainMap X Y a' b').hom⟪m⟫ ((wedgeInclL a'.dims b'.dims)⟪m⟫ w)
          = (Glue.inl X.finalVertex Y.initVertex)⟪m⟫ (a'.map.hom⟪m⟫ w) := by
        have hc := congrArg (fun t : (⋁a'.dims).toPsh ⟶ (wedge2 X Y).toPsh => t⟪m⟫ w)
          (concatChainMap_inclL X Y a' b')
        simp only [NatTrans.comp_app, types_comp_apply] at hc
        rw [hc]
        change (a'.map.hom ≫ Glue.inl X.finalVertex Y.initVertex)⟪m⟫ w = _
        simp only [NatTrans.comp_app, types_comp_apply]
      exact CubeChain.wedge2_inl_ne_inr X Y hm _ _ (hL.symm.trans (hw ▸ hR))
  have hρLinit : ρL⟪0⟫ (⋁a.dims).init = (⋁(a'.dims ++ b'.dims)).init := by
    rw [hρL, NatTrans.comp_app, types_comp_apply,
      app_init_eq_of_initVertex (wedgeInclL a.dims b.dims) (wedgeInclL_initVertex a.dims b.dims)]
    exact hh2.φ.app_init
  have hρRfinal : ρR⟪0⟫ (⋁b.dims).final = (⋁(a'.dims ++ b'.dims)).final := by
    rw [hρR, NatTrans.comp_app, types_comp_apply,
      app_final_eq_of_finalVertex (wedgeInclR a.dims b.dims) (wedgeInclR_finalVertex a.dims b.dims)]
    exact hh2.φ.app_final
  have hbaseL : a.dims = [] → ∀ (z : (⋁a.dims).cells 0),
      ∃ w, (wedgeInclL a'.dims b'.dims)⟪0⟫ w = ρL⟪0⟫ z := by
    intro hda z
    refine ⟨(⋁a'.dims).init, ?_⟩
    rw [app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
      (wedgeInclL_initVertex a'.dims b'.dims)]
    have hsub : Subsingleton ((⋁a.dims).cells 0) := by
      rw [hda]; exact inferInstanceAs (Subsingleton ((□0).cells 0))
    rw [hsub.elim z (⋁a.dims).init]; exact hρLinit.symm
  have hbaseR : b.dims = [] → ∀ (z : (⋁b.dims).cells 0),
      ∃ w, (wedgeInclR a'.dims b'.dims)⟪0⟫ w = ρR⟪0⟫ z := by
    intro hdb z
    refine ⟨(⋁b'.dims).final, ?_⟩
    rw [app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
      (wedgeInclR_finalVertex a'.dims b'.dims)]
    have hsub : Subsingleton ((⋁b.dims).cells 0) := by
      rw [hdb]; exact inferInstanceAs (Subsingleton ((□0).cells 0))
    rw [hsub.elim z (⋁b.dims).final]; exact hρRfinal.symm
  have himgL := himg_reduce a.dims ρL (wedgeInclL a'.dims b'.dims) hposL hbaseL
  have himgR := himg_reduce b.dims ρR (wedgeInclR a'.dims b'.dims) hposR hbaseR
  -- Endpoints for `leftFactor`/`rightFactor`, derived up-front (via `himg` + `append_inter`).
  have hinit_L : (wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).init = ρL⟪0⟫ (⋁a.dims).init := by
    rw [app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
      (wedgeInclL_initVertex a'.dims b'.dims)]; exact hρLinit.symm
  have hfinal_R : (wedgeInclR a'.dims b'.dims)⟪0⟫ (⋁b'.dims).final = ρR⟪0⟫ (⋁b.dims).final := by
    rw [app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
      (wedgeInclR_finalVertex a'.dims b'.dims)]; exact hρRfinal.symm
  have hjeq : ρL⟪0⟫ (⋁a.dims).final = ρR⟪0⟫ (⋁b.dims).init := by
    rw [hρL, hρR]; simp only [NatTrans.comp_app, types_comp_apply]
    rw [wedgeInclL_final_eq_wedgeInclR_init a.dims b.dims]
  have hfinal_L : (wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).final = ρL⟪0⟫ (⋁a.dims).final := by
    obtain ⟨wL, hwL⟩ := himgL 0 (⋁a.dims).final
    obtain ⟨wR, hwR⟩ := himgR 0 (⋁b.dims).init
    obtain ⟨hwLeq, _⟩ := append_inter a'.dims b'.dims wL wR (by rw [hwL, hwR, hjeq])
    rw [← hwLeq, hwL]
  have hinit_R : (wedgeInclR a'.dims b'.dims)⟪0⟫ (⋁b'.dims).init = ρR⟪0⟫ (⋁b.dims).init := by
    obtain ⟨wL, hwL⟩ := himgL 0 (⋁a.dims).final
    obtain ⟨wR, hwR⟩ := himgR 0 (⋁b.dims).init
    obtain ⟨_, hwReq⟩ := append_inter a'.dims b'.dims wL wR (by rw [hwL, hwR, hjeq])
    rw [← hwReq, hwR]
  have hall_L : ∀ c ∈ wedgeToCubes ⟨a.dims, ρL⟩,
      (appendProjL a'.dims b'.dims c.1 c.1.pos c.2).isSome := by
    have hcomp := wedgeToCubes_comp ρL a.dims (𝟙 (⋁a.dims).toPsh)
    rw [Category.id_comp] at hcomp
    rw [hcomp]; intro c hc
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨w, hw⟩ := himgL (d.1 : ℕ) d.2
    simp only [← hw, appendProjL_wedgeInclL, Option.isSome_some]
  have hall_R : ∀ c ∈ wedgeToCubes ⟨b.dims, ρR⟩,
      (appendProjR a'.dims b'.dims c.1 c.1.pos c.2).isSome := by
    have hcomp := wedgeToCubes_comp ρR b.dims (𝟙 (⋁b.dims).toPsh)
    rw [Category.id_comp] at hcomp
    rw [hcomp]; intro c hc
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨w, hw⟩ := himgR (d.1 : ℕ) d.2
    simp only [← hw, appendProjR_wedgeInclR, Option.isSome_some]
  set fhom := leftFactor ρL hall_L hinit_L hfinal_L with hfhom
  set ghom := rightFactor ρR hall_R hinit_R hfinal_R with hghom
  have hfhom_comp : fhom ≫ wedgeInclL a'.dims b'.dims = ρL :=
    leftFactor_comp ρL hall_L hinit_L hfinal_L
  have hghom_comp : ghom ≫ wedgeInclR a'.dims b'.dims = ρR :=
    rightFactor_comp ρR hall_R hinit_R hfinal_R
  have hfval : ∀ (c : (⋁a.dims).cells 0),
      (wedgeInclL a'.dims b'.dims)⟪0⟫ (fhom⟪0⟫ c) = ρL⟪0⟫ c := by
    intro c
    have hc := congrArg (fun t => t.app (op ▫0) c) hfhom_comp
    simpa only [NatTrans.comp_app, types_comp_apply] using hc
  have hgval : ∀ (c : (⋁b.dims).cells 0),
      (wedgeInclR a'.dims b'.dims)⟪0⟫ (ghom⟪0⟫ c) = ρR⟪0⟫ c := by
    intro c
    have hc := congrArg (fun t => t.app (op ▫0) c) hghom_comp
    simpa only [NatTrans.comp_app, types_comp_apply] using hc
  have hp : (wedgeInclL a'.dims b'.dims)⟪0⟫ (fhom⟪0⟫ (⋁a.dims).final)
      = (wedgeInclR a'.dims b'.dims)⟪0⟫ (ghom⟪0⟫ (⋁b.dims).init) := by
    rw [hfval, hgval, hρL, hρR]
    simp only [NatTrans.comp_app, types_comp_apply]
    rw [wedgeInclL_final_eq_wedgeInclR_init a.dims b.dims]
  obtain ⟨hfin, hginit⟩ := append_inter a'.dims b'.dims _ _ hp
  have hfinit : fhom⟪0⟫ (⋁a.dims).init = (⋁a'.dims).init := by
    apply wedgeInclL_app_injective a'.dims b'.dims (op ▫0)
    rw [hfval, hρLinit, app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
      (wedgeInclL_initVertex a'.dims b'.dims)]
  have hgfinal : ghom⟪0⟫ (⋁b.dims).final = (⋁b'.dims).final := by
    apply wedgeInclR_app_injective a'.dims b'.dims (op ▫0)
    rw [hgval, hρRfinal, app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
      (wedgeInclR_finalVertex a'.dims b'.dims)]
  let fφ : ⋁a.dims ⟶ ⋁a'.dims := { hom := fhom, app_init := hfinit, app_final := hfin }
  let gφ : ⋁b.dims ⟶ ⋁b'.dims := { hom := ghom, app_init := hginit, app_final := hgfinal }
  have fw : fφ ≫ a'.map = a.map := by
    apply hom_ext; rw [comp_hom]
    change fhom ≫ a'.map.hom = a.map.hom
    have e : ρL ≫ (concatChainMap X Y a' b').hom
        = fhom ≫ a'.map.hom ≫ Glue.inl X.finalVertex Y.initVertex := by
      rw [← hfhom_comp, Category.assoc]; congr 1; exact concatChainMap_inclL X Y a' b'
    apply (cancel_mono (Glue.inl X.finalVertex Y.initVertex)).mp
    rw [Category.assoc, ← e, hcompL]
  have gw : gφ ≫ b'.map = b.map := by
    apply hom_ext; rw [comp_hom]
    change ghom ≫ b'.map.hom = b.map.hom
    have e : ρR ≫ (concatChainMap X Y a' b').hom
        = ghom ≫ b'.map.hom ≫ Glue.inr X.finalVertex Y.initVertex := by
      rw [← hghom_comp, Category.assoc]; congr 1; exact concatChainMap_inclR X Y a' b'
    apply (cancel_mono (Glue.inr X.finalVertex Y.initVertex)).mp
    rw [Category.assoc, ← e, hcompR]
  refine ⟨((⟨fφ, fw⟩ : (a : Obj X) ⟶ a'), (⟨gφ, gw⟩ : (b : Obj Y) ⟶ b')), ?_⟩
  apply hom_ext'
  change concatHomφ (⟨fφ, fw⟩ : (a : Obj X) ⟶ a') (⟨gφ, gw⟩ : (b : Obj Y) ⟶ b') = hh2.φ
  apply hom_ext
  refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
  · rw [concatHomφ_inclL]
    change fhom ≫ wedgeInclL a'.dims b'.dims = wedgeInclL a.dims b.dims ≫ hh2ᵂ
    rw [hfhom_comp, hρL]
  · rw [concatHomφ_inclR]
    change ghom ≫ wedgeInclR a'.dims b'.dims = wedgeInclR a.dims b.dims ≫ hh2ᵂ
    rw [hghom_comp, hρR]

/-! ### The computable equivalence -/

variable (h : (wedge2 X Y).AdmitsAltitude)

/-- The morphism half of the computable inverse, via `splitHomData`. -/
def chSplitMap {c c' : Ch (wedge2 X Y)} (f : c ⟶ c') : splitObj h c ⟶ splitObj h c' :=
  (splitHomData (eqToHom (chConcat_obj_splitObj h c) ≫ f
    ≫ eqToHom (chConcat_obj_splitObj h c').symm)).1

theorem chSplitMap_spec {c c' : Ch (wedge2 X Y)} (f : c ⟶ c') :
    (chConcat X Y).map (chSplitMap h f)
      = eqToHom (chConcat_obj_splitObj h c) ≫ f ≫ eqToHom (chConcat_obj_splitObj h c').symm :=
  (splitHomData _).2

/-- The computable inverse functor of `chConcat`. -/
def chSplit : Ch (wedge2 X Y) ⥤ (Ch X × Ch Y) where
  obj := splitObj h
  map := chSplitMap h
  map_id c := (chConcat X Y).map_injective (by
    rw [chSplitMap_spec, CategoryTheory.Functor.map_id]; simp)
  map_comp f g := (chConcat X Y).map_injective (by
    rw [CategoryTheory.Functor.map_comp, chSplitMap_spec, chSplitMap_spec, chSplitMap_spec]; simp)

/-- **The computable Segal equivalence.**  `Ch(X ∨ Y) ≌ Ch X × Ch Y`, built from the explicit
inverse `chSplit` (no `Classical.choice`). -/
def chSegalC : (Ch X × Ch Y) ≌ Ch (wedge2 X Y) :=
  CategoryTheory.Equivalence.mk (chConcat X Y) (chSplit h)
    (NatIso.ofComponents (fun p => eqToIso (splitObj_chConcat_obj h p.1 p.2).symm) (by
      intro p p' f
      apply (chConcat X Y).map_injective
      simp only [Functor.comp_map, Functor.map_comp, chSplit, Functor.id_map]
      simp [chSplitMap_spec, eqToHom_map]))
    (NatIso.ofComponents (fun c => eqToIso (chConcat_obj_splitObj h c)) (by
      intro c c' f
      simp only [Functor.comp_map, chSplit, chSplitMap_spec, Functor.id_map]
      simp))

end ChainCat



