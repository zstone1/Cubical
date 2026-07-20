import CubeChains.Chains.WedgeSplit

/-!
# Chains/WedgeSplitMap — the computable morphism split and Segal equivalence

The morphism half of the computable inverse of `chConcat`, and the resulting **computable**
`chSegalC : Ch X × Ch Y ≌ Ch (X ∨ Y)`.

* `BlockProj` / `projFactor` — factor a map whose beads land in one block through that block's
  inclusion, side-agnostically; `leftFactor`/`rightFactor` instantiate it at the two halves.
* `splitHomData` — fullness of `chConcat` as data, with endpoints derived up-front from
  `himg` + `append_inter`.
* `chSplit` / `chSegalC` — the inverse functor and the choice-free equivalence.
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet CubeChain

namespace ChainCat

/-! ### Generic computable factorization through a block inclusion

A map `ρ : ⋁d ⟶ ⋁w` whose beads all land in a sub-block factors through that block's inclusion,
computably: project the beads, then rebuild by `wedgeDesc` (which recovers the vertices for free).
Instantiated at both halves of an append below; nothing here knows which side it is on. -/

/-- A **block projection**: a mono `incl` onto a sub-block of `⋁w`, together with a computable
partial inverse on bead cells.  `proj` is only ever asked about levels `m ≥ 1`. -/
structure BlockProj (w e : List ℕ+) where
  incl : (⋁e).toPsh ⟶ (⋁w).toPsh
  proj : ∀ (m : ℕ), 1 ≤ m → (⋁w).cells m → Option ((⋁e).cells m)
  spec : ∀ (m : ℕ) (hm : 1 ≤ m) (z : (⋁w).cells m) (r : (⋁e).cells m),
    proj m hm z = some r → incl⟪m⟫ r = z
  sec : ∀ (m : ℕ) (hm : 1 ≤ m) (r : (⋁e).cells m), proj m hm (incl⟪m⟫ r) = some r
  inj : ∀ n : ℕ, Function.Injective (incl⟪n⟫)

section Factor

variable {w e d : List ℕ+} (P : BlockProj w e)

/-- The cubes of a list in `⋁w` that `P` carries into its block, dropping the rest. -/
def projCubes (l : List (Σ n : ℕ+, (⋁w).cells (n : ℕ))) :
    List (Σ n : ℕ+, (⋁e).cells (n : ℕ)) :=
  l.filterMap fun c => (P.proj c.1 c.1.pos c.2).map fun r => ⟨c.1, r⟩

/-- If every cube projects, re-including recovers the original list. -/
theorem projCubes_push (l : List (Σ n : ℕ+, (⋁w).cells (n : ℕ)))
    (hall : ∀ c ∈ l, (P.proj c.1 c.1.pos c.2).isSome) :
    (projCubes P l).map (fun c => (⟨c.1, P.incl⟪(c.1 : ℕ)⟫ c.2⟩ :
        Σ n : ℕ+, (⋁w).cells (n : ℕ))) = l := by
  induction l with
  | nil => rfl
  | cons c rest ih =>
    rw [projCubes, List.filterMap_cons]
    rcases hc : P.proj c.1 c.1.pos c.2 with _ | r
    · exact absurd hc (by have := hall c (List.mem_cons_self ..); rw [hc] at this; simp at this)
    · rw [Option.map_some, List.map_cons]
      exact congrArg₂ _ (Sigma.ext rfl (heq_of_eq (P.spec _ _ _ _ hc)))
        (ih fun c' hc' => hall c' (List.mem_cons_of_mem _ hc'))

/-- Projected beads recover the source's dimension list (re-including does not move a
cube's dimension). -/
theorem projCubes_hdims (ρ : (⋁d).toPsh ⟶ (⋁w).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨d, ρ⟩, (P.proj c.1 c.1.pos c.2).isSome) :
    (projCubes P (wedgeToCubes ⟨d, ρ⟩)).map (·.1) = d := by
  refine Eq.trans ?_ (wedgeToCubes_dims d ρ)
  conv_rhs => rw [← projCubes_push P _ hall]
  rw [List.map_map]; rfl

/-- The projected beads form a chain in `⋁e` (reflection of the pushed chain along the mono). -/
theorem projCubes_isChain (ρ : (⋁d).toPsh ⟶ (⋁w).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨d, ρ⟩, (P.proj c.1 c.1.pos c.2).isSome)
    (hinit : P.incl⟪0⟫ (⋁e).init = ρ⟪0⟫ (⋁d).init)
    (hfinal : P.incl⟪0⟫ (⋁e).final = ρ⟪0⟫ (⋁d).final) :
    IsCubeChain (⋁e).init (projCubes P (wedgeToCubes ⟨d, ρ⟩)) (⋁e).final := by
  refine isCubeChain_of_map_injective P.incl P.inj _ (⋁e).init (⋁e).final ?_
  rw [projCubes_push P (wedgeToCubes ⟨d, ρ⟩) hall, hinit, hfinal]
  exact wedgeToCubes_isCubeChain d ρ

/-- If every value of `ρ` is an `incl`-image, then every bead of `ρ` projects. -/
theorem projCubes_isSome (ρ : (⋁d).toPsh ⟶ (⋁w).toPsh)
    (himg : ∀ (m : ℕ) (z : (⋁d).cells m), ∃ r, P.incl⟪m⟫ r = ρ⟪m⟫ z) :
    ∀ c ∈ wedgeToCubes ⟨d, ρ⟩, (P.proj c.1 c.1.pos c.2).isSome := by
  have hcomp := wedgeToCubes_comp ρ d (𝟙 (⋁d).toPsh)
  rw [Category.id_comp] at hcomp
  rw [hcomp]; intro c hc
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hc
  obtain ⟨r, hr⟩ := himg (q.1 : ℕ) q.2
  simp only [← hr, P.sec, Option.isSome_some]

/-- **The computable factorization.**  The unique `⋁d ⟶ ⋁e` with `projFactor ≫ P.incl = ρ`. -/
def projFactor (ρ : (⋁d).toPsh ⟶ (⋁w).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨d, ρ⟩, (P.proj c.1 c.1.pos c.2).isSome)
    (hinit : P.incl⟪0⟫ (⋁e).init = ρ⟪0⟫ (⋁d).init)
    (hfinal : P.incl⟪0⟫ (⋁e).final = ρ⟪0⟫ (⋁d).final) :
    (⋁d).toPsh ⟶ (⋁e).toPsh :=
  eqToHom (congrArg (fun l => (⋁l).toPsh) (projCubes_hdims P ρ hall).symm)
    ≫ (wedgeDescHom _ (projCubes_isChain P ρ hall hinit hfinal)).hom

theorem projFactor_comp (ρ : (⋁d).toPsh ⟶ (⋁w).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨d, ρ⟩, (P.proj c.1 c.1.pos c.2).isSome)
    (hinit : P.incl⟪0⟫ (⋁e).init = ρ⟪0⟫ (⋁d).init)
    (hfinal : P.incl⟪0⟫ (⋁e).final = ρ⟪0⟫ (⋁d).final) :
    projFactor P ρ hall hinit hfinal ≫ P.incl = ρ := by
  refine wedgeToCubes_inj d _ ρ ?_ ?_
  · simp only [projFactor, Category.assoc]
    rw [wedgeToCubes_eqToHom (projCubes_hdims P ρ hall).symm, wedgeToCubes_comp,
      wedgeToCubes_wedgeDescHom, projCubes_push P (wedgeToCubes ⟨d, ρ⟩) hall]
  · have key : (projFactor P ρ hall hinit hfinal)⟪0⟫ (⋁d).init = (⋁e).init := by
      change (wedgeDescHom _ (projCubes_isChain P ρ hall hinit hfinal)).hom⟪0⟫
          ((eqToHom (congrArg (fun l => (⋁l).toPsh) (projCubes_hdims P ρ hall).symm))⟪0⟫
            (⋁d).init) = (⋁e).init
      rw [serialWedge_eqToHom_init (projCubes_hdims P ρ hall)]
      exact wedgeDesc_init _ _ _ _
    change P.incl⟪0⟫ ((projFactor P ρ hall hinit hfinal)⟪0⟫ (⋁d).init) = ρ⟪0⟫ (⋁d).init
    rw [key]; exact hinit

end Factor

/-! ### The two block projections of an append -/

variable {a' b' : List ℕ+}

/-- The `da`-block of `⋁(da ++ db)`, as a block projection. -/
def leftBlock (da db : List ℕ+) : BlockProj (da ++ db) da where
  incl := wedgeInclL da db
  proj := appendProjL da db
  spec := appendProjL_spec da db
  sec := appendProjL_wedgeInclL da db
  inj := fun n => wedgeInclL_app_injective da db (op ▫n)

/-- The `db`-block of `⋁(da ++ db)`, as a block projection. -/
def rightBlock (da db : List ℕ+) : BlockProj (da ++ db) db where
  incl := wedgeInclR da db
  proj := appendProjR da db
  spec := appendProjR_spec da db
  sec := appendProjR_wedgeInclR da db
  inj := fun n => wedgeInclR_app_injective da db (op ▫n)

/-- **Computable factorization through `wedgeInclL`.**  For `ρ` whose beads land in the
`a'`-block, the unique `⋁da ⟶ ⋁a'` with `leftFactor ≫ wedgeInclL = ρ`. -/
def leftFactor {da : List ℕ+} (ρ : (⋁da).toPsh ⟶ (⋁(a' ++ b')).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨da, ρ⟩, (appendProjL a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclL a' b')⟪0⟫ (⋁a').init = ρ⟪0⟫ (⋁da).init)
    (hfinal : (wedgeInclL a' b')⟪0⟫ (⋁a').final = ρ⟪0⟫ (⋁da).final) :
    (⋁da).toPsh ⟶ (⋁a').toPsh :=
  projFactor (leftBlock a' b') ρ hall hinit hfinal

theorem leftFactor_comp {da : List ℕ+} (ρ : (⋁da).toPsh ⟶ (⋁(a' ++ b')).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨da, ρ⟩, (appendProjL a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclL a' b')⟪0⟫ (⋁a').init = ρ⟪0⟫ (⋁da).init)
    (hfinal : (wedgeInclL a' b')⟪0⟫ (⋁a').final = ρ⟪0⟫ (⋁da).final) :
    leftFactor ρ hall hinit hfinal ≫ wedgeInclL a' b' = ρ :=
  projFactor_comp (leftBlock a' b') ρ hall hinit hfinal

/-- Computable factorization through `wedgeInclR`. -/
def rightFactor {dc : List ℕ+} (σ : (⋁dc).toPsh ⟶ (⋁(a' ++ b')).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨dc, σ⟩, (appendProjR a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclR a' b')⟪0⟫ (⋁b').init = σ⟪0⟫ (⋁dc).init)
    (hfinal : (wedgeInclR a' b')⟪0⟫ (⋁b').final = σ⟪0⟫ (⋁dc).final) :
    (⋁dc).toPsh ⟶ (⋁b').toPsh :=
  projFactor (rightBlock a' b') σ hall hinit hfinal

theorem rightFactor_comp {dc : List ℕ+} (σ : (⋁dc).toPsh ⟶ (⋁(a' ++ b')).toPsh)
    (hall : ∀ c ∈ wedgeToCubes ⟨dc, σ⟩, (appendProjR a' b' c.1 c.1.pos c.2).isSome)
    (hinit : (wedgeInclR a' b')⟪0⟫ (⋁b').init = σ⟪0⟫ (⋁dc).init)
    (hfinal : (wedgeInclR a' b')⟪0⟫ (⋁b').final = σ⟪0⟫ (⋁dc).final) :
    rightFactor σ hall hinit hfinal ≫ wedgeInclR a' b' = σ :=
  projFactor_comp (rightBlock a' b') σ hall hinit hfinal

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
      ∃ w, (wedgeInclL a'.dims b'.dims)⟪m⟫ w = ρL⟪m⟫ z := fun m hm z =>
    wedgeInclL_of_concat_inl X Y a' b' hm (comp_app_cell₂ hcompL m z)
  have hposR : ∀ (m : ℕ), 1 ≤ m → ∀ (z : (⋁b.dims).cells m),
      ∃ w, (wedgeInclR a'.dims b'.dims)⟪m⟫ w = ρR⟪m⟫ z := fun m hm z =>
    wedgeInclR_of_concat_inr X Y a' b' hm (comp_app_cell₂ hcompR m z)
  have hρLinit : ρL⟪0⟫ (⋁a.dims).init = (⋁(a'.dims ++ b'.dims)).init := by
    rw [hρL, NatTrans.comp_app, types_comp_apply,
      app_init_eq_of_initVertex (wedgeInclL a.dims b.dims) (wedgeInclL_initVertex a.dims b.dims)]
    exact hh2.φ.app_init
  have hρRfinal : ρR⟪0⟫ (⋁b.dims).final = (⋁(a'.dims ++ b'.dims)).final := by
    rw [hρR, NatTrans.comp_app, types_comp_apply,
      app_final_eq_of_finalVertex (wedgeInclR a.dims b.dims) (wedgeInclR_finalVertex a.dims b.dims)]
    exact hh2.φ.app_final
  -- Endpoints for `leftFactor`/`rightFactor`, derived up-front (via `himg` + `append_inter`).
  have hinit_L : (wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).init = ρL⟪0⟫ (⋁a.dims).init := by
    rw [app_init_eq_of_initVertex (wedgeInclL a'.dims b'.dims)
      (wedgeInclL_initVertex a'.dims b'.dims)]; exact hρLinit.symm
  have hfinal_R : (wedgeInclR a'.dims b'.dims)⟪0⟫ (⋁b'.dims).final = ρR⟪0⟫ (⋁b.dims).final := by
    rw [app_final_eq_of_finalVertex (wedgeInclR a'.dims b'.dims)
      (wedgeInclR_finalVertex a'.dims b'.dims)]; exact hρRfinal.symm
  have himgL := himg_reduce a.dims ρL (wedgeInclL a'.dims b'.dims) hposL
    (fun hda => himg_of_nil _ _ hda _ _ hinit_L)
  have himgR := himg_reduce b.dims ρR (wedgeInclR a'.dims b'.dims) hposR
    (fun hdb => himg_of_nil _ _ hdb _ _ hfinal_R)
  have hjeq : ρL⟪0⟫ (⋁a.dims).final = ρR⟪0⟫ (⋁b.dims).init := by
    rw [hρL, hρR]; simp only [NatTrans.comp_app, types_comp_apply]
    rw [wedgeInclL_final_eq_wedgeInclR_init a.dims b.dims]
  -- The junction: both halves hit it, and `append_inter` pins each side's endpoint at once.
  have hjunc : (wedgeInclL a'.dims b'.dims)⟪0⟫ (⋁a'.dims).final = ρL⟪0⟫ (⋁a.dims).final
      ∧ (wedgeInclR a'.dims b'.dims)⟪0⟫ (⋁b'.dims).init = ρR⟪0⟫ (⋁b.dims).init := by
    obtain ⟨wL, hwL⟩ := himgL 0 (⋁a.dims).final
    obtain ⟨wR, hwR⟩ := himgR 0 (⋁b.dims).init
    obtain ⟨hwLeq, hwReq⟩ := append_inter a'.dims b'.dims wL wR (by rw [hwL, hwR, hjeq])
    exact ⟨by rw [← hwLeq, hwL], by rw [← hwReq, hwR]⟩
  have hfinal_L := hjunc.1
  have hinit_R := hjunc.2
  have hall_L : ∀ c ∈ wedgeToCubes ⟨a.dims, ρL⟩,
      (appendProjL a'.dims b'.dims c.1 c.1.pos c.2).isSome :=
    projCubes_isSome (leftBlock a'.dims b'.dims) ρL himgL
  have hall_R : ∀ c ∈ wedgeToCubes ⟨b.dims, ρR⟩,
      (appendProjR a'.dims b'.dims c.1 c.1.pos c.2).isSome :=
    projCubes_isSome (rightBlock a'.dims b'.dims) ρR himgR
  set fhom := leftFactor ρL hall_L hinit_L hfinal_L with hfhom
  set ghom := rightFactor ρR hall_R hinit_R hfinal_R with hghom
  have hfhom_comp : fhom ≫ wedgeInclL a'.dims b'.dims = ρL :=
    leftFactor_comp ρL hall_L hinit_L hfinal_L
  have hghom_comp : ghom ≫ wedgeInclR a'.dims b'.dims = ρR :=
    rightFactor_comp ρR hall_R hinit_R hfinal_R
  have hfval := comp_app_cell hfhom_comp 0
  have hgval := comp_app_cell hghom_comp 0
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



