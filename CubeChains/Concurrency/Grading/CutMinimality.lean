import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Machinery.Presentation.Localize
import CubeChains.Machinery.Skeletal

/-!
# Concurrency/Grading/CutMinimality — every presentation carries every codimension-one arrow

A codimension-one arrow of a graded category whose codimension-zero arrows are invertible is
indecomposable: the letters of a word spelling it have codimensions summing to one, so every other
letter is invertible.  Hence *every* presentation of `(Ch K)ᵒᵖ` has a 1-cell for each
codimension-one refinement, and names every chain on the nose — `Ch K` has no non-trivial
isomorphism.

At three events that generating set is forced to contain a crossing of length two and forced to
repeat a crossing, and it never contains the reversal: neither Artin's atoms nor Garside's simples.
-/

universe w u' w₂ v u

open CategoryTheory CubeChains BPSet Opposite Equiv

namespace CategoryTheory.Presents

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (G : Grading C) (hrig : ∀ {a b : C} (f : a ⟶ b), G.codim f = 0 → IsIso f)

include hrig in
/-- **A word of codimension one has a letter that spells it** — the other letters have codimension
zero, hence are invertible. -/
theorem exists_cell_of_eval_codim_eq_one :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y), G.codim (p.eval.map u) = 1 →
      ∃ (x' y' : GenObj P.Gen) (e : x' ⟶ y') (s : p.at' x ≅ p.at' x') (t : p.at' y' ≅ p.at' y),
        p.eval.map u = s.hom ≫ p.arrow e ≫ t.hom := by
  intro x y u
  induction u with
  | nil =>
      intro h
      rw [p.eval_nil, G.codim_id] at h
      exact absurd h (by omega)
  | cons u e ih =>
      intro h
      rw [p.eval_cons, G.codim_comp] at h
      rcases Nat.eq_zero_or_pos (G.codim (p.arrow e)) with he | he
      · haveI := hrig _ he
        obtain ⟨x', y', e', s, t, hu⟩ := ih (by omega)
        refine ⟨x', y', e', s, t ≪≫ asIso (p.arrow e), ?_⟩
        rw [p.eval_cons, hu, Iso.trans_hom, asIso_hom]
        simp only [Category.assoc]
      · haveI := hrig (p.eval.map u) (by omega)
        exact ⟨_, _, e, asIso (p.eval.map u), Iso.refl _,
          by rw [p.eval_cons, Iso.refl_hom, Category.comp_id, asIso_hom]⟩

include hrig in
/-- **Every codimension-one arrow is the arrow of a single 1-cell**, up to an isomorphism at each
end: a lower bound on *every* presentation, not only on a cut-like one. -/
theorem exists_cell_of_codim_eq_one {a b : C} (f : a ⟶ b) (hf : G.codim f = 1) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (u : a ≅ p.at' x) (v : p.at' y ≅ b),
      f = u.hom ≫ p.arrow e ≫ v.hom := by
  obtain ⟨⟨wa⟩, ⟨α₀⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) a
  obtain ⟨⟨wb⟩, ⟨β₀⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) b
  -- both isomorphisms spelled at `p.at'`, so that no composite below changes spelling
  have α : p.at' wa ≅ a := α₀
  have β : p.at' wb ≅ b := β₀
  obtain ⟨u, hu⟩ : ∃ u : wa ⟶ wb, p.eval.map u = α.hom ≫ f ≫ β.inv := p.eval.map_surjective _
  have hcod : G.codim (p.eval.map u) = 1 := by
    rw [hu, G.codim_comp α.hom (f ≫ β.inv), G.codim_comp f β.inv,
      G.codim_eq_zero_of_isIso α.hom, G.codim_eq_zero_of_isIso β.inv, hf]
  obtain ⟨x', y', e, s, t, hfac⟩ := p.exists_cell_of_eval_codim_eq_one G hrig u hcod
  have key : α.inv ≫ (s.hom ≫ p.arrow e ≫ t.hom) ≫ β.hom = f := by
    rw [hfac.symm.trans hu]; simp
  exact ⟨x', y', e, α.symm ≪≫ s, t ≪≫ β,
    by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using key.symm⟩

end CategoryTheory.Presents

namespace ChainCat

/-! ## `Ch K` is rigid at codimension zero

A codimension-zero refinement is an identity (`codim_eq_zero_iff`, `endo_eq_id`), so the only
isomorphisms are identities — which is what lets a presentation's 0-cells name chains on the nose,
rather than up to isomorphism. -/

/-- A codimension-zero refinement is invertible, being an identity. -/
theorem isIso_of_codim_eq_zero {K : BPSet} {a b : Ch K} (f : a ⟶ b) (h : codim f = 0) :
    IsIso f := by
  obtain rfl := (codim_eq_zero_iff f).mp h
  rw [endo_eq_id f]
  infer_instance

theorem isIso_op_of_codim_eq_zero {K : BPSet} {A B : (Ch K)ᵒᵖ} (f : A ⟶ B)
    (h : ((grading K).op).codim f = 0) : IsIso f :=
  haveI := isIso_of_codim_eq_zero f.unop h
  ⟨(inv f.unop).op, Quiver.Hom.unop_inj (IsIso.inv_hom_id f.unop),
    Quiver.Hom.unop_inj (IsIso.hom_inv_id f.unop)⟩

/-- **An isomorphism of chains is an identity**, transport and all. -/
theorem iso_hom_eq_eqToHom {K : BPSet} {a b : Ch K} (u : a ≅ b) :
    ∃ h : a = b, u.hom = eqToHom h := by
  obtain rfl := eq_of_isIso u.hom
  exact ⟨rfl, by rw [endo_eq_id u.hom, eqToHom_refl]⟩

/-! ## Crossings ignore a transport -/

@[simp] theorem crossPerm_eqToHom_comp {K : BPSet} {a a' b : Ch K} (ha : a = a') (f : a' ⟶ b)
    {N : ℕ} (h : dimSum a.dims = N) (h' : dimSum a'.dims = N) :
    crossPerm h (eqToHom ha ≫ f) = crossPerm h' f := by
  subst ha; rw [eqToHom_refl, Category.id_comp]

@[simp] theorem crossPerm_comp_eqToHom {K : BPSet} {a b b' : Ch K} (hb : b = b') (f : a ⟶ b)
    {N : ℕ} (h : dimSum a.dims = N) : crossPerm h (f ≫ eqToHom hb) = crossPerm h f := by
  subst hb; rw [eqToHom_refl, Category.comp_id]

/-! ## Inside a bead nothing crosses

`coordMap_pos_lt_of_fst_eq` in strand coordinates: a pair of events in one bead of the source keeps
its order, so only a run can reverse all of its strands. -/

/-- **`crossPerm` is increasing inside a bead of the source.** -/
theorem crossPerm_lt_of_fst_eq {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    {e e' : beadEvent a.dims} (hb : e.1 = e'.1) (hlt : pos e < pos e') :
    crossPerm h f (strand a.dims h e) < crossPerm h f (strand a.dims h e') := by
  rw [crossPerm_strand, crossPerm_strand, Fin.lt_def, strand_val, strand_val]
  exact coordMap_pos_lt_of_fst_eq f.φ hb hlt

/-- **A chain coarser than a run cannot reverse its strands**: two events of one bead keep their
order, and the reversal keeps none. -/
theorem crossPerm_ne_revPerm {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N) (f : a ⟶ b)
    (ha : degree a ≠ 0) : crossPerm h f ≠ Fin.revPerm := by
  intro hrev
  obtain ⟨d, hd, hd1⟩ : ∃ d ∈ a.dims, d ≠ 1 := by
    by_contra hc
    exact ha ((degree_eq_zero_iff a).mpr (by simpa using hc))
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hd
  have h2 : 1 < (a.dims.get i : ℕ) := by
    rw [hi]
    obtain ⟨_ | _ | k, hk⟩ := d
    · exact absurd hk (by omega)
    · exact absurd rfl hd1
    · exact Nat.succ_lt_succ (Nat.succ_pos k)
  set e : beadEvent a.dims := ⟨i, ⟨0, by omega⟩⟩
  set e' : beadEvent a.dims := ⟨i, ⟨1, h2⟩⟩
  have hlt : pos e < pos e' := pos_lt_iff_of_fst_eq.mpr (by simp [Fin.lt_def])
  have hcross := crossPerm_lt_of_fst_eq h f (e := e) (e' := e') rfl hlt
  rw [hrev] at hcross
  have hs : strand a.dims h e < strand a.dims h e' := by
    rw [Fin.lt_def, strand_val, strand_val]
    exact hlt
  exact absurd (Fin.rev_lt_rev.mp hcross) (asymm hs)

/-- **A chain coarser than a run crosses less than the reversal.** -/
theorem permLen_crossPerm_lt_revPerm {K : BPSet} {a b : Ch K} {N : ℕ} (h : dimSum a.dims = N)
    (f : a ⟶ b) (ha : degree a ≠ 0) :
    permLen (crossPerm h f) < permLen (Fin.revPerm : Perm (Fin N)) := by
  have hadd := permLen_add_inv_mul_revPerm (crossPerm h f)
  have hpos : 0 < permLen ((crossPerm h f)⁻¹ * Fin.revPerm) := by
    rcases Nat.eq_zero_or_pos (permLen ((crossPerm h f)⁻¹ * Fin.revPerm)) with h0 | h0
    · exact absurd (inv_mul_eq_one.mp (eq_one_of_permLen_eq_zero _ h0))
        (crossPerm_ne_revPerm h f ha)
    · exact h0
  omega

/-- **The capacity of a degree-zero codimension-one refinement is one** — one bead of size two. -/
theorem crossCap_of_codim_eq_one {K : BPSet} {a b : Ch K} (f : a ⟶ b) (ha : degree a = 0)
    (hf : codim f = 1) : crossCap b.dims = 1 := by
  have hone : ∀ z ∈ a.dims, z = 1 := (degree_eq_zero_iff a).mp ha
  obtain ⟨l, r, p, q, hb, ha'⟩ := (codim_eq_one_iff f).mp hf
  obtain rfl : p = 1 := hone p (by rw [ha']; simp)
  obtain rfl : q = 1 := hone q (by rw [ha']; simp)
  have hl : crossCap l = 0 := crossCap_eq_zero_of_ones fun z hz => hone z (by rw [ha']; simp [hz])
  have hr : crossCap r = 0 := crossCap_eq_zero_of_ones fun z hz => hone z (by rw [ha']; simp [hz])
  rw [hb, crossCap_append, crossCap_cons, hl, hr]
  decide

/-! ## Three events

At three events the degree-one shape is `[2,1]`, whose single junction `2` forces exactly one pair
of strands to rise.  Everything this section exhibits is a refinement of it onto one bead. -/

theorem permLen_revPerm_three : permLen (Fin.revPerm : Perm (Fin 3)) = 3 := by decide

/-- The strand count of the degree-one shape, spelled once so every `crossPerm` reads at it. -/
theorem pairOneDim : dimSum [(2 : ℕ+), 1] = 3 := rfl

/-- **The degree-one hom-set at three events.**  A refinement of `[2,1]` onto one bead realises
every permutation rising across its wide bead — and the junction `2` is the only constraint, so
`τ 0 < τ 1` is the whole hypothesis. -/
theorem exists_crossPerm_pairOne {τ : Perm (Fin 3)} (hτ : τ 0 < τ 1) :
    ∃ f : zObj [(2 : ℕ+), 1] ⟶ zObj [(3 : ℕ+)], crossPerm pairOneDim f = τ := by
  refine exists_crossPerm_single (a := [(2 : ℕ+), 1]) pairOneDim (m := 3) rfl fun x y hxy hlt => ?_
  have hb := (beadAt_eq_iff _ (x : ℕ) (y : ℕ)).mp
    ((index_eq_iff_beadAt pairOneDim x y).mp (congrArg Fin.val hxy)) 2
    (mem_boundaries_iff.mpr ⟨[2], [1], rfl, rfl⟩)
  rw [Fin.lt_def] at hlt
  have hx := x.isLt
  have hy := y.isLt
  have hv : (x : ℕ) = 0 ∧ (y : ℕ) = 1 := by
    by_cases h : (2 : ℕ) ≤ (y : ℕ)
    · exact absurd (hb.mpr h) (by omega)
    · omega
  obtain rfl : x = 0 := Fin.ext (by simpa using hv.1)
  obtain rfl : y = 1 := Fin.ext (by simpa using hv.2)
  exact hτ

/-- **A codimension-one refinement out of a non-run can cross twice** — the 3-cycle, which is
neither a merge nor an atom, performed from a shape of degree one. -/
theorem exists_codim_eq_one_permLen_eq_two :
    ∃ (x y : Ch Zbp) (f : x ⟶ y) (h : dimSum x.dims = 3),
      codim f = 1 ∧ degree x = 1 ∧ permLen (crossPerm h f) = 2 := by
  obtain ⟨f, hf⟩ := exists_crossPerm_pairOne (τ := adjT 0 * adjT 1) (by decide)
  refine ⟨_, _, f, pairOneDim, ?_, ?_, ?_⟩
  · exact show degree (zObj [(3 : ℕ+)]) - degree (zObj [(2 : ℕ+), 1]) = 1 by decide
  · exact show degree (zObj [(2 : ℕ+), 1]) = 1 by decide
  · rw [hf]; decide

/-- On three strands a crossing of length two has order three. -/
theorem threeCycle_of_permLen_eq_two :
    ∀ σ : Perm (Fin 3), permLen σ = 2 → σ ≠ 1 ∧ σ * σ * σ = 1 := by decide

/-- **The forced non-atom is a 3-cycle** — neither the identity, nor an atom, nor the reversal. -/
theorem exists_codim_eq_one_threeCycle :
    ∃ (x y : Ch Zbp) (f : x ⟶ y) (h : dimSum x.dims = 3), codim f = 1 ∧ degree x = 1 ∧
      crossPerm h f ≠ 1 ∧ crossPerm h f * crossPerm h f * crossPerm h f = 1 := by
  obtain ⟨x, y, f, h, hf, hdeg, hlen⟩ := exists_codim_eq_one_permLen_eq_two
  obtain ⟨h1, h3⟩ := threeCycle_of_permLen_eq_two _ hlen
  exact ⟨x, y, f, h, hf, hdeg, h1, h3⟩

/-- **A codimension-one refinement of three events crosses at most twice**: out of a run the
capacity is one, and out of a coarser shape the reversal is unreachable. -/
theorem permLen_crossPerm_le_two_of_codim_eq_one {a b : Ch Zbp} (f : a ⟶ b)
    (h : dimSum a.dims = 3) (hf : codim f = 1) : permLen (crossPerm h f) ≤ 2 := by
  rcases Nat.eq_zero_or_pos (degree a) with ha | ha
  · have hle := permLen_crossPerm_le_crossCap b.dims f rfl h
    rw [crossCap_of_codim_eq_one f ha hf] at hle
    omega
  · have hlt := permLen_crossPerm_lt_revPerm h f (by omega)
    rw [permLen_revPerm_three] at hlt
    omega

/-- **The longest simple is not a cut**: `w₀` crosses three times, and no single cut does. -/
theorem crossPerm_ne_revPerm_of_codim_eq_one {a b : Ch Zbp} (f : a ⟶ b) (h : dimSum a.dims = 3)
    (hf : codim f = 1) : crossPerm h f ≠ Fin.revPerm := by
  intro hc
  have := permLen_crossPerm_le_two_of_codim_eq_one f h hf
  rw [hc, permLen_revPerm_three] at this
  omega

/-- **The crossing does not separate the cuts**: the atom `adjT 1` is performed both out of the run
and out of the degree-one shape `[2,1]`, whose own junction it does not cross — so a generating set
cannot carry one 1-cell per crossing. -/
theorem exists_codim_eq_one_crossPerm_eq :
    ∃ (x y x' y' : Ch Zbp) (f : x ⟶ y) (f' : x' ⟶ y') (h : dimSum x.dims = 3)
      (h' : dimSum x'.dims = 3), codim f = 1 ∧ codim f' = 1 ∧ x ≠ x' ∧
        crossPerm h f ≠ 1 ∧ crossPerm h f = crossPerm h' f' := by
  obtain ⟨f, hf⟩ := exists_crossPerm_pairOne (τ := adjT 1) (by decide)
  refine ⟨_, _, zObj (𝟙^3), zObj (atomComp 3 1), f, atomOnes 3 1, pairOneDim,
    dimSum_replicate 3, show degree (zObj [(3 : ℕ+)]) - degree (zObj [(2 : ℕ+), 1]) = 1 by decide,
    codim_atomOnes 3 1, ?_, ?_, ?_⟩
  · exact fun hc => absurd (congrArg (fun z : Ch Zbp => z.dims.length) hc) (by decide)
  · rw [hf]; exact adjT_ne_one (n := 3) 1
  · rw [hf, crossPerm_atomOnes]

/-! ## What a presentation of `(Ch K)ᵒᵖ` must carry -/

variable {P : Polygraph.{w, u', w₂}} {K : BPSet}

/-- **A presentation of `(Ch K)ᵒᵖ` names every chain on the nose** — the only isomorphisms are
identities, so essential surjectivity is surjectivity. -/
theorem exists_at'_eq (p : Presents P ((Ch K)ᵒᵖ)) (A : (Ch K)ᵒᵖ) : ∃ x, p.at' x = A := by
  obtain ⟨⟨w⟩, ⟨α⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) A
  exact ⟨w, (ChainCat.skeletal K).op ⟨α⟩⟩

/-- **Every presentation of `(Ch K)ᵒᵖ` has a 1-cell for each codimension-one refinement** — the cut
presentation is minimal. -/
theorem exists_cell_codim_eq_one (p : Presents P ((Ch K)ᵒᵖ)) {a b : Ch K} (f : a ⟶ b)
    (hf : codim f = 1) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (u : op b ≅ p.at' x) (v : p.at' y ≅ op a),
      f.op = u.hom ≫ p.arrow e ≫ v.hom :=
  p.exists_cell_of_codim_eq_one ((grading K).op)
    (fun g hg => isIso_op_of_codim_eq_zero g hg) f.op hf

/-- **…and its 0-cells name the two ends on the nose**, so only that transport stands between the
1-cell's arrow and the refinement. -/
theorem exists_cell_eq_of_codim_eq_one (p : Presents P ((Ch K)ᵒᵖ)) {a b : Ch K} (f : a ⟶ b)
    (hf : codim f = 1) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (ha : a = (p.at' y).unop) (hb : (p.at' x).unop = b),
      f = eqToHom ha ≫ (p.arrow e).unop ≫ eqToHom hb := by
  obtain ⟨x, y, e, u, v, hfac⟩ := exists_cell_codim_eq_one p f hf
  obtain ⟨ha, hva⟩ := iso_hom_eq_eqToHom v.unop
  obtain ⟨hb, hub⟩ := iso_hom_eq_eqToHom u.unop
  refine ⟨x, y, e, ha, hb, ?_⟩
  have := congrArg Quiver.Hom.unop hfac
  rw [unop_comp, unop_comp, Category.assoc] at this
  rw [← hva, ← hub]
  exact this

/-- **…and it performs the refinement's crossing**, read at the 0-cell naming the source. -/
theorem exists_cell_crossPerm_eq (p : Presents P ((Ch K)ᵒᵖ)) {a b : Ch K} (f : a ⟶ b)
    (hf : codim f = 1) {N : ℕ} (h : dimSum a.dims = N) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (h' : dimSum ((p.at' y).unop).dims = N),
      (p.at' y).unop = a ∧ crossPerm h' (p.arrow e).unop = crossPerm h f := by
  obtain ⟨x, y, e, ha, hb, hf'⟩ := exists_cell_eq_of_codim_eq_one p f hf
  refine ⟨x, y, e, ha ▸ h, ha.symm, ?_⟩
  rw [hf', crossPerm_eqToHom_comp ha _ h (ha ▸ h), crossPerm_comp_eqToHom]

/-! ## Neither Artin's atoms nor Garside's simples

The forced 1-cells at three events contain a crossing of length two (so the generating set is not
Artin's) and contain two cells of one crossing (so it is not Garside's, one cell per simple), while
no codimension-one refinement crosses three times — `w₀` is not among them at all. -/

/-- **A generator out of a non-run, crossing twice, is forced**: neither an atom nor a simple out of
the run, both of which leave a run. -/
theorem exists_cell_permLen_eq_two (p : Presents P ((Ch Zbp)ᵒᵖ)) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (h : dimSum ((p.at' y).unop).dims = 3),
      degree ((p.at' y).unop) = 1 ∧ permLen (crossPerm h (p.arrow e).unop) = 2 := by
  obtain ⟨c, d, f, hd, hc, hdeg, hlen⟩ := exists_codim_eq_one_permLen_eq_two
  obtain ⟨x, y, e, h', hy, hcross⟩ := exists_cell_crossPerm_eq p f hc hd
  exact ⟨x, y, e, h', by rw [hy, hdeg], by rw [hcross, hlen]⟩

/-- …so the 1-cells are never all atoms. -/
theorem not_forall_cell_permLen_le_one (p : Presents P ((Ch Zbp)ᵒᵖ)) :
    ¬ ∀ (x y : GenObj P.Gen) (e : x ⟶ y) (h : dimSum ((p.at' y).unop).dims = 3),
        permLen (crossPerm h (p.arrow e).unop) ≤ 1 := by
  obtain ⟨x, y, e, h, -, hlen⟩ := exists_cell_permLen_eq_two p
  intro hall
  have := hall x y e h
  omega

/-- **Two 1-cells of one crossing are forced**: the 0-cells differ, so no relabelling merges them,
and a generating set with one cell per simple is out of reach. -/
theorem exists_two_cells_crossPerm_eq (p : Presents P ((Ch Zbp)ᵒᵖ)) :
    ∃ (x y x' y' : GenObj P.Gen) (e : x ⟶ y) (e' : x' ⟶ y')
      (h : dimSum ((p.at' y).unop).dims = 3) (h' : dimSum ((p.at' y').unop).dims = 3),
      p.at' y ≠ p.at' y' ∧ crossPerm h (p.arrow e).unop ≠ 1 ∧
        crossPerm h (p.arrow e).unop = crossPerm h' (p.arrow e').unop := by
  obtain ⟨c, d, c', d', f, f', hd, hd', hc, hc', hne, hone, heq⟩ :=
    exists_codim_eq_one_crossPerm_eq
  obtain ⟨x, y, e, h, hy, hcross⟩ := exists_cell_crossPerm_eq p f hc hd
  obtain ⟨x', y', e', h', hy', hcross'⟩ := exists_cell_crossPerm_eq p f' hc' hd'
  refine ⟨x, y, x', y', e, e', h, h', ?_, by rw [hcross]; exact hone, by rw [hcross, hcross', heq]⟩
  intro hyy
  exact hne (hy.symm.trans (by rw [hyy]; exact hy'))

end ChainCat
