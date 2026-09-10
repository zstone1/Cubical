import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Machinery.Presentation.Localize

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
    (h : (grading K).op.codim f = 0) : IsIso f :=
  haveI := isIso_of_codim_eq_zero f.unop h
  ⟨(inv f.unop).op, Quiver.Hom.unop_inj (IsIso.inv_hom_id f.unop),
    Quiver.Hom.unop_inj (IsIso.hom_inv_id f.unop)⟩

/-- **An isomorphism of chains is an identity**, transport and all. -/
theorem iso_hom_eq_eqToHom {K : BPSet} {a b : Ch K} (u : a ≅ b) :
    ∃ h : a = b, u.hom = eqToHom h := by
  obtain rfl := eq_of_isIso u.hom
  exact ⟨rfl, by rw [endo_eq_id u.hom, eqToHom_refl]⟩

theorem op_eq_of_iso {K : BPSet} {A B : (Ch K)ᵒᵖ} (u : A ≅ B) : A = B :=
  unop_injective (eq_of_isIso u.unop.hom).symm

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

The reversal on one bead of three is the capacity (`crossCap_topDims_three`); its two cuts split it
as `1 + 2`, the first being bounded by the capacity of a degree-one shape and the second by the
reversal being out of reach. -/

theorem degree_zObj_top : degree (zObj (topDims 3)) = 2 := by decide

theorem permLen_revPerm_three : permLen (Fin.revPerm : Perm (Fin 3)) = 3 := by decide

theorem crossCap_topDims_three : crossCap (topDims 3) = 3 := by decide

/-- **A codimension-one refinement out of a non-run can cross twice** — the 3-cycle, which is
neither a merge nor an atom, performed from a shape of degree one. -/
theorem exists_codim_eq_one_permLen_eq_two :
    ∃ (x y : Ch Zbp) (f : x ⟶ y) (h : dimSum x.dims = 3),
      codim f = 1 ∧ degree x = 1 ∧ permLen (crossPerm h f) = 2 := by
  obtain ⟨F, hF⟩ := exists_permLen_crossPerm_eq_crossCap (topDims 3) (dimSum_topDims 3)
  have hcod : codim F = 2 := by
    have h := degree_eq_add_codim F
    rw [degree_ones, degree_zObj_top] at h
    omega
  obtain ⟨⟨m, g, k, hgk⟩, hg⟩ := (oneCutEquivBool F hcod).symm true
  have hk : codim k = 1 := by
    have h := codim_comp g k
    rw [hgk, hcod, hg] at h
    omega
  have hmid : degree m = 1 := by
    have h := degree_eq_add_codim g
    rw [degree_ones, hg] at h
    omega
  have hsum := permLen_crossPerm_comp (dimSum_replicate 3) g k
  rw [hgk, hF, crossCap_topDims_three] at hsum
  have hgle : permLen (crossPerm (dimSum_replicate 3) g) ≤ 1 := by
    have h := permLen_crossPerm_le_crossCap m.dims g rfl (dimSum_replicate 3)
    rwa [crossCap_of_codim_eq_one g (degree_ones 3) hg] at h
  have hklt := permLen_crossPerm_lt_revPerm (tgtStrands g (dimSum_replicate 3)) k (by omega)
  rw [permLen_revPerm_three] at hklt
  exact ⟨m, zObj (topDims 3), k, tgtStrands g (dimSum_replicate 3), hk, hmid, by omega⟩

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

/-- **The crossing does not separate the cuts**: two codimension-one refinements with distinct
sources perform the same non-trivial crossing. -/
theorem exists_codim_eq_one_crossPerm_eq :
    ∃ (x y x' y' : Ch Zbp) (f : x ⟶ y) (f' : x' ⟶ y') (h : dimSum x.dims = 3)
      (h' : dimSum x'.dims = 3), codim f = 1 ∧ codim f' = 1 ∧ x ≠ x' ∧
        crossPerm h f ≠ 1 ∧ crossPerm h f = crossPerm h' f' := by
  have hlen : permLen (adjT 0 * adjT 1 : Perm (Fin 3)) = 2 := by decide
  have hσ1 : (adjT 0 * adjT 1 : Perm (Fin 3)) ≠ 1 := by
    intro hc; rw [hc, permLen_one] at hlen; omega
  set F := (onesTopEquiv 3).symm (adjT 0 * adjT 1)
  have hFcross : crossPerm (dimSum_replicate 3) F = adjT 0 * adjT 1 :=
    (onesTopEquiv 3).apply_symm_apply _
  have hcod : codim F = 2 := by
    have h := degree_eq_add_codim F
    rw [degree_ones, degree_zObj_top] at h
    omega
  have hmid_deg : ∀ T : OneCut F, degree T.1.mid = 1 := by
    intro T
    have h := degree_eq_add_codim T.1.fst
    rw [degree_ones, T.2] at h
    omega
  -- one cut of the 3-cycle is an atom, or else the other cut performs the whole crossing
  have step : ∀ T : OneCut F,
      (∃ j : Fin 2, crossPerm (tgtStrands T.1.fst (dimSum_replicate 3)) T.1.snd = adjT j) ∨
        crossPerm (tgtStrands T.1.fst (dimSum_replicate 3)) T.1.snd = adjT 0 * adjT 1 := by
    intro T
    have hsum := permLen_crossPerm_comp (dimSum_replicate 3) T.1.fst T.1.snd
    rw [T.1.comp, hFcross, hlen] at hsum
    have hgle : permLen (crossPerm (dimSum_replicate 3) T.1.fst) ≤ 1 := by
      have h := permLen_crossPerm_le_crossCap T.1.mid.dims T.1.fst rfl (dimSum_replicate 3)
      rwa [crossCap_of_codim_eq_one T.1.fst (degree_ones 3) T.2] at h
    rcases Nat.eq_zero_or_pos (permLen (crossPerm (dimSum_replicate 3) T.1.fst)) with h0 | h1
    · right
      have hc := crossPerm_comp (dimSum_replicate 3) T.1.fst T.1.snd
      rw [T.1.comp, hFcross, eq_one_of_permLen_eq_zero _ h0, mul_one] at hc
      exact hc.symm
    · have h1 : permLen (crossPerm (tgtStrands T.1.fst (dimSum_replicate 3)) T.1.snd) = 1 := by
        omega
      exact Or.inl (eq_adjT_of_permLen_eq_one h1)
  have branch : ∀ (T : OneCut F) (j : Fin 2),
      crossPerm (tgtStrands T.1.fst (dimSum_replicate 3)) T.1.snd = adjT j →
      ∃ (x y x' y' : Ch Zbp) (f : x ⟶ y) (f' : x' ⟶ y') (h : dimSum x.dims = 3)
        (h' : dimSum x'.dims = 3), codim f = 1 ∧ codim f' = 1 ∧ x ≠ x' ∧
          crossPerm h f ≠ 1 ∧ crossPerm h f = crossPerm h' f' := by
    intro T j hj
    refine ⟨T.1.mid, zObj (topDims 3), zObj (𝟙^3), zObj (atomComp 3 j), T.1.snd, atomOnes 3 j,
      tgtStrands T.1.fst (dimSum_replicate 3), dimSum_replicate 3, T.codim_snd hcod,
      codim_atomOnes 3 j, ?_, ?_, ?_⟩
    · intro hmm
      have h := hmid_deg T
      rw [hmm, degree_ones] at h
      omega
    · rw [hj]; exact adjT_ne_one (n := 3) j
    · rw [hj, crossPerm_atomOnes]
  rcases step ((oneCutEquivBool F hcod).symm true) with ⟨j, hj⟩ | h0
  · exact branch _ j hj
  rcases step ((oneCutEquivBool F hcod).symm false) with ⟨j, hj⟩ | h1
  · exact branch _ j hj
  refine ⟨((oneCutEquivBool F hcod).symm true).1.mid, zObj (topDims 3),
    ((oneCutEquivBool F hcod).symm false).1.mid, zObj (topDims 3),
    ((oneCutEquivBool F hcod).symm true).1.snd, ((oneCutEquivBool F hcod).symm false).1.snd,
    tgtStrands ((oneCutEquivBool F hcod).symm true).1.fst (dimSum_replicate 3),
    tgtStrands ((oneCutEquivBool F hcod).symm false).1.fst (dimSum_replicate 3),
    ((oneCutEquivBool F hcod).symm true).codim_snd hcod,
    ((oneCutEquivBool F hcod).symm false).codim_snd hcod, ?_, ?_, ?_⟩
  · intro hm
    exact absurd ((oneCutEquivBool F hcod).symm.injective (Subtype.ext (Factorisation.ext hm)))
      (by decide)
  · rw [h0]; exact hσ1
  · rw [h0, h1]

/-! ## What a presentation of `(Ch K)ᵒᵖ` must carry -/

variable {P : Polygraph.{w, u', w₂}} {K : BPSet}

/-- **A presentation of `(Ch K)ᵒᵖ` names every chain on the nose** — the only isomorphisms are
identities, so essential surjectivity is surjectivity. -/
theorem exists_at'_eq (p : Presents P ((Ch K)ᵒᵖ)) (A : (Ch K)ᵒᵖ) : ∃ x, p.at' x = A := by
  obtain ⟨⟨w⟩, ⟨α⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) A
  exact ⟨w, op_eq_of_iso α⟩

/-- **Every presentation of `(Ch K)ᵒᵖ` has a 1-cell for each codimension-one refinement** — the cut
presentation is minimal. -/
theorem exists_cell_codim_eq_one (p : Presents P ((Ch K)ᵒᵖ)) {a b : Ch K} (f : a ⟶ b)
    (hf : codim f = 1) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (u : op b ≅ p.at' x) (v : p.at' y ≅ op a),
      f.op = u.hom ≫ p.arrow e ≫ v.hom :=
  p.exists_cell_of_codim_eq_one (grading K).op
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
