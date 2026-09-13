import CubeChains.Concurrency.Merge.CubeThin
import CubeChains.Machinery.Rewriting.Diamond

/-!
# Testing/DiamondCube — the localized cube slice read as a step diagram

`Relation.StepDiagram.isThin_of_hasDiamonds` at `Ch (□n)[W⁻¹]`: the vertices are the weak-order
classes, a step is one adjacent descent, and the arrow a step carries is the atom fraction out of
the class's run — `conjRun_map_eq` is why the face chosen does not matter.  `cubeStep_hasDiamonds`
is the cube's own diamond, and thinness follows with no word induction and no spanning theorem.

Not built by `lake build CubeChains`.
-/

open CategoryTheory BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-- The atom arrow a descent names, and its independence of the face chosen. -/
private theorem exists_atomArrow {σ τ : Equiv.Perm (Fin n)} (h : WeakOrder.DescentStep σ τ) :
    ∃ g : (W (□n)).Q.obj (wordRun σ).chain ⟶ (W (□n)).Q.obj (wordRun τ).chain,
      ∀ {d : Ch (□n)} (u : (wordRun σ).chain ⟶ d) (hd : cross d = τ),
        g = conjRun (cross_wordRun σ) hd ((W (□n)).Q.map u) := by
  obtain ⟨i, hdi, rfl⟩ := h
  obtain ⟨dc, uc, hdc, -⟩ := exists_atom_face (wordRun σ).ones (by rw [cross_wordRun]; exact hdi)
  rw [cross_wordRun] at hdc
  exact ⟨conjRun (cross_wordRun σ) hdc ((W (□n)).Q.map uc), fun u hd => conjRun_map_eq uc u hdc hd⟩

/-- **The cube's step diagram**: a weak-order class, its run's localized object, and the atom
fractions.  `conjRun_map_eq` is why a step carries one arrow and not a choice of face. -/
noncomputable def cubeStep (n : ℕ) :
    Relation.StepDiagram (Equiv.Perm (Fin n)) ((W (□n)).Localization) where
  obj σ := (W (□n)).Q.obj (wordRun σ).chain
  Step := WeakOrder.DescentStep
  arr h := (exists_atomArrow h).choose
  deg := permLen
  deg_step h := WeakOrder.permLen_lt_of_descentStep h

theorem cubeStep_arr_eq {σ τ : Equiv.Perm (Fin n)} (h : WeakOrder.DescentStep σ τ)
    {d : Ch (□n)} (u : (wordRun σ).chain ⟶ d) (hd : cross d = τ) :
    (cubeStep n).arr h = conjRun (cross_wordRun σ) hd ((W (□n)).Q.map u) :=
  (exists_atomArrow h).choose_spec u hd

/-- **Every word is a path** — the two spellings of a chain of atom steps. -/
theorem path_of_word {σ τ : Equiv.Perm (Fin n)}
    {g : (W (□n)).Q.obj (wordRun σ).chain ⟶ (W (□n)).Q.obj (wordRun τ).chain} (w : Word σ τ g) :
    ∃ P : Relation.StepDiagram.Path (cubeStep n) σ τ, P.ev = g := by
  induction w with
  | nil s => exact ⟨.nil, rfl⟩
  | @cons σ τ i d u hd h w₀ ih =>
      obtain ⟨P, hP⟩ := ih
      refine ⟨.cons (a := σ) (b := σ * adjT i) ⟨i, descent_of_word_step u hd, rfl⟩ P, ?_⟩
      rw [Relation.StepDiagram.Path.ev_cons, hP, cubeStep_arr_eq _ u hd]
      exact rfl

/-- **Conjugating a morphism already between class runs changes nothing** — the merge out of a run
into itself is the identity. -/
theorem conjRun_run_run {σ τ : Equiv.Perm (Fin n)}
    (g : (W (□n)).Q.obj (wordRun σ).chain ⟶ (W (□n)).Q.obj (wordRun τ).chain) :
    conjRun (cross_wordRun σ) (cross_wordRun τ) g = g := by
  have hid : ∀ ρ : Equiv.Perm (Fin n), (classRunIso (cross_wordRun ρ)).hom = 𝟙 _ := fun ρ => by
    rw [runIso_hom, show runHom (cross_wordRun ρ) = 𝟙 _ from Subsingleton.elim _ _]
    exact (W (□n)).Q.map_id _
  have hinv : (classRunIso (cross_wordRun τ)).inv = 𝟙 _ := by
    have h := (classRunIso (cross_wordRun τ)).hom_inv_id
    rwa [hid τ, Category.id_comp] at h
  rw [conjRun, hid σ, hinv, Category.id_comp, Category.comp_id]

/-- **The absorption clause, from the weak order** — reachability by descents *is* the order, so the
two cover lemmas of `WeakOrder` supply it with no reachability argument of their own. -/
theorem absorb_of_le {b c d : Equiv.Perm (Fin n)}
    (hord : ∀ x : WeakOrder n, x ≤ WeakOrder.of b → x ≤ WeakOrder.of c → x ≤ WeakOrder.of d)
    {e : Equiv.Perm (Fin n)} (hb : Relation.ReflTransGen WeakOrder.DescentStep b e)
    (hc : Relation.ReflTransGen WeakOrder.DescentStep c e) :
    Relation.ReflTransGen WeakOrder.DescentStep d e :=
  WeakOrder.reflTransGen_descentStep_iff_le.mpr
    (hord (WeakOrder.of e) (WeakOrder.reflTransGen_descentStep_iff_le.mp hb)
      (WeakOrder.reflTransGen_descentStep_iff_le.mp hc))

/-- **Thinness, from the diamonds alone.**  `hobj` is `classRunIso`, `hfull` is
`exists_word_of_hom`, and `Relation.StepDiagram.isThin_of_hasDiamonds` is everything else. -/
theorem isThin_of_cubeStep_hasDiamonds (hD : (cubeStep n).HasDiamonds) :
    Quiver.IsThin ((W (□n)).Localization) :=
  Relation.StepDiagram.isThin_of_hasDiamonds hD
    (fun X => by
      obtain ⟨c, rfl⟩ := Localization.Construction.exists_Q_obj (W (□n)) X
      exact ⟨cross c, ⟨classRunIso (rfl : cross c = cross c)⟩⟩)
    (fun a b f => path_of_word (conjRun_run_run f ▸
      exists_word_of_hom (cross_wordRun a) (cross_wordRun b) f))

/-! ## The diamond -/

/-- The crossing permutation of a refinement of a run, read off where it lands. -/
private theorem crossPerm_run {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {d : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (hd : cross d = σ * adjT i) :
    crossPerm (dimSum_dims_cube (wordRun σ).chain) u = adjT i := by
  have h := cross_eq_mul u
  rw [cross_wordRun, hd] at h
  have h2 := congrArg (fun x : Equiv.Perm (Fin n) => (σ * adjT i)⁻¹ * x) h
  simp only [inv_mul_cancel_left] at h2
  rw [← h2, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
    show ((adjT i)⁻¹ : Equiv.Perm (Fin n)) = adjT i from by rw [adjT, Equiv.swap_inv]]

/-- The canonical atom face of a descent, with its arrow and its codimension. -/
private theorem exists_atom_codim' {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (hdi : σ (adjHi i) < σ (adjLo i)) :
    ∃ (dc : Ch (□n)) (uc : (wordRun σ).chain ⟶ dc), cross dc = σ * adjT i ∧ codim uc = 1 := by
  obtain ⟨dc, uc, hdc, hdim⟩ :=
    exists_atom_face (wordRun σ).ones (by rw [cross_wordRun]; exact hdi)
  rw [cross_wordRun] at hdc
  refine ⟨dc, uc, hdc, ?_⟩
  have h0 : degree (wordRun σ).chain = 0 := (degree_eq_zero_iff _).mpr (wordRun σ).ones
  have h1 : degree dc = 1 := by
    rw [degree, hdim]
    have := degree_atomComp n i
    rwa [degree, zObj_dims] at this
  rw [codim, h0, h1]

/-- The diamond with the two cuts in order — the two cases the meet's `cross` splits into. -/
private theorem cubeStep_diamond_lt {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)}
    (hdi : σ (adjHi i) < σ (adjLo i)) (hdj : σ (adjHi j) < σ (adjLo j))
    (hij : (i : ℕ) < (j : ℕ))
    (hb : WeakOrder.DescentStep σ (σ * adjT i)) (hc : WeakOrder.DescentStep σ (σ * adjT j)) :
    ∃ (d : Equiv.Perm (Fin n)) (P : Relation.StepDiagram.Path (cubeStep n) (σ * adjT i) d)
      (Q : Relation.StepDiagram.Path (cubeStep n) (σ * adjT j) d),
      (cubeStep n).arr hb ≫ P.ev = (cubeStep n).arr hc ≫ Q.ev ∧
      ∀ ⦃e : Equiv.Perm (Fin n)⦄,
        Relation.ReflTransGen WeakOrder.DescentStep (σ * adjT i) e →
        Relation.ReflTransGen WeakOrder.DescentStep (σ * adjT j) e →
        Relation.ReflTransGen WeakOrder.DescentStep d e := by
  obtain ⟨dc, uc, hdc, hcu⟩ := exists_atom_codim' hdi
  obtain ⟨dc', uc', hdc', hcu'⟩ := exists_atom_codim' hdj
  have hne : dc ≠ dc' := fun hx =>
    (Nat.ne_of_lt hij)
      (adjT_inj (mul_left_cancel (show σ * adjT i = σ * adjT j by rw [← hdc, hx, hdc'])))
  obtain ⟨e, v, v', hcv, hcv'⟩ := exists_join uc uc' hcu hcu' hne
  have hlen : e.dims.length + 2 = n := length_of_two_steps (wordRun σ).ones uc v hcu hcv
  have hce : cross e = cross e := rfl
  obtain ⟨P, hP⟩ := path_of_word (word_of_step hdc hce v)
  obtain ⟨Q, hQ⟩ := path_of_word (word_of_step hdc' hce v')
  refine ⟨cross e, P, Q, ?_, ?_⟩
  · rw [cubeStep_arr_eq hb uc hdc, cubeStep_arr_eq hc uc' hdc', hP, hQ]
    refine ((conjRun_comp (cross_wordRun σ) hdc hce _ _).symm.trans ?_).trans
      (conjRun_comp (cross_wordRun σ) hdc' hce _ _)
    rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim (uc ≫ v) (uc' ≫ v')]
  · intro t h1 h2
    refine absorb_of_le (fun x k1 k2 => ?_) h1 h2
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hfar | hadj
    · rw [cross_of_meet_far (cross_wordRun σ) hfar (crossPerm_run uc hdc)
        (crossPerm_run uc' hdc') v v' hlen]
      exact WeakOrder.le_mul_adjT_mul_adjT hfar hdi hdj k1 k2
    · rw [cross_of_meet_braid (cross_wordRun σ) (by omega) (crossPerm_run uc hdc)
        (crossPerm_run uc' hdc') v v' hlen]
      exact WeakOrder.le_mul_adjT_braid (by omega) hdi hdj k1 k2

/-- **The cube's atom steps close diamonds.** -/
theorem cubeStep_hasDiamonds (n : ℕ) : (cubeStep n).HasDiamonds := by
  rintro σ b c ⟨i, hdi, rfl⟩ ⟨j, hdj, rfl⟩ hne
  have hij : (i : ℕ) ≠ (j : ℕ) := fun hx => hne (by rw [Fin.ext hx])
  rcases lt_or_gt_of_ne hij with h | h
  · exact cubeStep_diamond_lt hdi hdj h _ _
  · obtain ⟨d, P, Q, harr, habs⟩ := cubeStep_diamond_lt hdj hdi h ⟨j, hdj, rfl⟩ ⟨i, hdi, rfl⟩
    exact ⟨d, Q, P, harr.symm, fun {_} h1 h2 => habs h2 h1⟩

/-- **The localized cube slice is thin** — `Relation.StepDiagram.isThin_of_hasDiamonds` at
`cubeStep`, with no word induction of its own. -/
instance locCube_isThin' (n : ℕ) : Quiver.IsThin ((W (□n)).Localization) :=
  isThin_of_cubeStep_hasDiamonds (cubeStep_hasDiamonds n)

end ChainCat
