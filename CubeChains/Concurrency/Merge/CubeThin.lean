import CubeChains.Machinery.Localization.HomInduction
import CubeChains.Machinery.Rewriting.Diamond
import CubeChains.Concurrency.Merge.CubeFaces
import CubeChains.Concurrency.Merge.CubeSpanning
import Mathlib.CategoryTheory.HomCongr

/-!
# Concurrency/Merge/CubeThin — the localized cube slice is thin

`Ch (□n)[W⁻¹]` is a poset (`locCube_isThin`).  Every chain is entered from its class's run by a
merge, so a morphism is read between runs (`conjRun`): there a merge becomes the identity
(`conjRun_wInv`), and a refinement becomes the fraction its target names, which depends only on
that target's class (`conjRun_map_eq`).  That makes the weak order a `Relation.StepDiagram`
(`cubeStep`) whose steps are the adjacent descents: `exists_path_of_hom` spells every morphism in
them, `cubeStep_hasDiamonds` is the cube's own diamond, and thinness is then generic.  The join
absorbs because the order says so (`absorb_of_le`), which is why no spanning theorem enters.
-/

open CategoryTheory BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-! ## Conjugating onto the runs

Every chain is entered from its class's run by a merge, so a morphism of the localization can be
read between runs.  A refinement becomes the fraction its target names; a merge becomes the
identity, which is what lets a composite be read as a word in the atoms alone. -/

theorem nonempty_runHom (c : Ch (□n)) : Nonempty ((wordRun (cross c)).chain ⟶ c) := by
  obtain ⟨r, f, hr, hf⟩ := exists_W_run c
  have hcr : cross r = cross c := WeakOrder.of_injective (weakClass_eq_of_W hf)
  have hre : r = (wordRun (cross c)).chain :=
    run_eq_of_cross_eq hr (run_dims (wordRun (cross c))) (by rw [hcr, cross_wordRun])
  exact ⟨hre ▸ f⟩

/-- The merge from the class's run into a chain. -/
noncomputable def runHom {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    (wordRun σ).chain ⟶ c :=
  (h ▸ nonempty_runHom c).some

theorem W_runHom {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    W (□n) (runHom h) :=
  W_of_cross_eq _ (by rw [cross_wordRun, h])

/-- …and the isomorphism it becomes. -/
noncomputable def classRunIso {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    (W (□n)).Q.obj (wordRun σ).chain ≅ (W (□n)).Q.obj c :=
  Localization.Construction.wIso (runHom h) (W_runHom h)

@[simp] theorem runIso_hom {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    (classRunIso h).hom = (W (□n)).Q.map (runHom h) := rfl

/-- **Inside one class the class isos are compatible with every refinement** — the merge out of the
run is unique, so its triangle commutes. -/
theorem classRunIso_hom_comp {τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)} (h : cross c = τ)
    (h' : cross c' = τ) (k : c ⟶ c') :
    (classRunIso h).hom ≫ (W (□n)).Q.map k = (classRunIso h').hom := by
  rw [runIso_hom, runIso_hom, ← Functor.map_comp,
    show runHom h ≫ k = runHom h' from Subsingleton.elim _ _]

/-- …so the inverse absorbs it. -/
theorem classRunIso_inv_eq {τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)} (h : cross c = τ)
    (h' : cross c' = τ) (k : c ⟶ c') :
    (classRunIso h).inv = (W (□n)).Q.map k ≫ (classRunIso h').inv :=
  (cancel_epi (classRunIso h).hom).mp (by
    rw [Iso.hom_inv_id, ← Category.assoc, classRunIso_hom_comp h h' k, Iso.hom_inv_id])

/-- **A refinement, conjugated onto the runs of its two classes** — `(classRunIso h).symm.homCongr
(classRunIso h').symm`, so `Iso.homCongr_comp` is the whole of its multiplicativity. -/
noncomputable def conjRun {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = τ)
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') :
    (W (□n)).Q.obj (wordRun σ).chain ⟶ (W (□n)).Q.obj (wordRun τ).chain :=
  (classRunIso h).hom ≫ g ≫ (classRunIso h').inv

/-- The conjugate of a composite is the composite of the conjugates. -/
theorem conjRun_comp {σ τ ρ : Equiv.Perm (Fin n)} {c c' c'' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = τ) (h'' : cross c'' = ρ)
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c')
    (g' : (W (□n)).Q.obj c' ⟶ (W (□n)).Q.obj c'') :
    conjRun h h'' (g ≫ g') = conjRun h h' g ≫ conjRun h' h'' g' :=
  Iso.homCongr_comp (classRunIso h).symm (classRunIso h').symm (classRunIso h'').symm g g'

/-- **A refinement conjugates to the fraction its target names.** -/
theorem conjRun_map {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = τ) (f : c ⟶ c') :
    conjRun h h' ((W (□n)).Q.map f) = (W (□n)).Q.map (runHom h ≫ f) ≫ (classRunIso h').inv := by
  rw [conjRun, runIso_hom, ← Category.assoc, ← Functor.map_comp]

/-- **A merge conjugates to the identity** — it stays inside one class, whose run it came from. -/
theorem conjRun_wInv {σ : Equiv.Perm (Fin n)} {c c' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = σ) {w : c ⟶ c'} (hw : W (□n) w) :
    conjRun h' h (Localization.Construction.wInv w hw) = 𝟙 _ := by
  rw [conjRun, ← classRunIso_hom_comp h h' w, Category.assoc,
    show (W (□n)).Q.map w ≫ Localization.Construction.wInv w hw ≫ (classRunIso h).inv
      = (classRunIso h).inv from
    (Localization.Construction.wIso w hw).hom_inv_id_assoc _]
  exact (classRunIso h).hom_inv_id

/-- Conjugating a refinement out of a run only sees where it lands. -/
theorem conjRun_map_run {σ τ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (h : cross d = τ) :
    conjRun (cross_wordRun σ) h ((W (□n)).Q.map u)
      = (W (□n)).Q.map u ≫ (classRunIso h).inv := by
  rw [conjRun_map, show runHom (cross_wordRun σ) ≫ u = u from Subsingleton.elim _ _]

/-- **A fraction out of a run depends only on the class it lands in.**  Two faces of one class have
a common coarsening in that class (`exists_meet_W`), and both fractions collapse onto it. -/
theorem conjRun_map_eq {σ τ : Equiv.Perm (Fin n)} {d d' : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (u' : (wordRun σ).chain ⟶ d')
    (h : cross d = τ) (h' : cross d' = τ) :
    conjRun (cross_wordRun σ) h ((W (□n)).Q.map u)
      = conjRun (cross_wordRun σ) h' ((W (□n)).Q.map u') := by
  obtain ⟨e, w, w', hw, hw'⟩ := exists_meet_W (W_runHom h) (W_runHom h')
  have he : cross e = τ := by
    rw [← h]
    exact (WeakOrder.of_injective (weakClass_eq_of_W hw)).symm
  rw [conjRun_map_run u h, conjRun_map_run u' h', classRunIso_inv_eq h he w,
    classRunIso_inv_eq h' he w', ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, show u ≫ w = u' ≫ w' from Subsingleton.elim _ _]

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

/-! ## The weak order as a step diagram

A vertex is a weak-order class, carrying its run's localized object; a step is one adjacent
descent, carrying the atom fraction out of that run.  `conjRun_map_eq` is why a step carries a
single arrow rather than a choice of face. -/

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
fractions. -/
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

/-! ## Every morphism is a path of atom steps -/

/-- A refinement that crosses nothing conjugates to the empty path. -/
private theorem path_of_W {σ τ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (h : cross d = τ) (hds : cross d = σ) :
    ∃ P : Relation.StepDiagram.Path (cubeStep n) σ τ,
      P.ev = conjRun (cross_wordRun σ) h ((W (□n)).Q.map u) := by
  obtain rfl : σ = τ := hds.symm.trans h
  have hu : (W (□n)).Q.map u = (classRunIso h).hom := by
    rw [runIso_hom]
    exact congrArg _ (Subsingleton.elim _ _)
  have hid : conjRun (cross_wordRun σ) h ((W (□n)).Q.map u) = 𝟙 _ := by
    rw [conjRun_map_run u h, hu, Iso.hom_inv_id]
  exact ⟨.nil, hid.symm⟩

/-- **A fraction conjugates to one out of the source's class run.**  Every generation step below
reads a morphism this way, so the rewrite is named once. -/
theorem conjRun_out_run {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)} (hc : cross c = σ)
    (hc' : cross c' = τ) (f : c ⟶ c') :
    conjRun hc hc' ((W (□n)).Q.map f)
      = conjRun (cross_wordRun σ) hc' ((W (□n)).Q.map (runHom hc ≫ f)) := by
  rw [conjRun_map, conjRun_map_run, Functor.map_comp, Category.assoc]

/-- **Generation, out of a run**: a refinement of a run conjugates to a path of atom steps. -/
theorem path_of_run_map {σ : Equiv.Perm (Fin n)} : ∀ {τ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (h : cross d = τ),
    ∃ P : Relation.StepDiagram.Path (cubeStep n) σ τ,
      P.ev = conjRun (cross_wordRun σ) h ((W (□n)).Q.map u) := by
  induction σ using permLen_strongRec with
  | _ σ ih =>
    intro τ d u h
    by_cases hds : cross d = σ
    · exact path_of_W u h hds
    obtain ⟨i, e, hdesc, ⟨v⟩, ⟨w⟩, hce⟩ := exists_atom_factor u hds
    have hlen := permLen_mul_adjT_of_descent hdesc
    have hsplit : conjRun (cross_wordRun σ) h ((W (□n)).Q.map u)
        = conjRun (cross_wordRun σ) hce ((W (□n)).Q.map v)
          ≫ conjRun (cross_wordRun (σ * adjT i)) h ((W (□n)).Q.map (runHom hce ≫ w)) := by
      rw [show u = v ≫ w from Subsingleton.elim _ _, Functor.map_comp,
        conjRun_comp (cross_wordRun σ) hce h, conjRun_out_run hce h w]
    obtain ⟨P, hP⟩ := ih (σ * adjT i) (by omega) (runHom hce ≫ w) h
    refine ⟨.cons (a := σ) (b := σ * adjT i) ⟨i, hdesc, rfl⟩ P, ?_⟩
    rw [Relation.StepDiagram.Path.ev_cons, hP, cubeStep_arr_eq _ v hce]
    exact hsplit.symm

/-- One step of a path, read out of the class run. -/
theorem path_of_step {σ ρ : Equiv.Perm (Fin n)} {d e : Ch (□n)}
    (hd : cross d = σ) (he : cross e = ρ) (v : d ⟶ e) :
    ∃ P : Relation.StepDiagram.Path (cubeStep n) σ ρ,
      P.ev = conjRun hd he ((W (□n)).Q.map v) := by
  rw [conjRun_out_run hd he v]
  exact path_of_run_map (runHom hd ≫ v) he

/-- **Every morphism of the localized cube slice is a path of atom steps.**  Induction over
`Q`-images and formal inverses, the statement conjugated onto the runs. -/
theorem exists_path_of_hom {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)} (hc : cross c = σ)
    (hc' : cross c' = τ) (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') :
    ∃ P : Relation.StepDiagram.Path (cubeStep n) σ τ, P.ev = conjRun hc hc' g := by
  induction hc
  induction hc'
  refine Localization.Construction.hom_induction (W (□n))
    (fun c c' g => ∀ (σ τ : Equiv.Perm (Fin n)) (hc : cross c = σ) (hc' : cross c' = τ),
      ∃ P : Relation.StepDiagram.Path (cubeStep n) σ τ, P.ev = conjRun hc hc' g)
    (fun _ m _ u v hu hv σ ρ hc hc'' => ?_) (fun {a _} f σ τ hc hc' => path_of_step hc hc' f)
    (fun w hw σ τ hc hc' => ?_) g (cross c) (cross c') rfl rfl
  · obtain ⟨P, hP⟩ := hu σ _ hc rfl
    obtain ⟨Q, hQ⟩ := hv _ ρ rfl hc''
    refine ⟨P.comp Q, ?_⟩
    rw [Relation.StepDiagram.Path.ev_comp, hP, hQ]
    exact (conjRun_comp hc (rfl : cross m = cross m) hc'' u v).symm
  · obtain rfl : σ = τ :=
      hc.symm.trans ((WeakOrder.of_injective (weakClass_eq_of_W hw)).symm.trans hc')
    exact ⟨.nil, (conjRun_wInv hc' hc hw).symm⟩

/-! ## The diamond -/

/-- The crossing permutation of a refinement of a run, read off where it lands. -/
private theorem crossPerm_of_run {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {d : Ch (□n)}
    (u : (wordRun σ).chain ⟶ d) (hd : cross d = σ * adjT i) :
    crossPerm (dimSum_dims_cube (wordRun σ).chain) u = adjT i := by
  have h := cross_eq_mul u
  rw [cross_wordRun, hd] at h
  have h2 := congrArg (fun x : Equiv.Perm (Fin n) => (σ * adjT i)⁻¹ * x) h
  simp only [inv_mul_cancel_left] at h2
  rw [← h2, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
    show ((adjT i)⁻¹ : Equiv.Perm (Fin n)) = adjT i from by rw [adjT, Equiv.swap_inv]]

/-- The canonical atom face of a descent, with its arrow and its codimension. -/
private theorem exists_atom_codim {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
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
  obtain ⟨dc, uc, hdc, hcu⟩ := exists_atom_codim hdi
  obtain ⟨dc', uc', hdc', hcu'⟩ := exists_atom_codim hdj
  have hne : dc ≠ dc' := fun hx =>
    (Nat.ne_of_lt hij)
      (adjT_inj (mul_left_cancel (show σ * adjT i = σ * adjT j by rw [← hdc, hx, hdc'])))
  obtain ⟨e, v, v', hcv, hcv'⟩ := exists_join uc uc' hcu hcu' hne
  have hlen : e.dims.length + 2 = n := length_of_two_steps (wordRun σ).ones uc v hcu hcv
  have hce : cross e = cross e := rfl
  obtain ⟨P, hP⟩ := path_of_step hdc hce v
  obtain ⟨Q, hQ⟩ := path_of_step hdc' hce v'
  refine ⟨cross e, P, Q, ?_, ?_⟩
  · rw [cubeStep_arr_eq hb uc hdc, cubeStep_arr_eq hc uc' hdc', hP, hQ]
    refine ((conjRun_comp (cross_wordRun σ) hdc hce _ _).symm.trans ?_).trans
      (conjRun_comp (cross_wordRun σ) hdc' hce _ _)
    rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim (uc ≫ v) (uc' ≫ v')]
  · intro t h1 h2
    refine absorb_of_le (fun x k1 k2 => ?_) h1 h2
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hfar | hadj
    · rw [cross_of_meet_far (cross_wordRun σ) hfar (crossPerm_of_run uc hdc)
        (crossPerm_of_run uc' hdc') v v' hlen]
      exact WeakOrder.le_mul_adjT_mul_adjT hfar hdi hdj k1 k2
    · rw [cross_of_meet_braid (cross_wordRun σ) (by omega) (crossPerm_of_run uc hdc)
        (crossPerm_of_run uc' hdc') v v' hlen]
      exact WeakOrder.le_mul_adjT_braid (by omega) hdi hdj k1 k2

/-- **The cube's atom steps close diamonds.**  Swapping the two cuts swaps the two legs. -/
theorem cubeStep_hasDiamonds (n : ℕ) : (cubeStep n).HasDiamonds := by
  rintro σ b c ⟨i, hdi, rfl⟩ ⟨j, hdj, rfl⟩ hne
  have hij : (i : ℕ) ≠ (j : ℕ) := fun hx => hne (by rw [Fin.ext hx])
  rcases lt_or_gt_of_ne hij with h | h
  · exact cubeStep_diamond_lt hdi hdj h _ _
  · obtain ⟨d, P, Q, harr, habs⟩ := cubeStep_diamond_lt hdj hdi h ⟨j, hdj, rfl⟩ ⟨i, hdi, rfl⟩
    exact ⟨d, Q, P, harr.symm, fun {_} h1 h2 => habs h2 h1⟩

/-! ## Thinness -/

/-- **The localized cube slice is thin** — `Relation.StepDiagram.isThin_of_hasDiamonds` at
`cubeStep`, so reachability in the weak order stands in for the spanning theorem. -/
instance locCube_isThin (n : ℕ) : Quiver.IsThin ((W (□n)).Localization) :=
  Relation.StepDiagram.isThin_of_hasDiamonds (cubeStep_hasDiamonds n)
    (fun X => by
      obtain ⟨c, rfl⟩ := Localization.Construction.exists_Q_obj (W (□n)) X
      exact ⟨cross c, ⟨classRunIso (rfl : cross c = cross c)⟩⟩)
    (fun a b f => by
      obtain ⟨P, hP⟩ := exists_path_of_hom (cross_wordRun a) (cross_wordRun b) f
      exact ⟨P, hP.trans (conjRun_run_run f)⟩)

/-- **The hom-sets are the order relation**: `weakClass_le_of_loc_hom` one way, the spanning
theorem the other. -/
theorem nonempty_loc_hom_iff {c c' : Ch (□n)} :
    Nonempty ((W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') ↔ weakClass c' ≤ weakClass c :=
  ⟨fun ⟨g⟩ => weakClass_le_of_loc_hom g, nonempty_loc_hom⟩

/-- **`Q cubeTop` is a terminal object of the localized cube slice**: every chain refines the
one-bead chain, and thinness supplies the uniqueness. -/
noncomputable def isTerminal_locCubeTop :
    Limits.IsTerminal ((W (□n)).Q.obj (cubeTop n)) :=
  Limits.IsTerminal.ofUniqueHom (fun X => (W (□n)).Q.map (toCubeTop X.as.obj))
    fun _ _ => Subsingleton.elim _ _

end ChainCat
