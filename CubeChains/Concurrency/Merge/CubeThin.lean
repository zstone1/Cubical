import CubeChains.Machinery.Localization.HomInduction
import CubeChains.Concurrency.Merge.CubeFaces
import CubeChains.Concurrency.Merge.CubeSpanning

/-!
# Concurrency/Merge/CubeThin — the localized cube slice is thin

`Ch (□n)[W⁻¹]` is a poset (`locCube_isThin`).  Every chain is entered from its class's run by a
merge, so a morphism is read between runs (`conjRun`): there a merge becomes the identity
(`conjRun_wInv`), and a refinement becomes the fraction its target names, which depends only on
that target's class (`conjRun_map_eq`).  So every morphism is a word in the atom steps
(`exists_word_of_hom`), and two words with the same endpoints agree (`word_unique`) — a shared
first cut reduces, distinct cuts close by the diamond of `CubeFaces`.

Only *uniqueness* is proved here.  Which words exist is the base's spanning theorem, read at the
cube (`CubeSpanning`'s `nonempty_loc_hom`); `exists_word` is that arrow, spelled.
-/

open CategoryTheory BPSet CubeChains CubeChain

namespace ChainCat

variable {n : ℕ}

/-! ## Conjugating onto the runs

Every chain is entered from its class's run by a merge, so a morphism of the localization can be
read between runs.  A refinement becomes the fraction its target names; a merge becomes the
identity, which is what lets a composite be read as a word in the atoms alone. -/

theorem nonempty_runHom (c : Ch (□n)) : Nonempty ((runAt (cross c)).chain ⟶ c) := by
  obtain ⟨r, f, hr, hf⟩ := exists_W_run c
  have hcr : cross r = cross c := WeakOrder.of_injective (weakClass_eq_of_W hf)
  have hre : r = (runAt (cross c)).chain :=
    run_eq_of_cross_eq hr (run_dims (runAt (cross c))) (by rw [hcr, cross_runAt])
  exact ⟨hre ▸ f⟩

/-- The merge from the class's run into a chain. -/
noncomputable def runHom {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    (runAt σ).chain ⟶ c :=
  (h ▸ nonempty_runHom c).some

theorem W_runHom {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    W (□n) (runHom h) :=
  W_of_cross_eq _ (by rw [cross_runAt, h])

/-- …and the isomorphism it becomes. -/
noncomputable def classRunIso {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    (W (□n)).Q.obj (runAt σ).chain ≅ (W (□n)).Q.obj c :=
  Localization.Construction.wIso (runHom h) (W_runHom h)

@[simp] theorem runIso_hom {σ : Equiv.Perm (Fin n)} {c : Ch (□n)} (h : cross c = σ) :
    (classRunIso h).hom = (W (□n)).Q.map (runHom h) := rfl

/-- **A refinement, conjugated onto the runs of its two classes.** -/
noncomputable def conjRun {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = τ)
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') :
    (W (□n)).Q.obj (runAt σ).chain ⟶ (W (□n)).Q.obj (runAt τ).chain :=
  (classRunIso h).hom ≫ g ≫ (classRunIso h').inv

/-- The conjugate of a composite is the composite of the conjugates. -/
theorem conjRun_comp {σ τ ρ : Equiv.Perm (Fin n)} {c c' c'' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = τ) (h'' : cross c'' = ρ)
    (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c')
    (g' : (W (□n)).Q.obj c' ⟶ (W (□n)).Q.obj c'') :
    conjRun h h'' (g ≫ g') = conjRun h h' g ≫ conjRun h' h'' g' := by
  simp only [conjRun, Category.assoc, Iso.inv_hom_id_assoc]

/-- **A refinement conjugates to the fraction its target names.** -/
theorem conjRun_map {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = τ) (f : c ⟶ c') :
    conjRun h h' ((W (□n)).Q.map f) = (W (□n)).Q.map (runHom h ≫ f) ≫ (classRunIso h').inv := by
  rw [conjRun, runIso_hom, ← Category.assoc, ← Functor.map_comp]

/-- **THE RISK CHECK: a merge conjugates to the identity.** -/
theorem conjRun_wInv {σ : Equiv.Perm (Fin n)} {c c' : Ch (□n)}
    (h : cross c = σ) (h' : cross c' = σ) {w : c ⟶ c'} (hw : W (□n) w) :
    conjRun h' h (Localization.Construction.wInv w hw) = 𝟙 _ := by
  have hcomp : runHom h ≫ w = runHom h' := Subsingleton.elim _ _
  have hio : (classRunIso h').hom = (classRunIso h).hom ≫ (W (□n)).Q.map w := by
    rw [runIso_hom, runIso_hom, ← Functor.map_comp, hcomp]
  rw [conjRun, hio, Category.assoc]
  rw [show (W (□n)).Q.map w ≫ Localization.Construction.wInv w hw ≫ (classRunIso h).inv
      = (classRunIso h).inv from
    (Localization.Construction.wIso w hw).hom_inv_id_assoc _]
  exact (classRunIso h).hom_inv_id


/-- Conjugating a refinement out of a run only sees where it lands. -/
theorem conjRun_map_run {σ τ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (h : cross d = τ) :
    conjRun (cross_runAt σ) h ((W (□n)).Q.map u)
      = (W (□n)).Q.map u ≫ (classRunIso h).inv := by
  rw [conjRun_map, show runHom (cross_runAt σ) ≫ u = u from Subsingleton.elim _ _]

/-- **A fraction out of a run depends only on the class it lands in.**  Two faces of one class have
a common coarsening in that class (`exists_meet_W`), and both fractions collapse onto it. -/
theorem conjRun_map_eq {σ τ : Equiv.Perm (Fin n)} {d d' : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (u' : (runAt σ).chain ⟶ d')
    (h : cross d = τ) (h' : cross d' = τ) :
    conjRun (cross_runAt σ) h ((W (□n)).Q.map u)
      = conjRun (cross_runAt σ) h' ((W (□n)).Q.map u') := by
  obtain ⟨e, w, w', hw, hw'⟩ := exists_meet_W (W_runHom h) (W_runHom h')
  have he : cross e = τ := by
    rw [← h]
    exact (WeakOrder.of_injective (weakClass_eq_of_W hw)).symm
  have hfac : ∀ {c : Ch (□n)} (hc : cross c = τ) (k : c ⟶ e),
      (classRunIso hc).inv = (W (□n)).Q.map k ≫ (classRunIso he).inv := by
    intro c hc k
    have hrk : runHom hc ≫ k = runHom he := Subsingleton.elim _ _
    have hio : (classRunIso he).hom = (classRunIso hc).hom ≫ (W (□n)).Q.map k := by
      rw [runIso_hom, runIso_hom, ← Functor.map_comp, hrk]
    refine (cancel_epi (classRunIso hc).hom).mp ?_
    rw [Iso.hom_inv_id, ← Category.assoc, ← hio, Iso.hom_inv_id]
  rw [conjRun_map_run u h, conjRun_map_run u' h', hfac h w, hfac h' w',
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    show u ≫ w = u' ≫ w' from Subsingleton.elim _ _]

/-! ## Words in the atom steps -/

/-- **A word in the atom steps**: a morphism of the localization spelled as a chain of covers
between the runs of the weak-order classes it passes through. -/
inductive Word : ∀ (σ τ : Equiv.Perm (Fin n)),
    ((W (□n)).Q.obj (runAt σ).chain ⟶ (W (□n)).Q.obj (runAt τ).chain) → Prop
  | nil (σ : Equiv.Perm (Fin n)) : Word σ σ (𝟙 _)
  | cons {σ τ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {d : Ch (□n)}
      (u : (runAt σ).chain ⟶ d) (hd : cross d = σ * adjT i)
      {h : (W (□n)).Q.obj (runAt (σ * adjT i)).chain ⟶ (W (□n)).Q.obj (runAt τ).chain} :
      Word (σ * adjT i) τ h →
      Word σ τ (conjRun (cross_runAt σ) hd ((W (□n)).Q.map u) ≫ h)

theorem Word.comp {σ τ ρ : Equiv.Perm (Fin n)}
    {h : (W (□n)).Q.obj (runAt σ).chain ⟶ (W (□n)).Q.obj (runAt τ).chain}
    {h' : (W (□n)).Q.obj (runAt τ).chain ⟶ (W (□n)).Q.obj (runAt ρ).chain}
    (w : Word σ τ h) (w' : Word τ ρ h') : Word σ ρ (h ≫ h') := by
  induction w with
  | nil s => simpa using w'
  | cons u hd _ ih =>
    rw [Category.assoc]
    exact Word.cons u hd (ih w')

/-- The run of a class carries no bead of dimension above one. -/
theorem run_ones (σ : Equiv.Perm (Fin n)) : ∀ x ∈ (runAt σ).chain.dims, x = 1 :=
  fun x hx => List.eq_of_mem_replicate (by rw [← run_dims (runAt σ)]; exact hx)

/-- A refinement that crosses nothing conjugates to the empty word. -/
private theorem word_of_W {σ τ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (h : cross d = τ) (hds : cross d = σ) :
    Word σ τ (conjRun (cross_runAt σ) h ((W (□n)).Q.map u)) := by
  obtain rfl : σ = τ := hds.symm.trans h
  have hid : conjRun (cross_runAt σ) h ((W (□n)).Q.map u) = 𝟙 _ := by
    have hu : (W (□n)).Q.map u = (classRunIso h).hom := by
      rw [runIso_hom]
      exact congrArg _ (Subsingleton.elim _ _)
    rw [conjRun_map_run u h, hu, Iso.hom_inv_id]
  rw [hid]
  exact Word.nil _

/-- **A fraction conjugates to one out of the source's class run.**  Every generation step below
reads a morphism this way, so the rewrite is named once. -/
theorem conjRun_out_run {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)} (hc : cross c = σ)
    (hc' : cross c' = τ) (f : c ⟶ c') :
    conjRun hc hc' ((W (□n)).Q.map f)
      = conjRun (cross_runAt σ) hc' ((W (□n)).Q.map (runHom hc ≫ f)) := by
  rw [conjRun_map, conjRun_map_run, Functor.map_comp, Category.assoc]

/-- **Generation, out of a run**: a refinement of a run conjugates to a word in the atoms. -/
theorem word_of_run_map {σ : Equiv.Perm (Fin n)} : ∀ {τ : Equiv.Perm (Fin n)} {d : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (h : cross d = τ),
    Word σ τ (conjRun (cross_runAt σ) h ((W (□n)).Q.map u)) := by
  induction σ using permLen_strongRec with
  | _ σ ih =>
    intro τ d u h
    by_cases hds : cross d = σ
    · exact word_of_W u h hds
    obtain ⟨i, e, hdesc, ⟨v⟩, ⟨w⟩, hce⟩ := exists_atom_factor u hds
    have hlen := permLen_mul_adjT_of_descent hdesc
    rw [show u = v ≫ w from Subsingleton.elim _ _, Functor.map_comp,
      conjRun_comp (cross_runAt σ) hce h, conjRun_out_run hce h w]
    exact Word.cons v hce (ih (σ * adjT i) (by omega) (runHom hce ≫ w) h)

/-- One step of a word, read out of the class run. -/
theorem word_of_step {σ ρ : Equiv.Perm (Fin n)} {d e : Ch (□n)}
    (hd : cross d = σ) (he : cross e = ρ) (v : d ⟶ e) :
    Word σ ρ (conjRun hd he ((W (□n)).Q.map v)) := by
  rw [conjRun_out_run hd he v]
  exact word_of_run_map (runHom hd ≫ v) he


/-! ## Every morphism is a word -/

/-- **Every morphism of the localized cube slice is a word in the atoms.**  Induction over
`Q`-images and formal inverses, the statement conjugated onto the runs. -/
theorem exists_word_of_hom {σ τ : Equiv.Perm (Fin n)} {c c' : Ch (□n)} (hc : cross c = σ)
    (hc' : cross c' = τ) (g : (W (□n)).Q.obj c ⟶ (W (□n)).Q.obj c') :
    Word σ τ (conjRun hc hc' g) := by
  induction hc
  induction hc'
  refine Localization.Construction.hom_induction (W (□n))
    (fun c c' g => ∀ (σ τ : Equiv.Perm (Fin n)) (hc : cross c = σ) (hc' : cross c' = τ),
      Word σ τ (conjRun hc hc' g))
    (fun _ m _ u v hu hv σ ρ hc hc'' => ?_) (fun {a _} f σ τ hc hc' => word_of_step hc hc' f)
    (fun w hw σ τ hc hc' => ?_) g (cross c) (cross c') rfl rfl
  · rw [conjRun_comp hc (rfl : cross m = cross m) hc'']
    exact Word.comp (hu σ _ hc rfl) (hv _ ρ rfl hc'')
  · obtain rfl : σ = τ :=
      hc.symm.trans ((WeakOrder.of_injective (weakClass_eq_of_W hw)).symm.trans hc')
    rw [conjRun_wInv hc' hc hw]
    exact Word.nil σ

/-- **Fullness**: everything the weak order allows is spelled by a word.  The arrow is the base's
(`nonempty_loc_hom`); reading it between the two classes' runs is what spells it. -/
theorem exists_word (σ τ : Equiv.Perm (Fin n)) (hle : WeakOrder.of τ ≤ WeakOrder.of σ) :
    ∃ g, Word σ τ g := by
  obtain ⟨g⟩ := nonempty_loc_hom (c := (runAt σ).chain) (c' := (runAt τ).chain)
    (show WeakOrder.of (cross (runAt τ).chain) ≤ WeakOrder.of (cross (runAt σ).chain) by
      rw [cross_runAt, cross_runAt]; exact hle)
  exact ⟨_, exists_word_of_hom (cross_runAt σ) (cross_runAt τ) g⟩

/-! ## Thinness -/

/-- The crossing permutation of a refinement of a run, read off where it lands. -/
private theorem crossPerm_of_run {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {d : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (hd : cross d = σ * adjT i) :
    crossPerm (dimSum_dims_cube (runAt σ).chain) u = adjT i := by
  have h := cross_eq_mul u
  rw [cross_runAt, hd] at h
  have h2 := congrArg (fun x : Equiv.Perm (Fin n) => (σ * adjT i)⁻¹ * x) h
  simp only [inv_mul_cancel_left] at h2
  rw [← h2, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one,
    show ((adjT i)⁻¹ : Equiv.Perm (Fin n)) = adjT i from by rw [adjT, Equiv.swap_inv]]

/-- A step of a word descends the weak order strictly, so its cut is a descent. -/
theorem descent_of_word_step {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)} {d : Ch (□n)}
    (u : (runAt σ).chain ⟶ d) (hd : cross d = σ * adjT i) :
    σ (adjHi i) < σ (adjLo i) := by
  have hle := weakClass_le u
  rw [weakClass, weakClass, cross_runAt, hd] at hle
  have hp := WeakOrder.permLen_le_of_le hle
  simp only [WeakOrder.perm_of] at hp
  rcases lt_trichotomy (σ (adjLo i)) (σ (adjHi i)) with h | h | h
  · rw [permLen_mul_adjT h] at hp; omega
  · exact absurd (σ.injective h) (adjLo_ne_adjHi i)
  · exact h

/-- **A word only goes down the weak order.** -/
theorem word_le {σ τ : Equiv.Perm (Fin n)}
    {g : (W (□n)).Q.obj (runAt σ).chain ⟶ (W (□n)).Q.obj (runAt τ).chain} (w : Word σ τ g) :
    WeakOrder.of τ ≤ WeakOrder.of σ := by
  induction w with
  | nil s => exact le_refl _
  | cons u hd _ ih => exact ih.trans (WeakOrder.of_mul_adjT_le (descent_of_word_step u hd))

/-- The canonical atom face of a descent, with its arrow and its codimension. -/
private theorem exists_atom_codim {σ : Equiv.Perm (Fin n)} {i : Fin (n - 1)}
    (hdi : σ (adjHi i) < σ (adjLo i)) :
    ∃ (dc : Ch (□n)) (uc : (runAt σ).chain ⟶ dc), cross dc = σ * adjT i ∧ codim uc = 1 := by
  obtain ⟨dc, uc, hdc, hdim⟩ :=
    exists_atom_face (run_ones σ) (by rw [cross_runAt]; exact hdi)
  rw [cross_runAt] at hdc
  refine ⟨dc, uc, hdc, ?_⟩
  have h0 : degree (runAt σ).chain = 0 := (degree_eq_zero_iff _).mpr (run_ones σ)
  have h1 : degree dc = 1 := by
    rw [degree, hdim]
    have := degree_atomComp n i
    rwa [degree, zObj_dims] at this
  rw [codim, h0, h1]

/-- The two atoms `i`, `j` out of the run of `σ` meet in a face whose class absorbs everything
below both of theirs. -/
private def Diamond (σ : Equiv.Perm (Fin n)) (i j : Fin (n - 1)) : Prop :=
  ∃ (ρ : Equiv.Perm (Fin n)) (e dc dc' : Ch (□n))
    (_ : (runAt σ).chain ⟶ dc) (_ : (runAt σ).chain ⟶ dc')
    (_ : dc ⟶ e) (_ : dc' ⟶ e),
    cross dc = σ * adjT i ∧ cross dc' = σ * adjT j ∧ cross e = ρ ∧
    ∀ x : WeakOrder n, x ≤ WeakOrder.of (σ * adjT i) → x ≤ WeakOrder.of (σ * adjT j) →
      x ≤ WeakOrder.of ρ

/-- The diamond, with the two cuts in order — the two cases the meet's `cross` splits into. -/
private theorem word_diamond_lt {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)}
    (hdi : σ (adjHi i) < σ (adjLo i)) (hdj : σ (adjHi j) < σ (adjLo j))
    (hij : (i : ℕ) < (j : ℕ)) : Diamond σ i j := by
  obtain ⟨dc, uc, hdc, hcu⟩ := exists_atom_codim hdi
  obtain ⟨dc', uc', hdc', hcu'⟩ := exists_atom_codim hdj
  have hne : dc ≠ dc' := fun hc =>
    (Nat.ne_of_lt hij)
      (adjT_inj (mul_left_cancel (show σ * adjT i = σ * adjT j by rw [← hdc, hc, hdc'])))
  obtain ⟨e, v, v', hcv, hcv'⟩ := exists_join uc uc' hcu hcu' hne
  have hlen : e.dims.length + 2 = n := length_of_two_steps (run_ones σ) uc v hcu hcv
  refine ⟨cross e, e, dc, dc', uc, uc', v, v', hdc, hdc', rfl, ?_⟩
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hfar | hadj
  · rw [cross_of_meet_far (cross_runAt σ) hfar (crossPerm_of_run uc hdc)
      (crossPerm_of_run uc' hdc') v v' hlen]
    exact fun x h1 h2 => WeakOrder.le_mul_adjT_mul_adjT hfar hdi hdj h1 h2
  · rw [cross_of_meet_braid (cross_runAt σ) (by omega) (crossPerm_of_run uc hdc)
      (crossPerm_of_run uc' hdc') v v' hlen]
    exact fun x h1 h2 => WeakOrder.le_mul_adjT_braid (by omega) hdi hdj h1 h2

/-- **The diamond**: two distinct atoms out of a run meet in one face, and everything below both
their classes is below the meet's.  Swapping the two cuts swaps the two legs. -/
private theorem word_diamond {σ : Equiv.Perm (Fin n)} {i j : Fin (n - 1)}
    (hdi : σ (adjHi i) < σ (adjLo i)) (hdj : σ (adjHi j) < σ (adjLo j))
    (hij : (i : ℕ) ≠ (j : ℕ)) : Diamond σ i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact word_diamond_lt hdi hdj h
  · obtain ⟨ρ, e, dc, dc', uc, uc', v, v', hdc, hdc', hce, hord⟩ := word_diamond_lt hdj hdi h
    exact ⟨ρ, e, dc', dc, uc', uc, v', v, hdc', hdc, hce, fun x h1 h2 => hord x h2 h1⟩

/-- **Two words with the same endpoints are equal.**  Induction on the source's length: a shared
first cut reduces, and distinct cuts are closed by the diamond. -/
theorem word_unique {σ : Equiv.Perm (Fin n)} : ∀ {τ : Equiv.Perm (Fin n)}
    {g g' : (W (□n)).Q.obj (runAt σ).chain ⟶ (W (□n)).Q.obj (runAt τ).chain},
    Word σ τ g → Word σ τ g' → g = g' := by
  induction σ using permLen_strongRec with
  | _ σ ih =>
    intro τ g g' w w'
    cases w with
    | nil s =>
      cases w' with
      | nil s' => rfl
      | cons u' hd' w0' =>
        have h1 := permLen_mul_adjT_of_descent (descent_of_word_step u' hd')
        have h2 := WeakOrder.permLen_le_of_le (word_le w0')
        simp only [WeakOrder.perm_of] at h2
        omega
    | @cons _ _ i d u hd h w0 =>
      cases w' with
      | nil s' =>
        have h1 := permLen_mul_adjT_of_descent (descent_of_word_step u hd)
        have h2 := WeakOrder.permLen_le_of_le (word_le w0)
        simp only [WeakOrder.perm_of] at h2
        omega
      | @cons _ _ j d' u' hd' h' w0' =>
        have hdi := descent_of_word_step u hd
        have hlen := permLen_mul_adjT_of_descent hdi
        by_cases hij : (i : ℕ) = (j : ℕ)
        · obtain rfl : i = j := Fin.ext hij
          rw [conjRun_map_eq u u' hd hd']
          congr 1
          exact ih (σ * adjT i) (by omega) w0 w0'
        · have hdj := descent_of_word_step u' hd'
          have hlenj := permLen_mul_adjT_of_descent hdj
          obtain ⟨ρ, e, dc, dc', uc, uc', v, v', hdc, hdc', hce, hord⟩ :=
            word_diamond hdi hdj hij
          have hτ : WeakOrder.of τ ≤ WeakOrder.of ρ := hord _ (word_le w0) (word_le w0')
          obtain ⟨kw, hkw⟩ := exists_word ρ τ hτ
          have ht : h = conjRun hdc hce ((W (□n)).Q.map v) ≫ kw :=
            ih (σ * adjT i) (by omega) w0 ((word_of_step hdc hce v).comp hkw)
          have ht' : h' = conjRun hdc' hce ((W (□n)).Q.map v') ≫ kw :=
            ih (σ * adjT j) (by omega) w0' ((word_of_step hdc' hce v').comp hkw)
          rw [conjRun_map_eq u uc hd hdc, conjRun_map_eq u' uc' hd' hdc', ht, ht',
            ← Category.assoc, ← Category.assoc,
            ← conjRun_comp (cross_runAt σ) hdc hce, ← conjRun_comp (cross_runAt σ) hdc' hce,
            ← Functor.map_comp, ← Functor.map_comp,
            show uc ≫ v = uc' ≫ v' from Subsingleton.elim _ _]

/-- **The localized cube slice is thin.** -/
instance locCube_isThin (n : ℕ) : Quiver.IsThin ((W (□n)).Localization) := by
  intro X Y
  obtain ⟨c, rfl⟩ := Localization.Construction.exists_Q_obj _ X
  obtain ⟨c', rfl⟩ := Localization.Construction.exists_Q_obj _ Y
  refine ⟨fun g g' => ?_⟩
  have hc := word_unique (exists_word_of_hom rfl rfl g) (exists_word_of_hom rfl rfl g')
  rw [conjRun, conjRun] at hc
  exact (cancel_mono (classRunIso (rfl : cross c' = cross c')).inv).mp
    ((cancel_epi (classRunIso (rfl : cross c = cross c)).hom).mp hc)

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
