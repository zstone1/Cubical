import CubeChains.Concurrency.Presentation.SliceRuns
import CubeChains.Concurrency.Presentation.CutPresentation
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.HomCongr

/-!
# Concurrency/Presentation/LocPresentation — the loops at a run, and the Artin relations

A generator of the cut presentation out of the run on `N` events is an atom (`Cut.exists_atomComp`).
Inverting the merges makes every chain its own run (`runIso`), so a refinement is conjugated onto a
loop there (`conj`) which sees only the crossing permutation (`conj_eq_runLoop`).  Appending an atom
across an ascent multiplies the crossings (`runLoop_comp`), and that single fact is both Artin
relations (`atomLoop_comm`, `atomLoop_braid`) and the generation statement (`exists_atomWord`).
-/

open CategoryTheory Equiv Opposite BPSet CubeChains CubeChain

namespace ChainCat

set_option quotPrecheck false in
/-- The localization functor of the base, and the loops at the run of `N` events in it. -/
local notation "Qz" => ((W Zbp).op).Q
set_option quotPrecheck false in
local notation "RunEnd" N =>
  @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N))))

/-- **A generator out of the run cuts one of its `N-1` atoms' shapes** — and distinct indices name
distinct shapes (`atomComp_ne`), so the index is the generator's own. -/
theorem Cut.exists_atomComp {N : ℕ} {x : GenObj Cut.Refine} (e : x ⟶ Cut.vert (zObj (𝟙^N))) :
    ∃ k : Fin (N - 1), x.as = zObj (atomComp N k) :=
  _root_.ChainCat.exists_atomComp (Cut.genHom e) (Cut.codim_genHom e)

/-! ## Every chain is its run

Inverting the merges makes the merge out of a chain's own run an isomorphism, so a refinement is
conjugated onto a loop at that run (`conj`), and the loop sees only the crossing permutation
(`conj_congr`). -/

theorem isIso_Q_op_of_W {a b : Ch Zbp} {f : a ⟶ b} (hf : W Zbp f) :
    IsIso ((Qz).map f.op) := ((W Zbp).op).Q_inverts f.op hf

/-- **A merge is invertible in `Ch(Z)[W⁻¹]`** — the only comparison the reading of a word ever
needs. -/
noncomputable def mergeIso {a b : Ch Zbp} {m : a ⟶ b} (hm : W Zbp m) :
    (Qz).obj (op b) ≅ (Qz).obj (op a) :=
  @asIso _ _ _ _ ((Qz).map m.op) (isIso_Q_op_of_W hm)

/-- The merge into the run, in the localization. -/
noncomputable def runArrow {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    (Qz).obj (op b) ⟶ (Qz).obj (op (zObj (𝟙^N))) := (Qz).map (runMerge b hb).op

instance isIso_runArrow {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    IsIso (runArrow b hb) := isIso_Q_op_of_W (W_runMerge b hb)

/-- **A chain is its own run in the localization** — the merge out of the run is inverted. -/
noncomputable def runIso {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) :
    (Qz).obj (op b) ≅ (Qz).obj (op (zObj (𝟙^N))) := mergeIso (W_runMerge b hb)

/-- The merge out of the run into itself is the identity. -/
theorem runArrow_ones (N : ℕ) : runArrow (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ := by
  rw [runArrow, show runMerge (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ from endo_eq_id _, op_id]
  exact CategoryTheory.Functor.map_id _ _

theorem inv_runArrow_ones (N : ℕ) :
    inv (runArrow (zObj (𝟙^N)) (dimSum_replicate N)) = 𝟙 _ :=
  IsIso.inv_eq_of_hom_inv_id (by rw [Category.comp_id, runArrow_ones])

/-- **An arrow of the localized base, conjugated onto a loop at the run of `N` events** — `runIso`
at each end, so `Iso.homCongr_comp` is the whole of its multiplicativity. -/
noncomputable def runConjEquiv {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N)
    (hb : dimSum b.dims = N) : ((Qz).obj (op a) ⟶ (Qz).obj (op b)) ≃ RunEnd N :=
  (runIso a ha).homCongr (runIso b hb)

/-- **A refinement, conjugated onto a loop at the run** it is merged into from. -/
noncomputable def conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) : RunEnd N :=
  runConjEquiv (tgtStrands f ha) ha ((Qz).map f.op)

theorem conj_comp {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) (g : b ⟶ c) :
    conj ha (f ≫ g) = conj (tgtStrands f ha) g ≫ conj ha f :=
  Eq.trans (congrArg (runConjEquiv (tgtStrands g (tgtStrands f ha)) ha)
      ((Qz).map_comp g.op f.op))
    (Iso.homCongr_comp (runIso c _) (runIso b _) (runIso a ha) _ _)

theorem conj_eq_id {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) {f : a ⟶ b} (hf : W Zbp f) :
    conj ha f = 𝟙 _ := by
  have hrun : (Qz).map f.op ≫ runArrow a ha = runArrow b (tgtStrands f ha) :=
    (((Qz).map_comp f.op (runMerge a ha).op)).symm.trans
      (congrArg (fun t : zObj (𝟙^N) ⟶ b => (Qz).map t.op)
        (eq_of_W ((W Zbp).comp_mem _ _ (W_runMerge a ha) hf) (W_runMerge b (tgtStrands f ha))))
  change (runIso b (tgtStrands f ha)).inv ≫ (Qz).map f.op ≫ runArrow a ha = 𝟙 _
  rw [hrun]
  exact (runIso b (tgtStrands f ha)).inv_hom_id

theorem conj_comp_W {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) {m : b ⟶ c}
    (hm : W Zbp m) : conj ha (f ≫ m) = conj ha f := by
  rw [conj_comp, conj_eq_id _ hm, Category.id_comp]

theorem conj_W_comp {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N) {m : a ⟶ b}
    (hm : W Zbp m) (g : b ⟶ c) : conj ha (m ≫ g) = conj (tgtStrands m ha) g := by
  rw [conj_comp, conj_eq_id ha hm, Category.comp_id]

/-- **A refinement out of the run is its target's merge inverted, then itself** — the run merges
into itself by the identity, so there is nothing to conjugate on the left. -/
theorem conj_ones {N : ℕ} {b : Ch Zbp} (hb : dimSum b.dims = N) (f : zObj (𝟙^N) ⟶ b) :
    conj (dimSum_replicate N) f = (runIso b hb).inv ≫ (Qz).map f.op := by
  change (runIso b hb).inv ≫ (Qz).map f.op
      ≫ (runIso (zObj (𝟙^N)) (dimSum_replicate N)).hom = _
  rw [show (runIso (zObj (𝟙^N)) (dimSum_replicate N)).hom = 𝟙 _ from runArrow_ones N,
    Category.comp_id]

/-- **The conjugated loop sees only the crossing permutation** — merge both targets into one bead,
where a refinement is its crossing permutation. -/
theorem conj_congr {N : ℕ} {a b b' : Ch Zbp} (ha : dimSum a.dims = N) {f : a ⟶ b} {f' : a ⟶ b'}
    (h : crossPerm ha f = crossPerm ha f') : conj ha f = conj ha f' := by
  obtain ⟨m, hm⟩ := exists_W_to_top (tgtStrands f ha)
  obtain ⟨m', hm'⟩ := exists_W_to_top (tgtStrands f' ha)
  have hfm : f ≫ m = f' ≫ m' := hom_ext_of_crossPerm (h := ha) (by
    rw [crossPerm_comp ha f m, crossPerm_comp ha f' m',
      crossPerm_eq_one_of_W (tgtStrands f ha) hm,
      crossPerm_eq_one_of_W (tgtStrands f' ha) hm', one_mul, one_mul, h])
  rw [← conj_comp_W ha f hm, ← conj_comp_W ha f' hm', hfm]

/-! ## The loops at the run

A loop at the run is the word its crossing permutation spells: the crossing is all `conj` sees
(`conj_eq_runLoop`), and appending an atom across an ascent multiplies the crossings
(`runLoop_comp`). -/

/-- The loop at the run of the one-bead refinement whose crossing is `σ`. -/
noncomputable def runLoop (N : ℕ) (σ : Perm (Fin N)) : RunEnd N :=
  conj (dimSum_replicate N) ((onesTopEquiv N).symm σ)

theorem crossPerm_onesTopEquiv_symm (N : ℕ) (σ : Perm (Fin N)) :
    crossPerm (dimSum_replicate N) ((onesTopEquiv N).symm σ) = σ :=
  (onesTopEquiv N).apply_symm_apply σ

/-- **A refinement's loop is `runLoop` of its crossing permutation** — merging the source back to
the run and coarsening the target to one bead changes neither. -/
theorem conj_eq_runLoop {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    conj ha f = runLoop N (crossPerm ha f) := by
  rw [← conj_W_comp (dimSum_replicate N) (W_runMerge a ha) f]
  refine conj_congr _ ?_
  rw [crossPerm_onesTopEquiv_symm, crossPerm_comp,
    crossPerm_eq_one_of_W _ (W_runMerge a ha), mul_one]

@[simp] theorem runLoop_one (N : ℕ) : runLoop N 1 = 𝟙 _ :=
  conj_eq_id _ ((W_iff_crossPerm_eq_one (dimSum_replicate N) _).mpr
    (crossPerm_onesTopEquiv_symm N 1))

/-- The loop the `k`-th atom becomes once the merges are inverted. -/
noncomputable def atomLoop (N : ℕ) (k : Fin (N - 1)) : RunEnd N :=
  conj (dimSum_replicate N) (atomOnes N k)

theorem runLoop_adjT (N : ℕ) (k : Fin (N - 1)) : runLoop N (adjT k) = atomLoop N k := by
  rw [atomLoop, conj_eq_runLoop, crossPerm_atomOnes]

/-- **The atom's loop is its own two legs** — the crossing leg, then the merge leg inverted. -/
theorem atomLoop_eq_legs (N : ℕ) (k : Fin (N - 1)) :
    atomLoop N k = @inv _ _ _ _ _ (isIso_Q_op_of_W (W_mergeOnes N k))
      ≫ (Qz).map (atomOnes N k).op :=
  conj_ones (dimSum_atomComp N k) (atomOnes N k)

/-- **Composing two loops multiplies their crossings**, once the second ascends across its cut —
the `k`-th atom's cell above the one-bead refinement supplies the leg that does it. -/
theorem runLoop_comp {N : ℕ} {β : Perm (Fin N)} {k : Fin (N - 1)}
    (h : β (adjLo k) < β (adjHi k)) :
    runLoop N β ≫ runLoop N (adjT k) = runLoop N (β * adjT k) := by
  obtain ⟨m, hm⟩ := exists_W_to_top (a := zObj (atomComp N k)) (dimSum_atomComp N k)
  obtain ⟨w, hmw, hcross⟩ := exists_atom_step (d := zObj (topDims N)) (k := k) ⟨m⟩
    (crossPerm_onesTopEquiv_symm N β) h
  have hleg : conj (dimSum_atomComp N k) w = runLoop N β := by
    rw [← conj_W_comp (dimSum_replicate N) (W_mergeOnes N k) w, hmw]
    rfl
  refine Eq.trans (congrArg (fun t => runLoop N β ≫ t) (runLoop_adjT N k)) (Eq.symm ?_)
  rw [runLoop, conj_congr (dimSum_replicate N)
      (f := (onesTopEquiv N).symm (β * adjT k)) (f' := atomOnes N k ≫ w)
      ((crossPerm_onesTopEquiv_symm N _).trans hcross.symm),
    conj_comp, hleg]
  rfl

/-- **The atoms generate**: a loop at the run is the word its crossing permutation spells, one
atom per inversion. -/
theorem exists_atomWord : ∀ (N : ℕ) (σ : Perm (Fin N)),
    ∃ l : List (Fin (N - 1)), l.length = permLen σ ∧
      l.foldl (fun β k => β * adjT k) 1 = σ ∧
      runLoop N σ = l.foldl (fun g k => g ≫ atomLoop N k) (𝟙 _) := by
  intro N
  suffices key : ∀ (n : ℕ) (σ : Perm (Fin N)), permLen σ ≤ n →
      ∃ l : List (Fin (N - 1)), l.length = permLen σ ∧
        l.foldl (fun β k => β * adjT k) 1 = σ ∧
        runLoop N σ = l.foldl (fun g k => g ≫ atomLoop N k) (𝟙 _) from
    fun σ => key (permLen σ) σ le_rfl
  intro n
  induction n with
  | zero =>
      intro σ hσ
      obtain rfl : σ = 1 := eq_one_of_permLen_eq_zero σ (Nat.le_zero.mp hσ)
      exact ⟨[], by simp [permLen_one], rfl, by simp⟩
  | succ n ih =>
      intro σ hσ
      rcases Nat.eq_zero_or_pos (permLen σ) with h0 | hpos
      · exact ih σ (by omega)
      obtain ⟨i, hdesc⟩ := exists_adjacent_descent σ hpos
      have hlen : permLen σ = permLen (σ * adjT i) + 1 := permLen_mul_adjT_of_descent hdesc
      obtain ⟨l, hl, hβ, hloop⟩ := ih (σ * adjT i) (by omega)
      refine ⟨l ++ [i], by simp [hl, hlen], ?_, ?_⟩
      · rw [List.foldl_append, hβ]
        simpa using mul_adjT_adjT σ i
      · have hasc : (σ * adjT i) (adjLo i) < (σ * adjT i) (adjHi i) := adjT_ascent_of_descent hdesc
        rw [List.foldl_append, ← hloop]
        change runLoop N σ = runLoop N (σ * adjT i) ≫ atomLoop N i
        rw [← runLoop_adjT N i, runLoop_comp hasc, mul_adjT_adjT]

/-- **Every refinement is a word in the atoms**, conjugated by the merges into its two ends — one
letter per crossing. -/
theorem exists_atomWord_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    ∃ l : List (Fin (N - 1)), l.length = permLen (crossPerm ha f) ∧
      conj ha f = l.foldl (fun g k => g ≫ atomLoop N k) (𝟙 _) := by
  obtain ⟨l, hl, -, hloop⟩ := exists_atomWord N (crossPerm ha f)
  exact ⟨l, hl, (conj_eq_runLoop ha f).trans hloop⟩

/-! ## The Artin relations

A loop appends an atom across an ascent (`runLoop_comp`), which is all `isArtinFamily_of_atom`
asks: the atoms satisfy Artin's relation at every pair, and read at the two exponents
(`isArtinFamily_iff`) that is commutation and the braid relation. -/

section Relations

variable {N : ℕ} {i j : Fin (N - 1)}

/-- **The atoms out of a run are an Artin family**, loops composing in the opposite monoid. -/
theorem isArtinFamily_atomLoop (N : ℕ) :
    IsArtinFamily fun k : Fin (N - 1) => MulOpposite.op (atomLoop N k) := by
  have h := isArtinFamily_of_atom (g := fun σ : Perm (Fin N) => MulOpposite.op (runLoop N σ))
    fun _ _ ha => congrArg MulOpposite.op (runLoop_comp ha)
  simpa only [runLoop_adjT] using h

theorem atomLoop_comm (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomLoop N i ≫ atomLoop N j = atomLoop N j ≫ atomLoop N i := by
  have h := isArtinFamily_iff.mp (isArtinFamily_atomLoop N) (.comm i j hij)
  simp only [map_mul, FreeMonoid.lift_eval_of] at h
  exact congrArg MulOpposite.unop h

/-- **One bead cut in three braids** — the hexagon of the cell two adjacent cuts share. -/
theorem atomLoop_braid (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomLoop N i ≫ atomLoop N j ≫ atomLoop N i
      = atomLoop N j ≫ atomLoop N i ≫ atomLoop N j := by
  have h := isArtinFamily_iff.mp (isArtinFamily_atomLoop N) (.braid i j hij)
  simp only [map_mul, FreeMonoid.lift_eval_of] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg MulOpposite.unop h).trans (Category.assoc _ _ _))

/-- **The codimension-two dichotomy.**  A codimension-two refinement out of the run is entered by
*exactly two* atoms (`exists_atomPair_of_codim_two`), and those two satisfy the Artin relation of
their species: a hexagon when their cuts share a bead, a square when they do not.  The presentation
is cut by the two families `atomLoop_comm`/`atomLoop_braid`, not by one relation per `f` — most of
those would be `w = w`. -/
theorem artin_of_codim_two {d : Ch Zbp} (f : zObj (𝟙^N) ⟶ d) (hcod : codim f = 2) :
    ∃ i j : Fin (N - 1), (i : ℕ) < (j : ℕ) ∧
      (∀ k : Fin (N - 1), Nonempty (zObj (atomComp N k) ⟶ d) ↔ (k = i ∨ k = j)) ∧
      (((j : ℕ) = (i : ℕ) + 1 ∧
          atomLoop N i ≫ atomLoop N j ≫ atomLoop N i
            = atomLoop N j ≫ atomLoop N i ≫ atomLoop N j)
        ∨ ((i : ℕ) + 1 < (j : ℕ) ∧
          atomLoop N i ≫ atomLoop N j = atomLoop N j ≫ atomLoop N i)) := by
  obtain ⟨i, j, hij, hcount⟩ := exists_atomPair_of_codim_two f hcod
  refine ⟨i, j, hij, hcount, ?_⟩
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hgap | hadj
  · exact Or.inr ⟨hgap, atomLoop_comm hgap⟩
  · have hj : (j : ℕ) = (i : ℕ) + 1 := by omega
    exact Or.inl ⟨hj, atomLoop_braid hj⟩

end Relations

end ChainCat
