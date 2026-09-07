import CubeChains.Concurrency.Grading.TopBead
import CubeChains.Concurrency.Presentation.CutPresentation
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Concurrency/Presentation/LocPresentation — the atoms out of a run, and the cells they meet in

The codimension-one refinements out of the run on `N` events are the merge and the atom at each
cut (`eq_mergeOnes_or_atomOnes`, `Cut.exists_eq_atom`): `N-1` coordinate flips.

The codimension-two cell two atoms share (`exists_pairCell`) closes a square when their cuts are
disjoint (`atomLoop_comm`) and a hexagon when the cuts share a bead (`atomLoop_braid`) — the second
leg of each being the other atom, since a leg is pinned by its crossing permutation (`exists_leg`).
-/

open CategoryTheory Equiv Opposite BPSet CubeChains CubeChain

namespace ChainCat

/-! ## The atoms

Above a run, a codimension-one cell merges two adjacent events into one bead; the crossing leg is
the *other* staircase of that square, and it swaps them (`atomOnes`). -/
theorem W_eqToHom {a b : Ch Zbp} (h : a = b) : W Zbp (eqToHom h) := by
  cases h; exact (W Zbp).id_mem _

theorem not_W_atomOnes (N : ℕ) (k : Fin (N - 1)) : ¬ W Zbp (atomOnes N k) := fun h =>
  adjT_ne_one k
    ((crossPerm_atomOnes N k).symm.trans (crossPerm_eq_one_of_W (dimSum_replicate N) h))

/-- **The merge from the run on `N` events** — every chain on `N` events is entered from it, in
exactly one crossing-free way. -/
noncomputable def runMerge {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) : zObj (𝟙^N) ⟶ b :=
  (exists_W_from_ones b hb).choose

theorem W_runMerge {N : ℕ} (b : Ch Zbp) (hb : dimSum b.dims = N) : W Zbp (runMerge b hb) :=
  (exists_W_from_ones b hb).choose_spec

/-- **A merge out of the run is the only one** — `eq_of_W` pins it by its endpoints, so any merge
from the run rewrites to `runMerge` in one step. -/
theorem eq_runMerge {N : ℕ} {b : Ch Zbp} (hb : dimSum b.dims = N) {f : zObj (𝟙^N) ⟶ b}
    (hf : W Zbp f) : f = runMerge b hb :=
  eq_of_W hf (W_runMerge b hb)

/-- **Merges out of the run reach every shape uniquely** — the statement the Garside height rests
on, and the reason `runMerge`'s choice is no choice at all. -/
theorem existsUnique_W_ones {N : ℕ} {b : Ch Zbp} (hb : dimSum b.dims = N) :
    ∃! f : zObj (𝟙^N) ⟶ b, W Zbp f :=
  ⟨runMerge b hb, W_runMerge b hb, fun _ hf => eq_runMerge hb hf⟩

/-- The merge that runs alongside the `k`-th atom. -/
noncomputable def mergeOnes (N : ℕ) (k : Fin (N - 1)) :
    zObj (𝟙^N) ⟶ zObj (atomComp N k) :=
  runMerge (zObj (atomComp N k)) (dimSum_atomComp N k)

theorem W_mergeOnes (N : ℕ) (k : Fin (N - 1)) : W Zbp (mergeOnes N k) :=
  W_runMerge _ _
/-- The merge of an atom cell into one bead. -/
noncomputable def topOnes (N : ℕ) (k : Fin (N - 1)) :
    zObj (atomComp N k) ⟶ zObj [atomTop N k] :=
  (exists_crossPerm_eq_one (dimSum_atomComp N k)
    (nonempty_hom_single (m := atomTop N k) ((dimSum_atomComp N k).trans
      (atomTop_coe N k).symm))).choose

theorem crossPerm_topOnes (N : ℕ) (k : Fin (N - 1)) :
    crossPerm (dimSum_atomComp N k) (topOnes N k) = 1 :=
  (exists_crossPerm_eq_one (dimSum_atomComp N k)
    (nonempty_hom_single (m := atomTop N k) ((dimSum_atomComp N k).trans
      (atomTop_coe N k).symm))).choose_spec

/-- **Out of a run, a codimension-one refinement is the merge or the atom.**  Its crossing
permutation either ascends across the cut, and then it factors the arrow into one bead exactly as
the merge does, or it descends, and then as the atom does — `factor_ext` in both cases. -/
theorem eq_mergeOnes_or_atomOnes {N : ℕ} (k : Fin (N - 1))
    (u : zObj (𝟙^N) ⟶ zObj (atomComp N k)) : u = mergeOnes N k ∨ u = atomOnes N k := by
  have hprod : ∀ (h : zObj (𝟙^N) ⟶ zObj (atomComp N k)) (v : zObj (atomComp N k) ⟶
      zObj [atomTop N k]), crossPerm (dimSum_replicate N) (h ≫ v)
        = crossPerm (dimSum_atomComp N k) v * crossPerm (dimSum_replicate N) h :=
    fun h v => crossPerm_comp (dimSum_replicate N) h v
  have hne : crossPerm (dimSum_replicate N) u (adjHi k) ≠
      crossPerm (dimSum_replicate N) u (adjLo k) := fun hc =>
    absurd ((crossPerm (dimSum_replicate N) u).injective hc)
      (Fin.ne_of_val_ne (by rw [adjHi_val, adjLo_val]; omega))
  by_cases hasc : crossPerm (dimSum_replicate N) u (adjLo k)
      < crossPerm (dimSum_replicate N) u (adjHi k)
  · left
    obtain ⟨v, hv⟩ := exists_crossPerm_single (dimSum_atomComp N k) (m := atomTop N k)
      (atomTop_coe N k) (τ := crossPerm (dimSum_replicate N) u)
      fun x y hxy hlt => by
        obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy hlt
        exact hasc
    have heq : mergeOnes N k ≫ v = u ≫ topOnes N k :=
      hom_ext_of_crossPerm (h := dimSum_replicate N) (by
        rw [hprod, hprod, hv, crossPerm_topOnes,
          crossPerm_eq_one_of_W (dimSum_replicate N) (W_mergeOnes N k), one_mul, mul_one])
    exact (factor_ext rfl heq).1
  · right
    obtain ⟨v, hv⟩ := exists_crossPerm_single (dimSum_atomComp N k) (m := atomTop N k)
      (atomTop_coe N k) (τ := crossPerm (dimSum_replicate N) u * adjT k)
      fun x y hxy hlt => by
        obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy hlt
        simp only [Perm.mul_apply, adjT_lo, adjT_hi]
        omega
    have heq : atomOnes N k ≫ v = u ≫ topOnes N k :=
      hom_ext_of_crossPerm (h := dimSum_replicate N) (by
        rw [hprod, hprod, hv, crossPerm_topOnes, crossPerm_atomOnes, one_mul, mul_adjT_adjT])
    exact (factor_ext rfl heq).1


/-- **A codimension-one non-merge out of a run is one of its atoms.**  The cut splits the run into
`𝟙ⁱ 1 1 𝟙ʲ`, so the target is `𝟙ⁱ 2 𝟙ʲ`, and out of a run there is nothing there but the merge and
the atom. -/
theorem exists_eq_atomOnes {N : ℕ} {c : Ch Zbp} (f : zObj (𝟙^N) ⟶ c) (hcod : codim f = 1)
    (hnot : ¬ W Zbp f) :
    ∃ (k : Fin (N - 1)) (h : c = zObj (atomComp N k)), f ≫ eqToHom h = atomOnes N k := by
  obtain ⟨l, r, p, q, hcell, hones⟩ := (codim_eq_one_iff f).mp hcod
  have hones' : (𝟙^N : List ℕ+) = l ++ p :: q :: r := hones
  have hall : ∀ c ∈ l ++ p :: q :: r, c = (1 : ℕ+) := fun c hc =>
    List.eq_of_mem_replicate (by rw [hones']; exact hc)
  have hp : p = 1 := hall p (by simp)
  have hq : q = 1 := hall q (by simp)
  have hl : l = 𝟙^(l.length) := List.eq_replicate_of_mem fun c hc => hall c (by simp [hc])
  have hr : r = 𝟙^(r.length) := List.eq_replicate_of_mem fun c hc => hall c (by simp [hc])
  have hlen : l.length + 2 + r.length = N := by
    have h := congrArg List.length hones'
    simp only [List.length_replicate, List.length_append, List.length_cons] at h
    omega
  have hklt : l.length < N - 1 := by omega
  have hcell' : c.dims = atomComp N ⟨l.length, hklt⟩ := by
    rw [hcell, hp, hq, atomComp,
      show N - 2 - ((⟨l.length, hklt⟩ : Fin (N - 1)) : ℕ) = r.length by simp; omega, ← hl, ← hr]
    rfl
  obtain rfl : c = zObj (atomComp N ⟨l.length, hklt⟩) := Obj.eq_of_dims hcell'
  refine ⟨⟨l.length, hklt⟩, rfl, (Category.comp_id _).trans ?_⟩
  rcases eq_mergeOnes_or_atomOnes ⟨l.length, hklt⟩ f with h | h
  · exact absurd (h ▸ W_mergeOnes N ⟨l.length, hklt⟩) hnot
  · exact h

/-- **A generator out of the run that is not a merge is one of its `N-1` atoms** — and distinct
indices name distinct cells (`atomComp_ne`). -/
theorem Cut.exists_eq_atom {N : ℕ} {x : GenObj Cut.Refine} (e : x ⟶ Cut.vert (zObj (𝟙^N)))
    (he : ¬ W Zbp (Cut.genHom e)) :
    ∃ (k : Fin (N - 1)) (h : x.as = zObj (atomComp N k)),
      Cut.genHom e ≫ eqToHom h = atomOnes N k :=
  exists_eq_atomOnes (Cut.genHom e) (Cut.codim_genHom e) he

/-! ## The codimension-two cell of two atoms -/

theorem codim_mergeOnes (N : ℕ) (k : Fin (N - 1)) : codim (mergeOnes N k) = 1 := by
  rw [codim, degree_atomComp, degree_ones]

/-- **Distinct atoms cut distinct cells** — a cell above the run carries exactly one atom. -/
theorem atomComp_ne {N : ℕ} {i j : Fin (N - 1)} (hij : (i : ℕ) ≠ (j : ℕ)) :
    zObj (atomComp N i) ≠ zObj (atomComp N j) := by
  intro hc
  have hcross : crossPerm (dimSum_replicate N) (atomOnes N i ≫ eqToHom hc) = adjT i := by
    rw [crossPerm_comp, crossPerm_eq_one_of_W _ (W_eqToHom hc), one_mul, crossPerm_atomOnes]
  rcases eq_mergeOnes_or_atomOnes j (atomOnes N i ≫ eqToHom hc) with h | h
  · refine adjT_ne_one i (hcross.symm.trans ?_)
    rw [h]
    exact crossPerm_eq_one_of_W _ (W_mergeOnes N j)
  · refine hij (adjT_inj (hcross.symm.trans ?_))
    rw [h]
    exact crossPerm_atomOnes N j

theorem exists_W_top {N : ℕ} {b : Ch Zbp} (hb : dimSum b.dims = N) :
    ∃ m : b ⟶ zObj (topDims N), W Zbp m := by
  obtain ⟨m, hm⟩ := exists_crossPerm_eq_one hb
    ((nonempty_hom_top b.dims hb).map fun v =>
      eqToHom (Obj.eq_of_dims (a := b) (b := zObj b.dims) rfl) ≫ v)
  exact ⟨m, (W_iff_crossPerm_eq_one _ m).mpr hm⟩

/-- **Two distinct atoms lie under one codimension-two cell** — their two one-cut steps out of the
run both sit under the coarsest chain, so they close a diamond (`exists_diamond`). -/
theorem exists_pairCell {N : ℕ} (i j : Fin (N - 1)) (hij : (i : ℕ) ≠ (j : ℕ)) :
    ∃ d : Ch Zbp, dimSum d.dims = N ∧ degree d = 2 ∧
      Nonempty (zObj (atomComp N i) ⟶ d) ∧ Nonempty (zObj (atomComp N j) ⟶ d) := by
  obtain ⟨mi, hmi⟩ := exists_W_top (b := zObj (atomComp N i)) (dimSum_atomComp N i)
  obtain ⟨mj, hmj⟩ := exists_W_top (b := zObj (atomComp N j)) (dimSum_atomComp N j)
  have hsq : mergeOnes N i ≫ mi = mergeOnes N j ≫ mj :=
    eq_of_W ((W Zbp).comp_mem _ _ (W_mergeOnes N i) hmi)
      ((W Zbp).comp_mem _ _ (W_mergeOnes N j) hmj)
  obtain ⟨d, u, u', -, hu, -, -, -, -⟩ := exists_diamond
    (codim_mergeOnes N i) (codim_mergeOnes N j) hsq (atomComp_ne hij)
  refine ⟨d, (strandsEq u).symm.trans (dimSum_atomComp N i), ?_, ⟨u⟩, ⟨u'⟩⟩
  have h1 := degree_le_of_hom u
  rw [codim, degree_atomComp] at hu
  rw [degree_atomComp] at h1
  omega
/-! ## Legs out of an atom's cell -/

/-- **A leg out of an atom's cell, with a prescribed crossing permutation** — realised at both
extremes, hence in the middle (`exists_crossPerm_mid`). -/
theorem exists_leg {N : ℕ} (k : Fin (N - 1)) {d : Ch Zbp} (hd : dimSum d.dims = N)
    (hnk : Nonempty (zObj (atomComp N k) ⟶ d)) {σ : Perm (Fin N)}
    (hasc : σ (adjLo k) < σ (adjHi k))
    {u : zObj (𝟙^N) ⟶ d} (hu : crossPerm (dimSum_replicate N) u = σ) :
    ∃ w : zObj (atomComp N k) ⟶ d, crossPerm (dimSum_atomComp N k) w = σ := by
  obtain ⟨g, hg⟩ := exists_crossPerm_single (dimSum_atomComp N k) (m := atomTop N k)
    (atomTop_coe N k) fun x y hxy hlt => by
      obtain ⟨rfl, rfl⟩ := eq_adj_of_index_eq N k hxy hlt
      exact hasc
  obtain ⟨s, hs⟩ := exists_crossPerm_eq_one hd
    ((nonempty_hom_single (m := atomTop N k) (hd.trans (atomTop_coe N k).symm)).map
      fun v => eqToHom (Obj.eq_of_dims (b := zObj d.dims) rfl) ≫ v)
  exact exists_crossPerm_mid
    (crossPerm_eq_one_of_W (dimSum_replicate N) (W_mergeOnes N k)) hs hnk hu hg

/-- **One crossing step**: a leg out of the run that ascends across the `k`-th cut factors through
the `k`-th merge, and crossing instead lengthens it by that atom. -/
theorem exists_atom_step {N : ℕ} {d : Ch Zbp} (hd : dimSum d.dims = N) (k : Fin (N - 1))
    (hnk : Nonempty (zObj (atomComp N k) ⟶ d)) {t : zObj (𝟙^N) ⟶ d} {σ : Perm (Fin N)}
    (hσ : crossPerm (dimSum_replicate N) t = σ) (hasc : σ (adjLo k) < σ (adjHi k)) :
    ∃ w : zObj (atomComp N k) ⟶ d, mergeOnes N k ≫ w = t ∧
      crossPerm (dimSum_replicate N) (atomOnes N k ≫ w) = σ * adjT k := by
  obtain ⟨w, hw⟩ := exists_leg k hd hnk hasc hσ
  refine ⟨w, hom_ext_of_crossPerm (h := dimSum_replicate N) (by
    rw [crossPerm_comp, hw, crossPerm_eq_one_of_W _ (W_mergeOnes N k), mul_one]
    exact hσ.symm), ?_⟩
  rw [crossPerm_comp, hw]
  exact congrArg (fun p => σ * p) (crossPerm_atomOnes N k)
/-! ## A refinement, conjugated onto a loop at its run

Every chain is merged into from the run on its events, so a refinement is conjugated onto a loop
at that run (`conj`), and the loop sees only the crossing permutation (`conj_congr`). -/

theorem isIso_Q_op_of_W {a b : Ch Zbp} {f : a ⟶ b} (hf : W Zbp f) :
    IsIso (((W Zbp).op).Q.map f.op) := ((W Zbp).op).Q_inverts f.op hf

/-- **A refinement, conjugated onto a loop at the run** it is merged into from. -/
noncomputable def conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) :=
  letI := isIso_Q_op_of_W (W_runMerge b (tgtStrands f ha))
  inv (((W Zbp).op).Q.map (runMerge b (tgtStrands f ha)).op)
    ≫ ((W Zbp).op).Q.map f.op ≫ ((W Zbp).op).Q.map (runMerge a ha).op

theorem conj_comp {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) (g : b ⟶ c) :
    conj ha (f ≫ g) = conj (tgtStrands f ha) g ≫ conj ha f := by
  haveI := isIso_Q_op_of_W (W_runMerge b (tgtStrands f ha))
  haveI := isIso_Q_op_of_W (W_runMerge c (tgtStrands g (tgtStrands f ha)))
  simp only [conj, Category.assoc, IsIso.hom_inv_id_assoc]
  rw [show (f ≫ g).op = g.op ≫ f.op from rfl, Functor.map_comp, Category.assoc]

theorem conj_eq_id {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) {f : a ⟶ b} (hf : W Zbp f) :
    conj ha f = 𝟙 _ := by
  haveI := isIso_Q_op_of_W (W_runMerge b (tgtStrands f ha))
  have hrun : runMerge a ha ≫ f = runMerge b (tgtStrands f ha) :=
    eq_of_W ((W Zbp).comp_mem _ _ (W_runMerge a ha) hf) (W_runMerge b (tgtStrands f ha))
  rw [conj, ← Functor.map_comp,
    show f.op ≫ (runMerge a ha).op = (runMerge a ha ≫ f).op from rfl, hrun, IsIso.inv_hom_id]

theorem conj_comp_W {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) {m : b ⟶ c}
    (hm : W Zbp m) : conj ha (f ≫ m) = conj ha f := by
  rw [conj_comp, conj_eq_id _ hm, Category.id_comp]

theorem conj_W_comp {N : ℕ} {a b c : Ch Zbp} (ha : dimSum a.dims = N) {m : a ⟶ b}
    (hm : W Zbp m) (g : b ⟶ c) : conj ha (m ≫ g) = conj (tgtStrands m ha) g := by
  rw [conj_comp, conj_eq_id ha hm, Category.comp_id]

/-- **The conjugated loop sees only the crossing permutation** — merge both targets into one bead,
where a refinement is its crossing permutation. -/
theorem conj_congr {N : ℕ} {a b b' : Ch Zbp} (ha : dimSum a.dims = N) {f : a ⟶ b} {f' : a ⟶ b'}
    (h : crossPerm ha f = crossPerm ha f') : conj ha f = conj ha f' := by
  obtain ⟨m, hm⟩ := exists_W_top (tgtStrands f ha)
  obtain ⟨m', hm'⟩ := exists_W_top (tgtStrands f' ha)
  have hfm : f ≫ m = f' ≫ m' := hom_ext_of_crossPerm (h := ha) (by
    rw [crossPerm_comp ha f m, crossPerm_comp ha f' m',
      crossPerm_eq_one_of_W (tgtStrands f ha) hm,
      crossPerm_eq_one_of_W (tgtStrands f' ha) hm', one_mul, one_mul, h])
  rw [← conj_comp_W ha f hm, ← conj_comp_W ha f' hm', hfm]

/-! ## The Artin relations

The atoms, read as loops at the run.  A codimension-two cell above two of them supplies the second
leg of each, and the two legs are the *other* atom (`conj_eq_of_crossPerm`): far-apart cuts close a
square, adjacent ones a hexagon. -/

/-- The loop the `k`-th atom becomes once the merges are inverted. -/
noncomputable def atomLoop (N : ℕ) (k : Fin (N - 1)) :
    @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) :=
  conj (dimSum_replicate N) (atomOnes N k)

/-- **The atom's loop is its own two legs** — the crossing leg, then the merge leg inverted. -/
theorem atomLoop_eq_legs (N : ℕ) (k : Fin (N - 1)) :
    atomLoop N k = @inv _ _ _ _ _ (isIso_Q_op_of_W (W_mergeOnes N k))
      ≫ ((W Zbp).op).Q.map (atomOnes N k).op := by
  have hrun : runMerge (zObj (𝟙^N)) (dimSum_replicate N) = 𝟙 _ := endo_eq_id _
  rw [atomLoop, conj, hrun, op_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- **A leg out of an atom's cell is a loop at the run** — prefix the merge. -/
theorem conj_leg {N : ℕ} (k : Fin (N - 1)) {d : Ch Zbp} (w : zObj (atomComp N k) ⟶ d) :
    conj (dimSum_atomComp N k) w = conj (dimSum_replicate N) (mergeOnes N k ≫ w) :=
  (conj_W_comp (dimSum_replicate N) (W_mergeOnes N k) w).symm

/-- **A leg conjugates to the word its crossing spells**: crossing one cut more than another leg
appends that cut's atom. -/
theorem conj_eq_of_crossPerm {N : ℕ} {k l : Fin (N - 1)} {d : Ch Zbp}
    {w : zObj (atomComp N k) ⟶ d} {v : zObj (atomComp N l) ⟶ d}
    (h : crossPerm (dimSum_atomComp N k) w = crossPerm (dimSum_atomComp N l) v * adjT l) :
    conj (dimSum_atomComp N k) w = conj (dimSum_atomComp N l) v ≫ atomLoop N l := by
  have hcross : crossPerm (dimSum_replicate N) (mergeOnes N k ≫ w)
      = crossPerm (dimSum_replicate N) (atomOnes N l ≫ v) := by
    rw [crossPerm_comp, crossPerm_comp, crossPerm_eq_one_of_W _ (W_mergeOnes N k),
      crossPerm_atomOnes, mul_one, h]
  rw [conj_leg k w, conj_congr (dimSum_replicate N) hcross, conj_comp]
  rfl

/-- **Two atoms in one cell**: their two-step refinements agree when their crossings do. -/
theorem atom_pair_eq {N : ℕ} {i j : Fin (N - 1)} {d : Ch Zbp}
    {wi : zObj (atomComp N i) ⟶ d} {wj : zObj (atomComp N j) ⟶ d}
    (h : crossPerm (dimSum_atomComp N i) wi * adjT i
        = crossPerm (dimSum_atomComp N j) wj * adjT j) :
    atomOnes N i ≫ wi = atomOnes N j ≫ wj :=
  hom_ext_of_crossPerm (h := dimSum_replicate N) (by
    rw [crossPerm_comp, crossPerm_comp, crossPerm_atomOnes, crossPerm_atomOnes]; exact h)

section Relations

variable {N : ℕ} {i j : Fin (N - 1)}

/-- The merging leg of a cell above the `k`-th atom. -/
theorem exists_merge_leg (k : Fin (N - 1)) {d : Ch Zbp} (h : Nonempty (zObj (atomComp N k) ⟶ d)) :
    ∃ m : zObj (atomComp N k) ⟶ d, W Zbp m ∧
      crossPerm (dimSum_replicate N) (atomOnes N k ≫ m) = adjT k := by
  obtain ⟨m, hm⟩ := exists_crossPerm_eq_one (dimSum_atomComp N k) h
  exact ⟨m, (W_iff_crossPerm_eq_one _ m).mpr hm, by
    rw [crossPerm_comp, hm, crossPerm_atomOnes, one_mul]⟩

/-- **A leg that crosses only the other atom conjugates to that atom's loop** — the merging leg
`m` fixes the comparison, and a merge conjugates to the identity. -/
theorem conj_eq_atomLoop {k l : Fin (N - 1)} {d : Ch Zbp} {w : zObj (atomComp N k) ⟶ d}
    {m : zObj (atomComp N l) ⟶ d} (hw : crossPerm (dimSum_atomComp N k) w = adjT l)
    (hm : W Zbp m) : conj (dimSum_atomComp N k) w = atomLoop N l := by
  rw [conj_eq_of_crossPerm (v := m) (by rw [hw, crossPerm_eq_one_of_W _ hm, one_mul]),
    conj_eq_id _ hm, Category.id_comp]

/-- **A cell entered by two atoms identifies the words its two legs spell**: the two-step
refinements agree (`atom_pair_eq`) and `conj` is contravariant, so the loops compose the same way.
Both Artin relations are this at their own pair of legs. -/
theorem atomLoop_eq_of_legs {d : Ch Zbp} {wi : zObj (atomComp N i) ⟶ d}
    {wj : zObj (atomComp N j) ⟶ d}
    {u v : @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N))))}
    (h : crossPerm (dimSum_atomComp N i) wi * adjT i
        = crossPerm (dimSum_atomComp N j) wj * adjT j)
    (hi : conj (dimSum_atomComp N i) wi = u) (hj : conj (dimSum_atomComp N j) wj = v) :
    u ≫ atomLoop N i = v ≫ atomLoop N j := by
  have hconj := congrArg (conj (dimSum_replicate N)) (atom_pair_eq h)
  rwa [conj_comp, conj_comp, hi, hj] at hconj

theorem atomLoop_comm (hij : (i : ℕ) + 1 < (j : ℕ)) :
    atomLoop N i ≫ atomLoop N j = atomLoop N j ≫ atomLoop N i := by
  obtain ⟨d, hd, -, hni, hnj⟩ := exists_pairCell i j (by omega)
  obtain ⟨mi, hWmi, hui⟩ := exists_merge_leg i hni
  obtain ⟨mj, hWmj, huj⟩ := exists_merge_leg j hnj
  obtain ⟨wj, hwj⟩ := exists_leg j hd hnj (σ := adjT i)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) hui
  obtain ⟨wi, hwi⟩ := exists_leg i hd hni (σ := adjT j)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) huj
  exact (atomLoop_eq_of_legs (by rw [hwi, hwj]; exact (adjT_comm i j hij).symm)
    (conj_eq_atomLoop hwi hWmj) (conj_eq_atomLoop hwj hWmi)).symm

/-- **One bead cut in three braids** — the hexagon of the cell two adjacent cuts share. -/
theorem atomLoop_braid (hij : (j : ℕ) = (i : ℕ) + 1) :
    atomLoop N i ≫ atomLoop N j ≫ atomLoop N i
      = atomLoop N j ≫ atomLoop N i ≫ atomLoop N j := by
  obtain ⟨d, hd, -, hni, hnj⟩ := exists_pairCell i j (by omega)
  obtain ⟨mi, hWmi, hui⟩ := exists_merge_leg i hni
  obtain ⟨mj, hWmj, huj⟩ := exists_merge_leg j hnj
  obtain ⟨wj₁, hwj₁⟩ := exists_leg j hd hnj (σ := adjT i)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) hui
  obtain ⟨wi₁, hwi₁⟩ := exists_leg i hd hni (σ := adjT j)
    (by rw [Fin.lt_def]; simp only [adjT_val, adjLo_val, adjHi_val]; split_ifs <;> omega) huj
  obtain ⟨wi₂, hwi₂⟩ := exists_leg i hd hni (σ := adjT i * adjT j)
    (by rw [Fin.lt_def]
        simp only [Equiv.Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
        split_ifs <;> omega)
    (u := atomOnes N j ≫ wj₁) (by rw [crossPerm_comp, hwj₁, crossPerm_atomOnes])
  obtain ⟨wj₂, hwj₂⟩ := exists_leg j hd hnj (σ := adjT j * adjT i)
    (by rw [Fin.lt_def]
        simp only [Equiv.Perm.mul_apply, adjT_val, adjLo_val, adjHi_val]
        split_ifs <;> omega)
    (u := atomOnes N i ≫ wi₁) (by rw [crossPerm_comp, hwi₁, crossPerm_atomOnes])
  have hi : conj (dimSum_atomComp N i) wi₂ = atomLoop N i ≫ atomLoop N j := by
    rw [conj_eq_of_crossPerm (v := wj₁) (l := j) (by rw [hwi₂, hwj₁]),
      conj_eq_atomLoop hwj₁ hWmi]
  have hj : conj (dimSum_atomComp N j) wj₂ = atomLoop N j ≫ atomLoop N i := by
    rw [conj_eq_of_crossPerm (v := wi₁) (l := i) (by rw [hwj₂, hwi₁]),
      conj_eq_atomLoop hwi₁ hWmj]
  have hkey := atomLoop_eq_of_legs (by rw [hwi₂, hwj₂]; exact adjT_braid i j hij) hi hj
  rwa [Category.assoc, Category.assoc] at hkey

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

/-! ## The atoms generate

A loop at the run sees only a crossing permutation (`conj_eq_runLoop`), and a permutation is a
product of adjacent transpositions across ascents — so a loop is the word its crossing spells,
one atom per inversion.

The atoms are loops only *after* the merges are inverted: in `Ch Zbp` itself every endomorphism of
a chain is the identity (`endo_eq_id`), so there is nothing at `1ᴺ` for them to generate until
`conj` puts them there. -/

/-- The loop at the run of the one-bead refinement whose crossing is `σ`. -/
noncomputable def runLoop (N : ℕ) (σ : Perm (Fin N)) :
    @End (((W Zbp).op).Localization) _ (((W Zbp).op).Q.obj (op (zObj (𝟙^N)))) :=
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

/-- **Appending an atom across an ascent** — the `k`-th atom's cell above the one-bead refinement
supplies the leg that does it. -/
theorem runLoop_mul_adjT {N : ℕ} {β : Perm (Fin N)} {k : Fin (N - 1)}
    (h : β (adjLo k) < β (adjHi k)) :
    runLoop N (β * adjT k) = runLoop N β ≫ atomLoop N k := by
  obtain ⟨m, hm⟩ := exists_W_top (b := zObj (atomComp N k)) (dimSum_atomComp N k)
  obtain ⟨w, hmw, hcross⟩ := exists_atom_step (d := zObj (topDims N)) (dimSum_topDims N) k ⟨m⟩
    (crossPerm_onesTopEquiv_symm N β) h
  have hleg : conj (dimSum_atomComp N k) w = runLoop N β := by
    rw [← conj_W_comp (dimSum_replicate N) (W_mergeOnes N k) w, hmw]
    rfl
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
        rw [← runLoop_mul_adjT hasc, mul_adjT_adjT]

/-- **Every refinement is a word in the atoms**, conjugated by the merges into its two ends — one
letter per crossing. -/
theorem exists_atomWord_conj {N : ℕ} {a b : Ch Zbp} (ha : dimSum a.dims = N) (f : a ⟶ b) :
    ∃ l : List (Fin (N - 1)), l.length = permLen (crossPerm ha f) ∧
      conj ha f = l.foldl (fun g k => g ≫ atomLoop N k) (𝟙 _) := by
  obtain ⟨l, hl, -, hloop⟩ := exists_atomWord N (crossPerm ha f)
  exact ⟨l, hl, (conj_eq_runLoop ha f).trans hloop⟩

end ChainCat
