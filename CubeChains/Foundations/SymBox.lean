import CubeChains.Foundations.SortPerm
import CubeChains.Foundations.BoxMonoidal
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.CategoryTheory.Endomorphism

/-!
# Foundations/SymBox

The **symmetric box category** `SBox`: the objects of `Box`, but a morphism `▪m ⟶ ▪n` is a
`coord : Fin n → Bool ⊕ Fin m` — each target coordinate fixed to a sign or carrying one free
direction of the source, i.e. an injection `Fin m ↪ Fin n` plus a sign off its image.  So `≫` is
Kleisli composition for `Bool ⊕ -` and needs no combinatorics; `pos` is the injection, determined
by `coord` (`SHom.ext`).

`J : Box ⥤ SBox` is the wide subcategory of *monotone* injections; sorting an injection gives the
unique factorization `sHomEquiv : (▪m ⟶ ▪n) ≃ Perm (Fin m) × (▫m ⟶ ▫n)`.
-/

open CategoryTheory StdCube

namespace StdCube

/-! ## Sign vectors as coordinate assignments

`cellCoord c` is the `Bool ⊕ Fin n`-valued reading of a sign vector `c : Cell N n`; it turns
substitution into `Sum.elim` (`cellCoord_subst`), which is what makes `J` functorial. -/

variable {N n k : ℕ}

/-- A sign vector read coordinatewise: a fixed coordinate reports its sign, a free one reports
its index among the free coordinates. -/
def cellCoord (c : Cell N n) (j : Fin N) : Bool ⊕ Fin n :=
  if h : c.val j = none then Sum.inr (nonesIdx c j (mem_noneSet.mpr h))
  else Sum.inl ((c.val j).get (Option.isSome_iff_ne_none.mpr h))

theorem cellCoord_eq_inl_iff (c : Cell N n) (j : Fin N) (b : Bool) :
    cellCoord c j = Sum.inl b ↔ c.val j = some b := by
  unfold cellCoord
  by_cases h : c.val j = none
  · rw [dif_pos h, h]; simp
  · rw [dif_neg h, Sum.inl.injEq]
    exact ⟨fun hb => hb ▸ (Option.some_get _).symm, fun hb => Option.get_of_eq_some _ hb⟩

theorem cellCoord_eq_inr_iff (c : Cell N n) (j : Fin N) (i : Fin n) :
    cellCoord c j = Sum.inr i ↔ j = nones c i := by
  constructor
  · intro hj
    unfold cellCoord at hj
    by_cases h : c.val j = none
    · rw [dif_pos h, Sum.inr.injEq] at hj
      rw [← hj, nones_nonesIdx]
    · rw [dif_neg h] at hj; exact absurd hj (by simp)
  · rintro rfl
    unfold cellCoord
    rw [dif_pos (val_nones c i), nonesIdx_nones]

/-- A sign vector is determined by its coordinate reading. -/
theorem cell_ext_cellCoord {c d : Cell N n} (h : ∀ j, cellCoord c j = cellCoord d j) : c = d :=
  Subtype.ext <| funext fun j => Option.ext fun b => by
    rw [← cellCoord_eq_inl_iff, ← cellCoord_eq_inl_iff, h j]

@[simp] theorem cellCoord_topCell (N : ℕ) (j : Fin N) : cellCoord (topCell N) j = Sum.inr j :=
  (cellCoord_eq_inr_iff _ _ _).2 (nones_topCell N j).symm

/-- Substitution of sign vectors is `Sum.elim` on coordinate readings. -/
theorem cellCoord_subst (c : Cell N n) (a : Cell n k) (j : Fin N) :
    cellCoord (subst c a) j = (cellCoord c j).elim Sum.inl (cellCoord a) := by
  rcases hc : c.val j with _ | b
  · have hji : j = nones c (nonesIdx c j (mem_noneSet.mpr hc)) := (nones_nonesIdx c j _).symm
    rw [(cellCoord_eq_inr_iff c j _).2 hji]
    change cellCoord (subst c a) j = cellCoord a (nonesIdx c j (mem_noneSet.mpr hc))
    rcases ha : a.val (nonesIdx c j (mem_noneSet.mpr hc)) with _ | b
    · rw [(cellCoord_eq_inr_iff a _ _).2 (nones_nonesIdx a _ (mem_noneSet.mpr ha)).symm]
      refine (cellCoord_eq_inr_iff _ _ _).2 ?_
      rw [nones_subst, nones_nonesIdx]
      exact hji
    · rw [(cellCoord_eq_inl_iff a _ b).2 ha]
      refine (cellCoord_eq_inl_iff _ _ _).2 ?_
      rw [subst_val, substFun_of_none c a hc, ha]
  · rw [(cellCoord_eq_inl_iff c j b).2 hc]
    refine (cellCoord_eq_inl_iff _ _ _).2 ?_
    rw [subst_val, substFun_of_some c a (by rw [hc]; simp), hc]

end StdCube

/-! ## The symmetric box category -/

/-- The **symmetric box category**: dimensions again, but a morphism may permute coordinates. -/
structure SBox where
  /-- The dimension of this object. -/
  dim : ℕ
  deriving DecidableEq

namespace SBox

/-- The object of dimension `n`. -/
abbrev ob (n : ℕ) : SBox := ⟨n⟩

end SBox

/-- `▪n` — the symmetric site object of dimension `n`, the image of `▫n` under `J`. -/
notation:max "▪" n:max => SBox.ob n

/-- A morphism `▪m ⟶ ▪N`: every target coordinate is either fixed to a sign or carries exactly
one free direction of the source.  `pos` is redundant (`SHom.ext`), carried so that `≫` is
`Sum.elim` on the nose. -/
structure SHom (m N : ℕ) where
  /-- The sign, or the source direction, sitting at each target coordinate. -/
  coord : Fin N → Bool ⊕ Fin m
  /-- The target coordinate each source direction goes to. -/
  pos : Fin m → Fin N
  coord_pos : ∀ i, coord (pos i) = Sum.inr i
  pos_eq : ∀ (i : Fin m) (j : Fin N), coord j = Sum.inr i → j = pos i

namespace SHom

variable {m n p : ℕ}

@[ext] theorem ext : ∀ {f g : SHom m n}, f.coord = g.coord → f = g
  | ⟨_, pf, hf₁, _⟩, ⟨_, _, _, hg₂⟩, h => by
      subst h
      obtain rfl : pf = _ := funext fun i => hg₂ i (pf i) (hf₁ i)
      rfl

instance : DecidableEq (SHom m n) := fun f g =>
  decidable_of_iff (f.coord = g.coord) ⟨ext, fun h => by rw [h]⟩

/-- The identity: every coordinate carries its own direction. -/
protected def id (m : ℕ) : SHom m m where
  coord := Sum.inr
  pos := _root_.id
  coord_pos _ := rfl
  pos_eq _ _ h := Sum.inr.inj h

/-- Composition is Kleisli composition for the monad `Bool ⊕ -`. -/
protected def comp (f : SHom m n) (g : SHom n p) : SHom m p where
  coord k := (g.coord k).elim Sum.inl f.coord
  pos := g.pos ∘ f.pos
  coord_pos i := by simp only [Function.comp_apply, g.coord_pos, Sum.elim_inr, f.coord_pos]
  pos_eq i k h := by
    rcases hk : g.coord k with b | j
    · rw [hk] at h; exact absurd h (by simp)
    · rw [hk, Sum.elim_inr] at h
      exact (g.pos_eq j k hk).trans (congrArg g.pos (f.pos_eq i j h))

/-- `pos` is injective: it is a section of `coord` up to `Sum.inr`. -/
theorem pos_injective (u : SHom m n) : Function.Injective u.pos := by
  intro i i' h
  have hi := u.coord_pos i
  rw [h, u.coord_pos] at hi
  exact (Sum.inr.inj hi).symm

end SHom

instance : Category SBox where
  Hom a b := SHom a.dim b.dim
  id a := SHom.id a.dim
  comp f g := f.comp g
  id_comp f := SHom.ext (funext fun k => by
    change Sum.elim Sum.inl Sum.inr (f.coord k) = f.coord k
    cases f.coord k <;> rfl)
  comp_id _ := SHom.ext rfl
  assoc f g h := SHom.ext (funext fun k => by
    change Sum.elim Sum.inl (fun j => Sum.elim Sum.inl f.coord (g.coord j)) (h.coord k)
      = Sum.elim Sum.inl f.coord (Sum.elim Sum.inl g.coord (h.coord k))
    cases h.coord k <;> rfl)

namespace SBox

variable {a b c : SBox}

instance : DecidableEq (a ⟶ b) := inferInstanceAs (DecidableEq (SHom a.dim b.dim))

@[simp] theorem id_coord (a : SBox) (j : Fin a.dim) : SHom.coord (𝟙 a) j = Sum.inr j := rfl

@[simp] theorem id_pos (a : SBox) (i : Fin a.dim) : SHom.pos (𝟙 a) i = i := rfl

@[simp] theorem comp_coord (f : a ⟶ b) (g : b ⟶ c) (k : Fin c.dim) :
    SHom.coord (f ≫ g) k = (g.coord k).elim Sum.inl f.coord := rfl

@[simp] theorem comp_pos (f : a ⟶ b) (g : b ⟶ c) (i : Fin a.dim) :
    SHom.pos (f ≫ g) i = g.pos (f.pos i) := rfl

end SBox

/-! ## The inclusion `J : Box ⥤ SBox` -/

/-- The `SBox` morphism classified by a sign vector: keep the signs, let each free coordinate
carry its own index. -/
def SHom.ofCell {N n : ℕ} (c : Cell N n) : SHom n N where
  coord := cellCoord c
  pos := nones c
  coord_pos i := (cellCoord_eq_inr_iff c _ i).2 rfl
  pos_eq i j h := (cellCoord_eq_inr_iff c j i).1 h

/-- `Box` sits inside `SBox` as the wide subcategory of *monotone* injections. -/
def J : Box ⥤ SBox where
  obj X := ⟨X.dim⟩
  map f := SHom.ofCell (Box.sign f)
  map_id X := SHom.ext (funext fun j => by
    change cellCoord (Box.sign (𝟙 X)) j = Sum.inr j
    rw [Box.sign_id]; exact cellCoord_topCell _ _)
  map_comp f g := SHom.ext (funext fun j => by
    change cellCoord (Box.sign (f ≫ g)) j = _
    rw [Box.sign_comp]; exact cellCoord_subst _ _ j)

@[simp] theorem J_obj (X : Box) : J.obj X = ⟨X.dim⟩ := rfl

@[simp] theorem J_map_coord {m n : ℕ} (f : ▫m ⟶ ▫n) (j : Fin n) :
    SHom.coord (J.map f) j = cellCoord (Box.sign f) j := rfl

@[simp] theorem J_map_pos {m n : ℕ} (f : ▫m ⟶ ▫n) (i : Fin m) :
    SHom.pos (J.map f) i = faceEmb f i := rfl

instance : J.Faithful where
  map_injective h :=
    Box.hom_ext (cell_ext_cellCoord fun j => congrFun (congrArg SHom.coord h) j)

/-- `J` is a bijection on objects — the two categories are wide subcategory and ambient. -/
def SBox.objEquiv : Box ≃ SBox where
  toFun X := ⟨X.dim⟩
  invFun Y := ⟨Y.dim⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem J_obj_bijective : Function.Bijective J.obj := SBox.objEquiv.bijective

/-! ## The symmetries -/

/-- The symmetry of `▪m` given by `σ`: source direction `i` sits at coordinate `σ i`. -/
def symHom {m : ℕ} (σ : Equiv.Perm (Fin m)) : ▪m ⟶ ▪m where
  coord j := Sum.inr (σ.symm j)
  pos := σ
  coord_pos i := by rw [Equiv.symm_apply_apply]
  pos_eq i j h := by rw [← Sum.inr.inj h, Equiv.apply_symm_apply]

@[simp] theorem symHom_coord {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    SHom.coord (symHom σ) j = Sum.inr (σ.symm j) := rfl

@[simp] theorem symHom_pos {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    SHom.pos (symHom σ) i = σ i := rfl

@[simp] theorem symHom_one (m : ℕ) : symHom (1 : Equiv.Perm (Fin m)) = 𝟙 ▪m := SHom.ext rfl

/-- `pos` composes covariantly, so `≫` multiplies permutations the other way round — which is
exactly mathlib's `End` convention `f * g = g ≫ f`. -/
@[simp] theorem symHom_comp {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    symHom σ ≫ symHom τ = symHom (τ * σ) := SHom.ext rfl

/-- The permutation underlying an endomorphism of `▪n`; its inverse is read off `coord`, so it
stays computable. -/
def endPerm {n : ℕ} (u : ▪n ⟶ ▪n) : Equiv.Perm (Fin n) where
  toFun := u.pos
  invFun j := (u.coord j).elim (fun _ => j) _root_.id
  left_inv i := by simp only [u.coord_pos, Sum.elim_inr, id_eq]
  right_inv j := by
    obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.mp u.pos_injective) j
    simp only [u.coord_pos, Sum.elim_inr, id_eq]

@[simp] theorem endPerm_apply {n : ℕ} (u : ▪n ⟶ ▪n) (i : Fin n) : endPerm u i = u.pos i := rfl

@[simp] theorem endPerm_symHom {n : ℕ} (σ : Equiv.Perm (Fin n)) : endPerm (symHom σ) = σ :=
  Equiv.ext fun _ => rfl

@[simp] theorem symHom_endPerm {n : ℕ} (u : ▪n ⟶ ▪n) : symHom (endPerm u) = u :=
  SHom.ext <| funext fun j => by
    obtain ⟨i, rfl⟩ := (Finite.injective_iff_surjective.mp u.pos_injective) j
    rw [symHom_coord, u.coord_pos]
    exact congrArg Sum.inr ((endPerm u).symm_apply_eq.2 rfl)

/-- **`End ▪n` is the symmetric group** on `Fin n`: every endomorphism only permutes. -/
def endMulEquivPerm (n : ℕ) : End (▪n) ≃* Equiv.Perm (Fin n) where
  toFun := endPerm
  invFun := symHom
  left_inv := symHom_endPerm
  right_inv := endPerm_symHom
  map_mul' _ _ := Equiv.ext fun _ => rfl

/-- **`Aut ▪n` is the symmetric group** on `Fin n` — the units of `End ▪n`. -/
def autMulEquivPerm (n : ℕ) : Aut (▪n) ≃* Equiv.Perm (Fin n) :=
  (Aut.unitsEndEquivAut (▪n)).symm.trans
    ((Units.mapEquiv (endMulEquivPerm n)).trans toUnits.symm)

@[simp] theorem autMulEquivPerm_symm_hom {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((autMulEquivPerm n).symm σ).hom = symHom σ := rfl

/-! ## Unique factorization

```
        symHom σ              J.map φ
   ▪m ─────────────▶ ▪m ─────────────────▶ ▪n
   pos:    σ                faceEmb φ
```
Sorting the injection `u.pos` splits it as the monotone enumeration `nones u.cell` of its image,
precomposed with the sorting permutation `u.perm`. -/

namespace SHom

variable {m n : ℕ}

/-- The sign vector of a `SBox` morphism: forget *which* free direction sits at a free
coordinate, remember only that one does. -/
def cell (u : ▪m ⟶ ▪n) : Cell n m :=
  ⟨fun j => (u.coord j).elim some fun _ => none, by
    have himg : noneSet (fun j => (u.coord j).elim some fun _ => none)
        = Finset.univ.image u.pos := by
      ext j
      rw [mem_noneSet, Finset.mem_image]
      constructor
      · intro hj
        rcases hc : u.coord j with b | i
        · rw [hc] at hj; exact absurd hj (by simp)
        · exact ⟨i, Finset.mem_univ i, (u.pos_eq i j hc).symm⟩
      · rintro ⟨i, -, rfl⟩
        rw [u.coord_pos]; rfl
    rw [himg, Finset.card_image_of_injective _ u.pos_injective, Finset.card_univ,
      Fintype.card_fin]⟩

@[simp] theorem cell_val (u : ▪m ⟶ ▪n) (j : Fin n) :
    (cell u).val j = (u.coord j).elim some fun _ => none := rfl

theorem cell_val_eq_some {u : ▪m ⟶ ▪n} {j : Fin n} {b : Bool} (h : u.coord j = Sum.inl b) :
    (cell u).val j = some b := by simp [h]

theorem cell_val_eq_none {u : ▪m ⟶ ▪n} {j : Fin n} {i : Fin m} (h : u.coord j = Sum.inr i) :
    (cell u).val j = none := by simp [h]

/-- A free coordinate of `u.cell` really does carry a direction. -/
theorem exists_coord_eq_inr {u : ▪m ⟶ ▪n} {j : Fin n} (h : (cell u).val j = none) :
    ∃ i, u.coord j = Sum.inr i := by
  rcases hc : u.coord j with b | i
  · rw [cell_val, hc] at h; exact absurd h (by simp)
  · exact ⟨i, rfl⟩

theorem pos_mem_noneSet (u : ▪m ⟶ ▪n) (i : Fin m) : u.pos i ∈ noneSet (cell u).val := by
  rw [mem_noneSet, cell_val, u.coord_pos]; rfl

/-- The **sorting permutation** of `u`: the order in which `u.pos` visits its image. -/
def perm (u : ▪m ⟶ ▪n) : Equiv.Perm (Fin m) where
  toFun i := nonesIdx (cell u) (u.pos i) (u.pos_mem_noneSet i)
  invFun j := (u.coord (nones (cell u) j)).elim (fun _ => j) _root_.id
  left_inv i := by
    simp only [nones_nonesIdx, u.coord_pos, Sum.elim_inr, id_eq]
  right_inv j := by
    obtain ⟨i, hi⟩ := exists_coord_eq_inr (val_nones (cell u) j)
    simp only [hi, Sum.elim_inr, id_eq]
    refine (nones (cell u)).injective ?_
    rw [nones_nonesIdx]
    exact (u.pos_eq i _ hi).symm

/-- The defining property of the sorting permutation: `u.pos = nones u.cell ∘ u.perm`. -/
@[simp] theorem nones_cell_perm (u : ▪m ⟶ ▪n) (i : Fin m) :
    nones (cell u) (perm u i) = u.pos i := nones_nonesIdx _ _ _

/-- …read as the axes the factorization's cube face occupies. -/
@[simp] theorem faceEmb_ofSign_cell (u : ▪m ⟶ ▪n) (i : Fin m) :
    faceEmb (Box.ofSign (cell u)) (perm u i) = u.pos i := by
  change nones (Box.sign (Box.ofSign (cell u))) (perm u i) = u.pos i
  rw [Box.sign_ofSign]
  exact nones_cell_perm u i

theorem perm_symm_apply (u : ▪m ⟶ ▪n) (j : Fin m) :
    (perm u).symm j = (u.coord (nones (cell u) j)).elim (fun _ => j) _root_.id := rfl

end SHom

@[simp] theorem SHom.cell_symHom_comp {m n : ℕ} (σ : Equiv.Perm (Fin m)) (φ : ▫m ⟶ ▫n) :
    SHom.cell (symHom σ ≫ J.map φ) = Box.sign φ := by
  refine Subtype.ext (funext fun j => ?_)
  rw [SHom.cell_val]
  rcases hc : (Box.sign φ).val j with _ | b
  · rw [SBox.comp_coord, J_map_coord,
      (cellCoord_eq_inr_iff _ _ _).2 (nones_nonesIdx (Box.sign φ) j (mem_noneSet.mpr hc)).symm]
    rfl
  · rw [SBox.comp_coord, J_map_coord, (cellCoord_eq_inl_iff _ _ b).2 hc]
    rfl

@[simp] theorem SHom.perm_symHom_comp {m n : ℕ} (σ : Equiv.Perm (Fin m)) (φ : ▫m ⟶ ▫n) :
    SHom.perm (symHom σ ≫ J.map φ) = σ := by
  refine Equiv.ext fun i => ?_
  refine (nones (SHom.cell (symHom σ ≫ J.map φ))).injective ?_
  rw [SHom.nones_cell_perm, congrArg nones (SHom.cell_symHom_comp σ φ)]
  rfl

/-- **Unique factorization**: every symmetric box map is a permutation followed by a cube face,
in exactly one way. -/
def sHomEquiv {m n : ℕ} : (▪m ⟶ ▪n) ≃ Equiv.Perm (Fin m) × (▫m ⟶ ▫n) where
  toFun u := (SHom.perm u, Box.ofSign (SHom.cell u))
  invFun p := symHom p.1 ≫ J.map p.2
  left_inv u := by
    refine SHom.ext (funext fun j => ?_)
    rw [SBox.comp_coord, J_map_coord, Box.sign_ofSign]
    rcases hc : SHom.coord u j with b | i
    · rw [(cellCoord_eq_inl_iff _ _ b).2 (SHom.cell_val_eq_some hc), Sum.elim_inl]
    · obtain ⟨k, hk⟩ : ∃ k, j = nones (SHom.cell u) k :=
        ⟨nonesIdx (SHom.cell u) j (mem_noneSet.mpr (SHom.cell_val_eq_none hc)),
          (nones_nonesIdx _ _ _).symm⟩
      have hsymm : (SHom.perm u).symm k = i := by
        rw [SHom.perm_symm_apply, ← hk, hc]; rfl
      rw [(cellCoord_eq_inr_iff _ _ k).2 hk, Sum.elim_inr, symHom_coord, hsymm]
  right_inv p := by
    obtain ⟨σ, φ⟩ := p
    rw [Prod.mk.injEq]
    exact ⟨SHom.perm_symHom_comp σ φ, by rw [SHom.cell_symHom_comp, Box.ofSign_sign]⟩

@[simp] theorem sHomEquiv_symm_apply {m n : ℕ} (σ : Equiv.Perm (Fin m)) (φ : ▫m ⟶ ▫n) :
    sHomEquiv.symm (σ, φ) = symHom σ ≫ J.map φ := rfl

@[simp] theorem sHomEquiv_apply {m n : ℕ} (u : ▪m ⟶ ▪n) :
    sHomEquiv u = (SHom.perm u, Box.ofSign (SHom.cell u)) := rfl

/-- The factorization's injection: sort `σ` first, then read off the free coordinates of `φ`. -/
@[simp] theorem SHom.pos_symHom_comp {m n : ℕ} (σ : Equiv.Perm (Fin m)) (φ : ▫m ⟶ ▫n) (i : Fin m) :
    SHom.pos (symHom σ ≫ J.map φ) i = faceEmb φ (σ i) := rfl

@[simp] theorem sHomEquiv_J_map {m n : ℕ} (φ : ▫m ⟶ ▫n) : sHomEquiv (J.map φ) = (1, φ) :=
  sHomEquiv.apply_eq_iff_eq_symm_apply.2 (by rw [sHomEquiv_symm_apply, symHom_one,
    Category.id_comp])

@[simp] theorem sHomEquiv_symHom {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    sHomEquiv (symHom σ) = (σ, 𝟙 ▫m) :=
  sHomEquiv.apply_eq_iff_eq_symm_apply.2 (by
    have hid : J.map (𝟙 ▫m) = 𝟙 (▪m) := J.map_id ▫m
    rw [sHomEquiv_symm_apply, hid]
    exact (Category.comp_id (symHom σ)).symm)

/-! ## Sorting through a symmetric map

```
   ▪m ─────── u ───────▶ ▪n ─── symHom σ ───▶ ▪n
    │                                          ‖
    │ symHom (sortPerm u σ)                    ‖
    ▼                                          ‖
   ▪m ────────── J (sortFace u σ) ────────────▶ ▪n
```
The two halves compose as an action and a cocycle (`sortPerm_comp`, `sortFace_comp`) — which is
all a presheaf built on them needs.

Statements are phrased with `sHomEquiv.symm` rather than `symHom _ ≫ J.map _`: the latter
elaborates its target object as `J.obj ▫n`, and `rw` will not unfold `J` to reach `▪n`. -/

namespace SHom

variable {p m n : ℕ}

/-- The permutation half of the factorization of `u ≫ symHom σ`. -/
def sortPerm (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin m) :=
  perm (u ≫ symHom σ)

/-- The cube-face half of the factorization of `u ≫ symHom σ`. -/
def sortFace (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) : ▫m ⟶ ▫n :=
  Box.ofSign (cell (u ≫ symHom σ))

theorem sHomEquiv_comp_symHom (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) :
    sHomEquiv (u ≫ symHom σ) = (sortPerm u σ, sortFace u σ) := rfl

/-- The defining square. -/
theorem symm_sortPerm_sortFace (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) :
    sHomEquiv.symm (sortPerm u σ, sortFace u σ) = u ≫ symHom σ :=
  (congrArg sHomEquiv.symm (sHomEquiv_comp_symHom u σ)).symm.trans
    (sHomEquiv.symm_apply_apply _)

/-- …and its uniqueness: any factorization of `u ≫ symHom σ` *is* the sorted one. -/
theorem sortPerm_sortFace_eq {u : ▪m ⟶ ▪n} {σ : Equiv.Perm (Fin n)} {τ : Equiv.Perm (Fin m)}
    {ψ : ▫m ⟶ ▫n} (h : sHomEquiv.symm (τ, ψ) = u ≫ symHom σ) :
    (sortPerm u σ, sortFace u σ) = (τ, ψ) :=
  (congrArg sHomEquiv h).symm.trans (sHomEquiv.apply_symm_apply _)

theorem sortPerm_sortFace_id (σ : Equiv.Perm (Fin n)) :
    (sortPerm (𝟙 ▪n) σ, sortFace (𝟙 ▪n) σ) = (σ, 𝟙 ▫n) := by
  rw [← sHomEquiv_comp_symHom, Category.id_comp, sHomEquiv_symHom]

@[simp] theorem sortPerm_id (σ : Equiv.Perm (Fin n)) : sortPerm (𝟙 ▪n) σ = σ :=
  congrArg Prod.fst (sortPerm_sortFace_id σ)

@[simp] theorem sortFace_id (σ : Equiv.Perm (Fin n)) : sortFace (𝟙 ▪n) σ = 𝟙 ▫n :=
  congrArg Prod.snd (sortPerm_sortFace_id σ)

/-- Sorting through a symmetry just multiplies. -/
theorem sortPerm_sortFace_symHom (τ σ : Equiv.Perm (Fin m)) :
    (sortPerm (symHom τ) σ, sortFace (symHom τ) σ) = (σ * τ, 𝟙 ▫m) := by
  rw [← sHomEquiv_comp_symHom, symHom_comp, sHomEquiv_symHom]

@[simp] theorem sortPerm_symHom (τ σ : Equiv.Perm (Fin m)) : sortPerm (symHom τ) σ = σ * τ :=
  congrArg Prod.fst (sortPerm_sortFace_symHom τ σ)

@[simp] theorem sortFace_symHom (τ σ : Equiv.Perm (Fin m)) : sortFace (symHom τ) σ = 𝟙 ▫m :=
  congrArg Prod.snd (sortPerm_sortFace_symHom τ σ)

/-- A cube face in the identity order is already sorted. -/
theorem sortPerm_sortFace_J_map (φ : ▫m ⟶ ▫n) :
    (sortPerm (J.map φ) 1, sortFace (J.map φ) 1) = (1, φ) := by
  rw [← sHomEquiv_comp_symHom, symHom_one, Category.comp_id, sHomEquiv_J_map]

@[simp] theorem sortPerm_J_map_one (φ : ▫m ⟶ ▫n) : sortPerm (J.map φ) 1 = 1 :=
  congrArg Prod.fst (sortPerm_sortFace_J_map φ)

@[simp] theorem sortFace_J_map_one (φ : ▫m ⟶ ▫n) : sortFace (J.map φ) 1 = φ :=
  congrArg Prod.snd (sortPerm_sortFace_J_map φ)

/-- The factorization absorbs a cube face on the right. -/
theorem symm_comp_J_map (τ : Equiv.Perm (Fin p)) (ψ' : ▫p ⟶ ▫m) (ψ : ▫m ⟶ ▫n) :
    sHomEquiv.symm (τ, ψ' ≫ ψ) = sHomEquiv.symm (τ, ψ') ≫ J.map ψ := by
  rw [sHomEquiv_symm_apply, sHomEquiv_symm_apply, J.map_comp]
  exact (Category.assoc _ _ _).symm

/-- …and a symmetric map on the left — the two halves of `≫` in `SBox`. -/
theorem symm_comp_left (v : ▪p ⟶ ▪m) (τ : Equiv.Perm (Fin m)) (ψ : ▫m ⟶ ▫n) :
    sHomEquiv.symm (sortPerm v τ, sortFace v τ ≫ ψ) = v ≫ sHomEquiv.symm (τ, ψ) := by
  rw [symm_comp_J_map, symm_sortPerm_sortFace, sHomEquiv_symm_apply]
  exact Category.assoc _ _ _

/-- **Sorting twice is sorting once** — associativity in `SBox` plus uniqueness, no
combinatorics. -/
theorem sortPerm_sortFace_comp (v : ▪p ⟶ ▪m) (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) :
    (sortPerm (v ≫ u) σ, sortFace (v ≫ u) σ)
      = (sortPerm v (sortPerm u σ), sortFace v (sortPerm u σ) ≫ sortFace u σ) :=
  sortPerm_sortFace_eq (by
    rw [symm_comp_left, symm_sortPerm_sortFace]
    exact (Category.assoc _ _ _).symm)

@[simp] theorem sortPerm_comp (v : ▪p ⟶ ▪m) (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) :
    sortPerm (v ≫ u) σ = sortPerm v (sortPerm u σ) :=
  congrArg Prod.fst (sortPerm_sortFace_comp v u σ)

@[simp] theorem sortFace_comp (v : ▪p ⟶ ▪m) (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) :
    sortFace (v ≫ u) σ = sortFace v (sortPerm u σ) ≫ sortFace u σ :=
  congrArg Prod.snd (sortPerm_sortFace_comp v u σ)

/-- A symmetry and its inverse cancel. -/
theorem comp_symHom_inv (u : ▪m ⟶ ▪n) (σ : Equiv.Perm (Fin n)) :
    (u ≫ symHom σ⁻¹) ≫ symHom σ = u := by
  rw [Category.assoc, symHom_comp, mul_inv_cancel, symHom_one, Category.comp_id]

/-! ### Sorting is `Tuple.sort` -/

/-- **The sorting permutation is the rank map of the injection**: `u.pos ∘ (perm u)⁻¹` is the
monotone enumeration `nones (cell u)`, and `u.pos` is injective, so `Tuple.sort` is pinned. -/
theorem perm_eq_sort_inv (u : ▪m ⟶ ▪n) : perm u = (Tuple.sort u.pos)⁻¹ :=
  Tuple.eq_sort_inv u.pos_injective (by
    have h : u.pos ∘ ⇑(perm u)⁻¹ = ⇑(nones (cell u)) := funext fun j => by
      rw [Function.comp_apply, Equiv.Perm.inv_def, ← nones_cell_perm u ((perm u).symm j),
        Equiv.apply_symm_apply]
    rw [h]
    exact (nones (cell u)).monotone)

/-- Sorting an order through a cube face sorts the tuple `σ ∘ faceEmb φ`. -/
theorem sortPerm_J_map (φ : ▫m ⟶ ▫n) (σ : Equiv.Perm (Fin n)) :
    sortPerm (J.map φ) σ = (Tuple.sort fun i => σ (faceEmb φ i))⁻¹ := by
  rw [sortPerm, perm_eq_sort_inv]
  rfl

end SHom

/-- Composing with a symmetry on the left multiplies the order. -/
@[simp] theorem symm_symHom_comp {m n : ℕ} (τ σ : Equiv.Perm (Fin m)) (ψ : ▫m ⟶ ▫n) :
    symHom τ ≫ sHomEquiv.symm (σ, ψ) = sHomEquiv.symm (σ * τ, ψ) := by
  rw [← SHom.symm_comp_left, SHom.sortPerm_symHom, SHom.sortFace_symHom, Category.id_comp]

/-- A cube face is the factorization with the identity order. -/
@[simp] theorem sHomEquiv_symm_one {m n : ℕ} (ψ : ▫m ⟶ ▫n) : sHomEquiv.symm (1, ψ) = J.map ψ :=
  sHomEquiv.symm_apply_eq.2 (sHomEquiv_J_map ψ).symm

/-- `comp_symHom_inv` at a cube face, spelled as callers see it (`J.map ψ`'s target elaborates
to `J.obj ▫n`, which `rw` will not unfold to `▪n`). -/
theorem SHom.J_map_comp_symHom_inv {m n : ℕ} (ψ : ▫m ⟶ ▫n) (σ : Equiv.Perm (Fin n)) :
    (J.map ψ ≫ symHom σ⁻¹) ≫ symHom σ = J.map ψ := SHom.comp_symHom_inv (J.map ψ) σ

/-- **Sorting is invertible**: sorting `J ψ` through `σ⁻¹`, then the outcome back through `σ`,
returns `ψ` with the inverse order — uniqueness of the factorization, read backwards. -/
theorem SHom.sortPerm_sortFace_inv {m n : ℕ} (ψ : ▫m ⟶ ▫n) (σ : Equiv.Perm (Fin n)) :
    (SHom.sortPerm (J.map (SHom.sortFace (J.map ψ) σ⁻¹)) σ,
        SHom.sortFace (J.map (SHom.sortFace (J.map ψ) σ⁻¹)) σ)
      = ((SHom.sortPerm (J.map ψ) σ⁻¹)⁻¹, ψ) := by
  refine SHom.sortPerm_sortFace_eq ?_
  have h1 : sHomEquiv.symm (SHom.sortPerm (J.map ψ) σ⁻¹, SHom.sortFace (J.map ψ) σ⁻¹)
      = J.map ψ ≫ symHom σ⁻¹ := SHom.symm_sortPerm_sortFace (J.map ψ) σ⁻¹
  have h2 : (symHom (SHom.sortPerm (J.map ψ) σ⁻¹)⁻¹
        ≫ sHomEquiv.symm (SHom.sortPerm (J.map ψ) σ⁻¹, SHom.sortFace (J.map ψ) σ⁻¹)) ≫ symHom σ
      = J.map (SHom.sortFace (J.map ψ) σ⁻¹) ≫ symHom σ := by
    rw [symm_symHom_comp, mul_inv_cancel, sHomEquiv_symm_one]
    rfl
  rw [h1] at h2
  refine Eq.trans ?_ h2
  rw [Category.assoc]
  exact congrArg (fun t => symHom (SHom.sortPerm (J.map ψ) σ⁻¹)⁻¹ ≫ t)
    (SHom.J_map_comp_symHom_inv ψ σ).symm

@[simp] theorem SHom.sortPerm_sortFace_perm {m n : ℕ} (ψ : ▫m ⟶ ▫n) (σ : Equiv.Perm (Fin n)) :
    SHom.sortPerm (J.map (SHom.sortFace (J.map ψ) σ⁻¹)) σ = (SHom.sortPerm (J.map ψ) σ⁻¹)⁻¹ :=
  congrArg Prod.fst (SHom.sortPerm_sortFace_inv ψ σ)

@[simp] theorem SHom.sortFace_sortFace_inv {m n : ℕ} (ψ : ▫m ⟶ ▫n) (σ : Equiv.Perm (Fin n)) :
    SHom.sortFace (J.map (SHom.sortFace (J.map ψ) σ⁻¹)) σ = ψ :=
  congrArg Prod.snd (SHom.sortPerm_sortFace_inv ψ σ)
