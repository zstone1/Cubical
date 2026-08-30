import CubeChains.Machinery.Cube.SymPresheaf
import CubeChains.Precubical.Wedge.Wedge
import Mathlib.CategoryTheory.Conj

/-!
# Machinery/Cube/SymRepresentable — the free symmetric cube is representable

`symFree (□ⁿ) ≅ y(▪n)`: an `SBox`-cell of the free symmetric cube is a cube face with an order on
its axes, which is exactly the sorting factorization `sHomEquiv`.  Restricting along `J` therefore
makes `Aut ▪n = Sₙ` act on `H(□ⁿ)` by honest precubical automorphisms, and faithfully — on the top
cell the action is left multiplication of orders.  The same rigidity that makes the action faithful
kills the projection: for `n ≥ 2` there is no map `H(□ⁿ) ⟶ □ⁿ` at all.
-/

open CategoryTheory Opposite

namespace CubeChains

/-- `y(▪n)` read as a precubical set. -/
def symYoneda : SBox ⥤ PrecubicalSet := yoneda ⋙ symRestrict

/-- **`symFree` of a cube is representable** — the sorting factorization, made natural. -/
def symFreeCube (n : ℕ) : symFree.obj (□n).toPsh ≅ yoneda.obj ▪n :=
  NatIso.ofComponents (fun Y => (sHomEquiv (m := Y.unop.dim) (n := n)).symm.toIso)
    (fun u => by
      apply ConcreteCategory.hom_ext
      intro p
      exact SHom.symm_comp_left u.unop p.1 p.2)

@[simp] theorem symFreeCube_hom_app (n : ℕ) {m : ℕ}
    (p : Equiv.Perm (Fin m) × ((□n).toPsh.obj (op ▫m))) :
    (symFreeCube n).hom.app (op ▪m) p = sHomEquiv.symm p := rfl

@[simp] theorem symFreeCube_inv_app (n : ℕ) {m : ℕ} (u : ▪m ⟶ ▪n) :
    (symFreeCube n).inv.app (op ▪m) u = sHomEquiv u := rfl

/-- **`H` of a cube is `▪n`'s representable, restricted along `J`.** -/
def HCube (n : ℕ) : H.obj (□n).toPsh ≅ symYoneda.obj ▪n :=
  symRestrict.mapIso (symFreeCube n)

/-! ## The direction a step performs

An `H(□ⁿ)`-cell is a symmetric box map, and a symmetric box map's `pos` already reads its
`j`-th step off as an axis of `□ⁿ` — the order and the face, composed. -/

/-- The axis of `□ⁿ` an `H(□ⁿ)`-cell performs at step `j`. -/
def cellDir {n m : ℕ} (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n)) (j : Fin m) : Fin n :=
  SHom.pos (sHomEquiv.symm p) j

/-- …read on the sorting factorization: step `j` is the cell's own axis `p.1 j`. -/
theorem cellDir_eq {n m : ℕ} (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n)) (j : Fin m) :
    cellDir p j = faceEmb p.2 (p.1 j) := by
  conv_rhs => rw [← sHomEquiv.apply_symm_apply p]
  exact (SHom.faceEmb_ofSign_cell (sHomEquiv.symm p) j).symm

/-! ## The reorientation action -/

/-- **`Sₙ` acts on `H(□ⁿ)` by precubical automorphisms** — the symmetries of `▪n`, transported
along representability. -/
def reorientH (n : ℕ) : Equiv.Perm (Fin n) →* Aut (H.obj (□n).toPsh) :=
  ((HCube n).symm.conjAut.toMonoidHom).comp
    ((symYoneda.mapAut ▪n).comp (autMulEquivPerm n).symm.toMonoidHom)

/-- The action is post-composition with `symHom σ`, read through the factorization. -/
theorem reorientH_app (n : ℕ) (σ : Equiv.Perm (Fin n)) {m : ℕ}
    (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n)) :
    (reorientH n σ).hom⟪m⟫ p = sHomEquiv (sHomEquiv.symm p ≫ symHom σ) := rfl

/-- **The action relabels the steps**: the axis performed at step `j` moves by `σ`. -/
theorem cellDir_reorientH (n : ℕ) (σ : Equiv.Perm (Fin n)) {m : ℕ}
    (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n)) (j : Fin m) :
    cellDir ((reorientH n σ).hom⟪m⟫ p) j = σ (cellDir p j) :=
  congrArg (fun u : ▪m ⟶ ▪n => SHom.pos u j)
    ((congrArg sHomEquiv.symm (reorientH_app n σ p)).trans (sHomEquiv.symm_apply_apply _))

/-- **The action permutes axes**: the cell's `i`-th free direction leaves axis `j` for `σ j`. -/
theorem faceEmb_reorientH (n : ℕ) (σ : Equiv.Perm (Fin n)) {m : ℕ}
    (p : Equiv.Perm (Fin m) × (▫m ⟶ ▫n)) (i : Fin m) :
    faceEmb ((reorientH n σ).hom⟪m⟫ p).2 (((reorientH n σ).hom⟪m⟫ p).1 i)
      = σ (faceEmb p.2 (p.1 i)) :=
  (cellDir_eq _ i).symm.trans
    ((cellDir_reorientH n σ p i).trans (congrArg σ (cellDir_eq p i)))

/-- **On top cells the action is left multiplication of orders.** -/
theorem reorientH_top (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    (reorientH n σ).hom⟪n⟫ (τ, 𝟙 ▫n) = (σ * τ, 𝟙 ▫n) :=
  have h : sHomEquiv.symm (τ, 𝟙 ▫n) = symHom τ :=
    sHomEquiv.symm_apply_eq.2 (sHomEquiv_symHom τ).symm
  (congrArg (fun w => sHomEquiv (w ≫ symHom σ)) h).trans
    ((congrArg sHomEquiv (symHom_comp τ σ)).trans (sHomEquiv_symHom (σ * τ)))

/-- **The reorientation action is faithful.** -/
theorem reorientH_injective (n : ℕ) : Function.Injective (reorientH n) := fun σ σ' h => by
  have h' : ((σ * 1 : Equiv.Perm (Fin n)), 𝟙 ▫n) = ((σ' * 1 : Equiv.Perm (Fin n)), 𝟙 ▫n) :=
    (reorientH_top n σ 1).symm.trans
      ((congrArg (fun a : Aut (H.obj (□n).toPsh) => a.hom⟪n⟫ (1, 𝟙 ▫n)) h).trans
        (reorientH_top n σ' 1))
  simpa using congrArg Prod.fst h'

/-! ## …but there is no map back to the cube

```
   (▪n ⟶ ▪n) ───── φ ────▶ (▫n ⟶ ▫n)      the target is {𝟙}: cubes are rigid
        │                       │
   J.map g ≫ -             g ≫ -           naturality along g : ▫k ⟶ ▫n
        ▼                       ▼
   (▪k ⟶ ▪n) ───── φ ────▶ (▫k ⟶ ▫n)      so φ (J.map g ≫ symHom σ) = g, every σ
```
On an edge (`k = 1`) `J` is onto, so one element of the bottom left has two such readings, and
they differ by `σ`. -/

/-- The unit law of the symmetry action; `Category.comp_id` will not match this composite, whose
middle object is spelled `J.obj ▫n`. -/
theorem comp_symHom_one {m n : ℕ} (u : ▪m ⟶ ▪n) :
    u ≫ symHom (1 : Equiv.Perm (Fin n)) = u := by rw [symHom_one, Category.comp_id]

/-- **An edge carries no order**: `Perm (Fin 1)` is trivial, so `J` is onto `▪1 ⟶ ▪n`. -/
theorem J_map_edge {n : ℕ} (u : ▪1 ⟶ ▪n) : J.map (Box.ofSign (SHom.cell u)) = u := by
  have h : sHomEquiv.symm (SHom.perm u, Box.ofSign (SHom.cell u)) = u :=
    sHomEquiv.symm_apply_apply u
  rwa [sHomEquiv_symm_apply, Subsingleton.elim (SHom.perm u) 1, symHom_one,
    Category.id_comp] at h

/-- A map `H(□ⁿ) ⟶ □ⁿ` reads a symmetric map off any `J`-factorization of it, forgetting `σ`. -/
theorem cubeHom_apply {n k : ℕ} (φ : H.obj (□n).toPsh ⟶ (□n).toPsh) (u : ▪k ⟶ ▪n)
    (g : ▫k ⟶ ▫n) (σ : Equiv.Perm (Fin n)) (h : u = J.map g ≫ symHom σ) :
    φ.app (op ▫k) (sHomEquiv u) = g := by
  have hnat := NatTrans.naturality_apply φ g.op
    (show (H.obj (□n).toPsh).obj (op ▫n) from (σ, 𝟙 ▫n))
  rw [Box.endo_eq_id (φ.app (op ▫n) (show (H.obj (□n).toPsh).obj (op ▫n) from (σ, 𝟙 ▫n)))] at hnat
  refine Eq.trans (congrArg _ ?_) (hnat.trans (Category.comp_id g))
  exact (congrArg sHomEquiv h).trans (Prod.ext rfl (Category.comp_id _).symm)

/-- …so every symmetry would fix the axis of every edge — the two readings of `J.map g ≫ symHom σ`
are `g` and its `σ`-relabelling. -/
theorem cubeHom_fix_axis {n : ℕ} (φ : H.obj (□n).toPsh ⟶ (□n).toPsh) (g : ▫1 ⟶ ▫n)
    (σ : Equiv.Perm (Fin n)) : σ (faceEmb g 0) = faceEmb g 0 := by
  obtain ⟨u, hu⟩ : ∃ u : ▪1 ⟶ ▪n, u = J.map g ≫ symHom σ := ⟨_, rfl⟩
  have hgg : g = Box.ofSign (SHom.cell u) :=
    (cubeHom_apply φ u g σ hu).symm.trans (cubeHom_apply φ u (Box.ofSign (SHom.cell u)) 1
      ((J_map_edge u).symm.trans (comp_symHom_one _).symm))
  exact congrArg (fun w : ▪1 ⟶ ▪n => SHom.pos w 0)
    (hu.symm.trans ((J_map_edge u).symm.trans (congrArg J.map hgg.symm)))

/-- **There is no map `H(□ⁿ) ⟶ □ⁿ` once `n ≥ 2`** — a transposition moves the axis of an edge. -/
theorem isEmpty_cubeHom {n : ℕ} (hn : 2 ≤ n) :
    IsEmpty (H.obj (□n).toPsh ⟶ (□n).toPsh) := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  refine ⟨fun φ => ?_⟩
  obtain ⟨g⟩ : Nonempty (▫1 ⟶ ▫n) :=
    ⟨Box.ofSign (StdCube.freeMin (StdCube.constVertex n false) (show 0 < n by omega))⟩
  obtain ⟨j, hj⟩ := exists_ne (faceEmb g 0)
  exact hj ((Equiv.swap_apply_left (faceEmb g 0) j).symm.trans
    (cubeHom_fix_axis φ g (Equiv.swap (faceEmb g 0) j)))

instance : IsEmpty (H.obj (□2).toPsh ⟶ (□2).toPsh) := isEmpty_cubeHom le_rfl

end CubeChains
