import CubeChains.Machinery.Cube.SymBox
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Machinery/Cube/SymPresheaf — the symmetric round trip `H = J* ∘ J₍!₎`

`SymPrecubicalSet = SBoxᵒᵖ ⥤ Type`; `symRestrict` is precomposition with `J.op`, and `symFree` is
its left adjoint written out: a cell of `symFree.obj K` at `▪n` is a cell of `K` together with an
order on its `n` axes, restricted by factoring `u ≫ symHom σ` (`SHom.sortPerm`/`SHom.sortFace`).

Functoriality is uniqueness of the factorization plus associativity in `SBox` — no combinatorics.
The universal property rests on the one identity
`(σ, y) = (symFree.obj K).map (symHom σ).op (1, y)`.
-/

open CategoryTheory Opposite

/-- **Symmetric precubical sets**: presheaves on the symmetric box category. -/
abbrev SymPrecubicalSet : Type 1 := SBoxᵒᵖ ⥤ Type

namespace CubeChains

/-- `J*` — a symmetric precubical set is in particular a precubical set. -/
def symRestrict : SymPrecubicalSet ⥤ PrecubicalSet :=
  (Functor.whiskeringLeft Boxᵒᵖ SBoxᵒᵖ Type).obj J.op

/-! ## The free symmetric precubical set

```
   (symFree.obj K).obj (op ▪n)  =  Perm (Fin n) × K.obj (op ▫n)
        │                                    │
        │ map u.op                           │ (σ, y) ↦ (sortPerm u σ, K.map (sortFace u σ).op y)
        ▼                                    ▼
   (symFree.obj K).obj (op ▪m)  =  Perm (Fin m) × K.obj (op ▫m)
```
-/

/-- `J₍!₎` — a cell of `K` together with an order on its axes. -/
def symFree : PrecubicalSet ⥤ SymPrecubicalSet where
  obj K :=
    { obj := fun Y => Equiv.Perm (Fin Y.unop.dim) × K.obj (op ▫Y.unop.dim)
      map := fun u =>
        ↾fun p => (SHom.sortPerm u.unop p.1, K.map (SHom.sortFace u.unop p.1).op p.2)
      map_id := fun Y => by
        apply ConcreteCategory.hom_ext; intro p
        change (SHom.sortPerm (𝟙 Y.unop) p.1, K.map (SHom.sortFace (𝟙 Y.unop) p.1).op p.2) = p
        rw [SHom.sortPerm_id, SHom.sortFace_id, op_id, Functor.map_id_apply]
      map_comp := fun u v => by
        apply ConcreteCategory.hom_ext; intro p
        change (SHom.sortPerm (v.unop ≫ u.unop) p.1,
            K.map (SHom.sortFace (v.unop ≫ u.unop) p.1).op p.2) = _
        rw [SHom.sortPerm_comp, SHom.sortFace_comp, op_comp, Functor.map_comp_apply]
        rfl }
  map f :=
    { app := fun Y => ↾fun p => (p.1, f.app (op ▫Y.unop.dim) p.2)
      naturality := fun X Y u => by
        apply ConcreteCategory.hom_ext; intro p
        simp only [CategoryTheory.comp_apply]
        exact Prod.ext rfl (NatTrans.naturality_apply f (SHom.sortFace u.unop p.1).op p.2) }
  map_id K := by
    refine NatTrans.ext (funext fun Y => ?_)
    apply ConcreteCategory.hom_ext; intro p
    rfl
  map_comp f g := by
    refine NatTrans.ext (funext fun Y => ?_)
    apply ConcreteCategory.hom_ext; intro p
    rfl

theorem symFree_obj_obj (K : PrecubicalSet) (n : ℕ) :
    (symFree.obj K).obj (op ▪n) = (Equiv.Perm (Fin n) × K.obj (op ▫n)) := rfl

theorem symFree_obj_map {K : PrecubicalSet} {m n : ℕ} (u : ▪m ⟶ ▪n)
    (p : Equiv.Perm (Fin n) × K.obj (op ▫n)) :
    (symFree.obj K).map u.op p
      = (SHom.sortPerm u p.1, K.map (SHom.sortFace u p.1).op p.2) := rfl

@[simp] theorem symFree_map_app {K L : PrecubicalSet} (f : K ⟶ L) {n : ℕ}
    (p : Equiv.Perm (Fin n) × K.obj (op ▫n)) :
    (symFree.map f).app (op ▪n) p = (p.1, f.app (op ▫n) p.2) := rfl

/-- Reindexing along a symmetry only multiplies the order. -/
theorem symFree_obj_map_symHom {K : PrecubicalSet} {n : ℕ} (τ σ : Equiv.Perm (Fin n))
    (y : K.obj (op ▫n)) :
    (symFree.obj K).map (symHom τ).op (σ, y) = (σ * τ, y) := by
  rw [symFree_obj_map, SHom.sortPerm_symHom, SHom.sortFace_symHom, op_id, Functor.map_id_apply]

/-- **Every element is a symmetry away from the identity order** — the identity the universal
property runs on. -/
theorem symFree_obj_symHom_one {K : PrecubicalSet} {n : ℕ}
    (p : Equiv.Perm (Fin n) × K.obj (op ▫n)) :
    (symFree.obj K).map (symHom p.1).op (1, p.2) = p := by
  rw [symFree_obj_map_symHom, one_mul]

/-! ## The universal property -/

/-- The unit: a cell of `K` is a cell in its own order. -/
def symUnit (K : PrecubicalSet) : K ⟶ J.op ⋙ symFree.obj K where
  app X := ↾fun y => (1, y)
  naturality X Y g := by
    apply ConcreteCategory.hom_ext; intro y
    simp only [CategoryTheory.comp_apply]
    change (1, K.map g y)
      = (SHom.sortPerm (J.map g.unop) 1, K.map (SHom.sortFace (J.map g.unop) 1).op y)
    rw [SHom.sortPerm_J_map_one, SHom.sortFace_J_map_one]
    rfl

/-- Reading a map out of `symFree.obj K` on the identity order. -/
theorem unit_whisker_app {K : PrecubicalSet} {G : SymPrecubicalSet} (γ : symFree.obj K ⟶ G)
    {n : ℕ} (y : K.obj (op ▫n)) :
    (symUnit K ≫ Functor.whiskerLeft J.op γ).app (op ▫n) y = γ.app (op ▪n) (1, y) := by
  rw [NatTrans.comp_app, types_comp_apply]
  rfl

/-- The unit is natural in `K`. -/
theorem symUnit_naturality {K L : PrecubicalSet} (f : K ⟶ L) :
    symUnit K ≫ Functor.whiskerLeft J.op (symFree.map f) = f ≫ symUnit L :=
  rfl

/-- `β`'s naturality, read in `G` along the symmetric map of a cube face. -/
theorem naturality_symm_one {K : PrecubicalSet} {G : SymPrecubicalSet} (β : K ⟶ J.op ⋙ G)
    {m n : ℕ} (ψ : ▫m ⟶ ▫n) (y : K.obj (op ▫n)) :
    β.app (op ▫m) (K.map ψ.op y) = G.map (sHomEquiv.symm (1, ψ)).op (β.app (op ▫n) y) := by
  rw [sHomEquiv_symm_one]
  exact NatTrans.naturality_apply β ψ.op y

/-- The descent of `β` along the unit: push the cell into the order it carries. -/
def symDesc {K : PrecubicalSet} (G : SymPrecubicalSet) (β : K ⟶ J.op ⋙ G) :
    symFree.obj K ⟶ G where
  app Y := ↾fun p => G.map (symHom p.1).op (β.app (op ▫Y.unop.dim) p.2)
  naturality X Y u := by
    apply ConcreteCategory.hom_ext; intro p
    simp only [CategoryTheory.comp_apply]
    change G.map (symHom (SHom.sortPerm u.unop p.1)).op
        (β.app _ (K.map (SHom.sortFace u.unop p.1).op p.2))
      = G.map u (G.map (symHom p.1).op (β.app _ p.2))
    rw [naturality_symm_one β (SHom.sortFace u.unop p.1) p.2, ← Functor.map_comp_apply,
      ← op_comp, symm_symHom_comp, one_mul, SHom.symm_sortPerm_sortFace, op_comp,
      Functor.map_comp_apply]
    rfl

/-- A map out of `symFree.obj K` is determined by its value on the identity order. -/
theorem app_eq_map_symHom {K : PrecubicalSet} {G : SymPrecubicalSet} (δ : symFree.obj K ⟶ G)
    {n : ℕ} (p : Equiv.Perm (Fin n) × K.obj (op ▫n)) :
    δ.app (op ▪n) p = G.map (symHom p.1).op (δ.app (op ▪n) (1, p.2)) := by
  conv_lhs => rw [← symFree_obj_symHom_one p]
  rw [← types_comp_apply ((symFree.obj K).map (symHom p.1).op) (δ.app (op ▪n)), δ.naturality]
  rfl

/-- …hence two maps agreeing on the unit agree. -/
theorem symFree_hom_ext {K : PrecubicalSet} {G : SymPrecubicalSet} {γ γ' : symFree.obj K ⟶ G}
    (h : symUnit K ≫ Functor.whiskerLeft J.op γ = symUnit K ≫ Functor.whiskerLeft J.op γ') :
    γ = γ' := by
  refine NatTrans.ext (funext fun Y => ?_)
  apply ConcreteCategory.hom_ext; intro p
  have hb : γ.app (op ▪Y.unop.dim) (1, p.2) = γ'.app (op ▪Y.unop.dim) (1, p.2) := by
    rw [← unit_whisker_app γ, ← unit_whisker_app γ', h]
  exact (app_eq_map_symHom γ p).trans ((congrArg _ hb).trans (app_eq_map_symHom γ' p).symm)

/-- …and the descent really descends. -/
theorem symUnit_symDesc {K : PrecubicalSet} (G : SymPrecubicalSet) (β : K ⟶ J.op ⋙ G) :
    symUnit K ≫ Functor.whiskerLeft J.op (symDesc G β) = β := by
  refine NatTrans.ext (funext fun X => ?_)
  apply ConcreteCategory.hom_ext; intro y
  rw [unit_whisker_app (n := X.unop.dim)]
  change G.map (symHom 1).op (β.app X y) = β.app X y
  rw [symHom_one, op_id, Functor.map_id_apply]

/-- **`symFree.obj K` is the left Kan extension of `K` along `J.op`.** -/
instance symFree_isLeftKanExtension (K : PrecubicalSet) :
    (symFree.obj K).IsLeftKanExtension (symUnit K) where
  nonempty_isUniversal := ⟨Limits.IsInitial.ofUniqueHom
    (fun E => StructuredArrow.homMk (symDesc E.right E.hom) (symUnit_symDesc E.right E.hom))
    (fun E m => StructuredArrow.hom_ext _ _
      (symFree_hom_ext ((StructuredArrow.w m).trans (symUnit_symDesc E.right E.hom).symm)))⟩

instance (K : PrecubicalSet) : Functor.HasLeftKanExtension J.op K :=
  Functor.HasLeftKanExtension.mk (symFree.obj K) (symUnit K)

/-! ## The round trip -/

/-- `H = J* ∘ J₍!₎` — the symmetric round trip on precubical sets. -/
def H : PrecubicalSet ⥤ PrecubicalSet := symFree ⋙ symRestrict

theorem H_obj_obj (K : PrecubicalSet) (n : ℕ) :
    (H.obj K).obj (op ▫n) = (Equiv.Perm (Fin n) × K.obj (op ▫n)) := rfl

theorem H_obj_map {K : PrecubicalSet} {k m : ℕ} (g : ▫k ⟶ ▫m)
    (p : Equiv.Perm (Fin m) × K.obj (op ▫m)) :
    (H.obj K).map g.op p
      = (SHom.sortPerm (J.map g) p.1, K.map (SHom.sortFace (J.map g) p.1).op p.2) := rfl

/-! ## Comparison with mathlib's Kan extension -/

/-- **`symFree` is mathlib's left Kan extension functor** — Kan extensions are unique.
Spelled with `leftKanExtension` (what `lan` unfolds to): under the `lan` spelling the
`HasLeftKanExtension` argument stays a metavariable and mathlib's `IsLeftKanExtension`
instance never fires. -/
noncomputable def symFreeIsoLan : symFree ≅ J.op.lan := by
  refine NatIso.ofComponents (fun K => ?_) (fun {K L} f => ?_)
  · exact Functor.leftKanExtensionUnique (symFree.obj K) (symUnit K)
      (Functor.leftKanExtension J.op K) (Functor.leftKanExtensionUnit J.op K)
  · refine Functor.hom_ext_of_isLeftKanExtension _ (symUnit K) _ _ ?_
    dsimp only
    rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp, ← Category.assoc, ← Category.assoc,
      symUnit_naturality, Functor.leftKanExtensionUnique_hom, Functor.leftKanExtensionUnique_hom,
      Category.assoc]
    refine (congrArg (fun t => f ≫ t) (Functor.descOfIsLeftKanExtension_fac (symFree.obj L)
      (symUnit L) (J.op.leftKanExtension L) (J.op.leftKanExtensionUnit L))).trans ?_
    refine (Functor.descOfIsLeftKanExtension_fac (J.op.leftKanExtension K)
      (J.op.leftKanExtensionUnit K) (J.op.leftKanExtension L)
      (f ≫ J.op.leftKanExtensionUnit L)).symm.trans ?_
    exact congrArg (fun t => t ≫ Functor.whiskerLeft J.op (J.op.lan.map f))
      (Functor.descOfIsLeftKanExtension_fac (symFree.obj K) (symUnit K)
        (J.op.leftKanExtension K) (J.op.leftKanExtensionUnit K)).symm

/-- **`H` is mathlib's round trip** `J.op.lan ⋙ symRestrict`. -/
noncomputable def HIsoLan : H ≅ J.op.lan ⋙ symRestrict :=
  Functor.isoWhiskerRight symFreeIsoLan symRestrict

/-! ## The adjunction -/

/-- **`symFree ⊣ symRestrict`** — the universal property in its readable form.  `noncomputable`
only through mathlib's `lanAdjunction`; `symDesc` is the computable descent. -/
noncomputable def symFreeAdj : symFree ⊣ symRestrict :=
  Adjunction.ofNatIsoLeft (J.op.lanAdjunction Type) symFreeIsoLan.symm

/-- Its unit is the one this file runs on. -/
@[simp] theorem symFreeAdj_unit_app (K : PrecubicalSet) : symFreeAdj.unit.app K = symUnit K := by
  change (J.op.lanAdjunction Type).unit.app K ≫ symRestrict.map (symFreeIsoLan.symm.hom.app K)
      = symUnit K
  rw [Functor.lanAdjunction_unit]
  exact (Functor.descOfIsLeftKanExtension_fac (J.op.leftKanExtension K)
    (J.op.leftKanExtensionUnit K) (symFree.obj K) (𝟙 K ≫ symUnit K)).trans (Category.id_comp _)

end CubeChains
