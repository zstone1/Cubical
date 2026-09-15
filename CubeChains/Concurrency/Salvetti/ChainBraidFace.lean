import CubeChains.Concurrency.Executions.Elements
import CubeChains.Concurrency.Grading.OrderedPartition
import CubeChains.Machinery.Arrangement.BraidCovector
import CubeChains.Machinery.Arrangement.BraidPreorder
import CubeChains.Machinery.Arrangement.SalElements

/-!
# Concurrency/Salvetti/ChainBraidFace — chains of `□n` are faces of the braid COM

```
Ch (□n)  ≃  {ordered partition of Fin n}  ≃  COM.Face (braidCOM n)
        beadOf ↑                        ↑ blockMap (the normal form)
```
A chain's braid face is the covector of its ordered partition (`chFace`), and the face order is the
coarsening of partitions (`chFace_faceLE_iff`, the only place the covector's order is read), so the
partition dictionary of `Concurrency/Grading/OrderedPartition` is the base equivalence
`chFaceCatEquiv`.
-/

open CategoryTheory Opposite CubeChains CubeChain PrecubicalSet

namespace CubeChains

variable {n : ℕ}

/-- The braid face of a chain: the covector of its ordered partition `beadOf`. -/
def chFace (b : Ch (□n)) : COM.Face (braidCOM n) :=
  ⟨braidSign (fun q => ((beadOf b q : ℕ) : ℤ)), (fun q => ((beadOf b q : ℕ) : ℤ)), rfl⟩

/-- Escape hatch to the covector: `chFace` *is* `braidSign` of the ordered partition. -/
theorem chFace_val (b : Ch (□n)) :
    (chFace b).1 = braidSign (fun q => ((beadOf b q : ℕ) : ℤ)) := rfl

/-- **The face order between two chains *is* the coarsening of their ordered partitions** —
`braidSign_faceLE_iff` at the covector `chFace` is `braidSign` of. -/
theorem chFace_faceLE_iff {a b : Ch (□n)} : (chFace b).1 ⊑ (chFace a).1 ↔ BeadRefines a b := by
  change braidSign (fun q => ((beadOf b q : ℕ) : ℤ)) ⊑ braidSign (fun q => ((beadOf a q : ℕ) : ℤ))
    ↔ _
  rw [braidSign_faceLE_iff]
  simp only [ne_eq, Nat.cast_inj, Nat.cast_lt]
  refine ⟨fun h p q hpq => not_lt.mp fun hc => absurd ((h q p (Nat.ne_of_lt hc)).mp hc) (by omega),
    fun h i j hne => ⟨fun hlt => not_le.mp fun hc => absurd (h j i hc) (by omega),
      fun hlt => lt_of_le_of_ne (h i j hlt.le) hne⟩⟩

/-- **`chFace` is monotone under refinement:** `chFace b ⊑ chFace a` for a chain map `f : a ⟶ b`. -/
theorem chFace_faceLE {a b : Ch (□n)} (f : a ⟶ b) : (chFace b).1 ⊑ (chFace a).1 :=
  chFace_faceLE_iff.mpr (beadRefines_of_hom f)

/-- **Chains are braid faces**: forward the partition's covector, backward the chain of the
ordered partition `blockMap (covectorHeight X.1)` of the canonical height — computable both ways. -/
def chFaceEquiv : Ch (□n) ≃ COM.Face (braidCOM n) where
  toFun := chFace
  invFun X := blockChain (blockMap (covectorHeight X.1)) (blockMap_surjective _)
  left_inv := fun b => by
    change (ChainCat.chCubes (□n)).symm _ = b
    rw [Equiv.symm_apply_eq]
    apply eq_of_cubes
    rw [ChainCat.chCubes_val]
    have hsign : braidSign (covectorHeight (chFace b).1)
        = braidSign (fun q => ((beadOf b q : ℕ) : ℤ)) := braidSign_covectorHeight_mem (chFace b).2
    obtain ⟨hlen, hβval⟩ := blockMap_eq_of_braidSign (beadOf_surjective b) hsign.symm
    exact ofBlockMap_cubes_eq b (blockMap (covectorHeight (chFace b).1))
      (blockMap_surjective _) hlen hβval
  right_inv := fun X => by
    apply Subtype.ext
    have hfun : (fun q => ((beadOf (blockChain (blockMap (covectorHeight X.1))
          (blockMap_surjective _)) q : ℕ) : ℤ))
        = (fun q => ((blockMap (covectorHeight X.1) q : ℕ) : ℤ)) :=
      funext fun q => congrArg Nat.cast
        (beadOf_blockChain (blockMap (covectorHeight X.1)) (blockMap_surjective _) q)
    change braidSign (fun q => ((beadOf (blockChain (blockMap (covectorHeight X.1))
        (blockMap_surjective _)) q : ℕ) : ℤ)) = X.1
    rw [hfun, braidSign_blockMap]
    exact braidSign_covectorHeight_mem X.2

/-! ## The base equivalence `(Ch (□n))ᵒᵖ ≌ Face (braidCOM n)`

`chFace` is a bijection on objects and an order-iso on the thin hom-sets (`chFace_faceLE` forward,
`reflectHom` converse), so unit, counit and naturality are `Subsingleton.elim`. -/

instance : Quiver.IsThin (Ch (□n))ᵒᵖ := fun _ _ => inferInstance
instance : Quiver.IsThin (COM.Face (braidCOM n)) := fun _ _ => inferInstance

/-- The forward functor: a chain to its braid face, a refinement to the face-order relation. -/
def chFaceFunctor : (Ch (□n))ᵒᵖ ⥤ COM.Face (braidCOM n) where
  obj X := chFace X.unop
  map f := homOfLE (chFace_faceLE f.unop)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The inverse functor: a face to its reconstructed chain, an order relation to `reflectHom`. -/
def chFaceInverse : COM.Face (braidCOM n) ⥤ (Ch (□n))ᵒᵖ where
  obj Z := op (chFaceEquiv.symm Z)
  map {Z W} g := (reflectHom (a := chFaceEquiv.symm W) (b := chFaceEquiv.symm Z)
    (chFace_faceLE_iff.mp (by
      rw [show chFace (chFaceEquiv.symm Z) = Z from chFaceEquiv.apply_symm_apply Z,
        show chFace (chFaceEquiv.symm W) = W from chFaceEquiv.apply_symm_apply W]
      exact leOfHom g))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The base equivalence** `(Ch (□n))ᵒᵖ ≌ Face (braidCOM n)`.  Consumed by `Ch⋆ ≌ Sal`. -/
def chFaceCatEquiv : (Ch (□n))ᵒᵖ ≌ COM.Face (braidCOM n) where
  functor := chFaceFunctor
  inverse := chFaceInverse
  unitIso := NatIso.ofComponents
    (fun X => eqToIso (congrArg op (chFaceEquiv.symm_apply_apply X.unop).symm))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun Z => eqToIso (chFaceEquiv.apply_symm_apply Z))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end CubeChains
