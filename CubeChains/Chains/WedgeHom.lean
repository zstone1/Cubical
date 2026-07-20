import CubeChains.Chains.Segal

/-!
# Chains/WedgeHom

Maps out of a serial wedge are tuples of bead data: for a presheaf `P` with a single vertex,
`((⋁a).toPsh ⟶ P) ≃ ∏ᵢ P.obj (op ▫aᵢ)`.  Each pushout step `⋁(c :: rest) = □c ∨ ⋁rest`
contributes one Yoneda factor, and the gluing condition is vacuous because the two competing
maps `□⁰ ⟶ P` agree.  `wedgeHomProdAppend` is the monoidality: splitting a word splits the
tuple, compatibly with `wedgeInclL`/`wedgeInclR`.
-/

open CategoryTheory Opposite BPSet

namespace ChainCat

/-- The bead data of a word: one `c`-cell of `P` per bead `c`. -/
def wedgeHomProd (P : PrecubicalSet) : List ℕ+ → Type
  | [] => PUnit
  | c :: rest => P.obj (op ▫(c : ℕ)) × wedgeHomProd P rest

theorem wedgeHomProd_nil (P : PrecubicalSet) : wedgeHomProd P [] = PUnit := rfl

theorem wedgeHomProd_cons (P : PrecubicalSet) (c : ℕ+) (rest : List ℕ+) :
    wedgeHomProd P (c :: rest) = (P.obj (op ▫(c : ℕ)) × wedgeHomProd P rest) := rfl

/-- Yoneda at a bead, with the implicits pinned: an un-pinned `F` sends the unifier into `P`. -/
def cubeHomEquiv (P : PrecubicalSet) (n : ℕ) : ((□n).toPsh ⟶ P) ≃ P.obj (op ▫n) :=
  yonedaEquiv (X := ▫n) (F := P)

/-- Restrict a map out of `⋁a` to its beads. -/
def wedgeHomFwd (P : PrecubicalSet) : (a : List ℕ+) → ((⋁a).toPsh ⟶ P) → wedgeHomProd P a
  | [], _ => PUnit.unit
  | c :: rest, φ =>
      (cubeHomEquiv P (c : ℕ) (wedgeInl (□(c : ℕ)) (⋁rest) ≫ φ),
        wedgeHomFwd P rest (wedgeInr (□(c : ℕ)) (⋁rest) ≫ φ))

/-- Assemble bead data into a map out of `⋁a`; `pt` fixes the value on `⋁[] = □⁰`. -/
def wedgeHomBwd (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) :
    (a : List ℕ+) → wedgeHomProd P a → ((⋁a).toPsh ⟶ P)
  | [], _ => pt
  | c :: rest, x =>
      wedge2Desc ((cubeHomEquiv P (c : ℕ)).symm x.1) (wedgeHomBwd P pt hP rest x.2) (hP _ _)

@[simp] theorem wedgeHomFwd_nil (P : PrecubicalSet) (φ : (⋁([] : List ℕ+)).toPsh ⟶ P) :
    wedgeHomFwd P [] φ = PUnit.unit := rfl

@[simp] theorem wedgeHomFwd_cons (P : PrecubicalSet) (c : ℕ+) (rest : List ℕ+)
    (φ : (⋁(c :: rest)).toPsh ⟶ P) :
    wedgeHomFwd P (c :: rest) φ =
      (cubeHomEquiv P (c : ℕ) (wedgeInl (□(c : ℕ)) (⋁rest) ≫ φ),
        wedgeHomFwd P rest (wedgeInr (□(c : ℕ)) (⋁rest) ≫ φ)) := rfl

theorem wedgeHomBwd_cons (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) (c : ℕ+) (rest : List ℕ+)
    (x : wedgeHomProd P (c :: rest)) :
    wedgeHomBwd P pt hP (c :: rest) x =
      wedge2Desc ((cubeHomEquiv P (c : ℕ)).symm x.1) (wedgeHomBwd P pt hP rest x.2) (hP _ _) :=
  rfl

theorem wedgeHomBwd_fwd (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) :
    ∀ (a : List ℕ+) (φ : (⋁a).toPsh ⟶ P), wedgeHomBwd P pt hP a (wedgeHomFwd P a φ) = φ
  | [], φ => hP _ _
  | c :: rest, φ => by
      rw [wedgeHomFwd_cons, wedgeHomBwd_cons]
      refine wedge2_hom_ext ?_ ?_
      · rw [wedge2Desc_inl, Equiv.symm_apply_apply]
      · rw [wedge2Desc_inr]; exact wedgeHomBwd_fwd P pt hP rest _

theorem wedgeHomFwd_bwd (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) :
    ∀ (a : List ℕ+) (x : wedgeHomProd P a), wedgeHomFwd P a (wedgeHomBwd P pt hP a x) = x
  | [], _ => rfl
  | c :: rest, x => by
      rw [wedgeHomBwd_cons, wedgeHomFwd_cons, wedge2Desc_inl, wedge2Desc_inr,
        Equiv.apply_symm_apply, wedgeHomFwd_bwd P pt hP rest]
      exact rfl

/-- **Maps out of a serial wedge are tuples of bead data.**  `hP` (one vertex) makes every
gluing condition vacuous; `pt` is the value forced on the empty wedge `⋁[] = □⁰`. -/
def wedgeHomEquiv (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) (a : List ℕ+) :
    ((⋁a).toPsh ⟶ P) ≃ wedgeHomProd P a where
  toFun := wedgeHomFwd P a
  invFun := wedgeHomBwd P pt hP a
  left_inv := wedgeHomBwd_fwd P pt hP a
  right_inv := wedgeHomFwd_bwd P pt hP a

@[simp] theorem wedgeHomEquiv_apply (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) (a : List ℕ+) (φ : (⋁a).toPsh ⟶ P) :
    wedgeHomEquiv P pt hP a φ = wedgeHomFwd P a φ := rfl

@[simp] theorem wedgeHomEquiv_symm_apply (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) (a : List ℕ+) (x : wedgeHomProd P a) :
    (wedgeHomEquiv P pt hP a).symm x = wedgeHomBwd P pt hP a x := rfl

/-! ### Monoidality: splitting a word splits the tuple -/

/-- Bead data over a concatenation splits. -/
def wedgeHomProdAppend (P : PrecubicalSet) :
    (a₁ a₂ : List ℕ+) → wedgeHomProd P (a₁ ++ a₂) ≃ wedgeHomProd P a₁ × wedgeHomProd P a₂
  | [], a₂ => (Equiv.punitProd (wedgeHomProd P a₂)).symm
  | c :: rest, a₂ =>
      ((Equiv.refl (P.obj (op ▫(c : ℕ)))).prodCongr (wedgeHomProdAppend P rest a₂)).trans
        (Equiv.prodAssoc _ _ _).symm

@[simp] theorem wedgeHomProdAppend_nil (P : PrecubicalSet) (a₂ : List ℕ+)
    (x : wedgeHomProd P a₂) : wedgeHomProdAppend P [] a₂ x = (PUnit.unit, x) := rfl

@[simp] theorem wedgeHomProdAppend_cons (P : PrecubicalSet) (c : ℕ+) (rest a₂ : List ℕ+)
    (x : wedgeHomProd P (c :: (rest ++ a₂))) :
    wedgeHomProdAppend P (c :: rest) a₂ x =
      ((x.1, (wedgeHomProdAppend P rest a₂ x.2).1),
        (wedgeHomProdAppend P rest a₂ x.2).2) := rfl

/-- **The append law.**  Restricting to the two halves of `⋁(a₁ ++ a₂)` computes the split
of the bead tuple. -/
theorem wedgeHomFwd_append (P : PrecubicalSet) :
    ∀ (a₁ a₂ : List ℕ+) (φ : (⋁(a₁ ++ a₂)).toPsh ⟶ P),
      wedgeHomProdAppend P a₁ a₂ (wedgeHomFwd P (a₁ ++ a₂) φ)
        = (wedgeHomFwd P a₁ (wedgeInclL a₁ a₂ ≫ φ),
            wedgeHomFwd P a₂ (wedgeInclR a₁ a₂ ≫ φ))
  | [], a₂, φ => by
      have h : wedgeInclR ([] : List ℕ+) a₂ ≫ φ = φ := by
        rw [wedgeInclR_nil_left]; exact Category.id_comp φ
      -- `[] ++ a₂` and `a₂` differ only inside `≫`'s object slot, where `rw` cannot reach;
      -- `change` fixes the spelling once at default transparency.
      change (PUnit.unit, wedgeHomFwd P a₂ φ)
          = (PUnit.unit, wedgeHomFwd P a₂ (wedgeInclR ([] : List ℕ+) a₂ ≫ φ))
      rw [h]
  | c :: rest, a₂, φ => by
      have ih := wedgeHomFwd_append P rest a₂ (wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) ≫ φ)
      -- Both cocycles are re-associated *in term mode*: the reassociated composites carry
      -- `□c ∨ ⋁(rest ++ a₂)` in `≫`'s object slot where the goal carries `⋁(c :: rest ++ a₂)`,
      -- so `rw [Category.assoc]` cannot see them.
      have hL : wedgeInr (□(c : ℕ)) (⋁rest) ≫ wedgeInclL (c :: rest) a₂ ≫ φ
          = wedgeInclL rest a₂ ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) ≫ φ :=
        (wedgeInclL_cons_inr_assoc c rest a₂ φ).trans (Category.assoc _ _ _)
      have hR : wedgeInclR (c :: rest) a₂ ≫ φ
          = wedgeInclR rest a₂ ≫ wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) ≫ φ :=
        (congrArg (fun f => f ≫ φ) (wedgeInclR_cons c rest a₂)).trans (Category.assoc _ _ _)
      -- Same landmine: `(c :: rest) ++ a₂` is only `rfl`-equal to `c :: (rest ++ a₂)`.
      change ((cubeHomEquiv P (c : ℕ) (wedgeInl (□(c : ℕ)) (⋁(rest ++ a₂)) ≫ φ),
                (wedgeHomProdAppend P rest a₂ (wedgeHomFwd P (rest ++ a₂)
                  (wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) ≫ φ))).1),
              (wedgeHomProdAppend P rest a₂ (wedgeHomFwd P (rest ++ a₂)
                  (wedgeInr (□(c : ℕ)) (⋁(rest ++ a₂)) ≫ φ))).2)
            = ((cubeHomEquiv P (c : ℕ)
                    (wedgeInl (□(c : ℕ)) (⋁rest) ≫ wedgeInclL (c :: rest) a₂ ≫ φ),
                  wedgeHomFwd P rest (wedgeInr (□(c : ℕ)) (⋁rest) ≫ wedgeInclL (c :: rest) a₂ ≫ φ)),
                wedgeHomFwd P a₂ (wedgeInclR (c :: rest) a₂ ≫ φ))
      rw [wedgeInclL_cons_inl_assoc, hL, hR, ih]
      rfl

/-- The append law, transported through `wedgeHomEquiv`. -/
theorem wedgeHomEquiv_append (P : PrecubicalSet) (pt : (□0).toPsh ⟶ P)
    (hP : ∀ f g : (□0).toPsh ⟶ P, f = g) (a₁ a₂ : List ℕ+)
    (φ : (⋁(a₁ ++ a₂)).toPsh ⟶ P) :
    wedgeHomProdAppend P a₁ a₂ (wedgeHomEquiv P pt hP (a₁ ++ a₂) φ)
      = (wedgeHomEquiv P pt hP a₁ (wedgeInclL a₁ a₂ ≫ φ),
          wedgeHomEquiv P pt hP a₂ (wedgeInclR a₁ a₂ ≫ φ)) :=
  wedgeHomFwd_append P a₁ a₂ φ

end ChainCat
