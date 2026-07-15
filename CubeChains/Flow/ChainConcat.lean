import CubeChains.Chains.Segal

/-!
# Flow/ChainConcat — endpoint-parameterised chains and their concatenation

`BPSet.repoint K u v` re-points `K` at a chosen pair of vertices, so `Ch (K.repoint u v)` is
"the cube chains of `K` from `u` to `v`" with no new foundations.  Concatenation

    chConcatAt K u v w : Ch (K.repoint u v) × Ch (K.repoint v w) ⥤ Ch (K.repoint u w)

is `Chains/Segal`'s `chConcat` followed by the fold `(K;u,v) ∨ (K;v,w) ⟶ (K;u,w)`.  It is
**strictly** associative and unital: dimension sequences concatenate by `List.append`.

No side conditions (`NonSelfLinked`/`AdmitsAltitude` are needed only for the `RefineObj ≌ Ch`
comparison, which this file never touches).

Gotcha: `⋁((A ++ B) ++ C)` and `⋁(A ++ (B ++ C))` are only *propositionally* equal, so
associativity is stated across the transport `wedgeCast (List.append_assoc ..)`.  Everything is
proved from the two half-inclusions `wedgeInclL`/`wedgeInclR` and their extensionality
(`concat_hom_ext`).
-/

open CategoryTheory CategoryTheory.Limits Opposite BPSet

namespace CubeChains

open ChainCat CubeChain

/-! ### Transporting a wedge along an equality of dimension sequences -/

/-- The canonical iso `⋁d₁ ⟶ ⋁d₂` of an equality of dimension sequences. -/
noncomputable def wedgeCast {d₁ d₂ : List ℕ+} (h : d₁ = d₂) : ⋁d₁ ⟶ ⋁d₂ :=
  eqToHom (congrArg BPSet.serialWedge h)

theorem wedgeCast_rfl {d : List ℕ+} (h : d = d) : (wedgeCast h).hom = 𝟙 ((⋁d).toPsh) := rfl

theorem wedgeCast_self_symm {d₁ d₂ : List ℕ+} (h : d₁ = d₂) :
    (wedgeCast h).hom ≫ (wedgeCast h.symm).hom = 𝟙 _ := by
  subst h; rfl

theorem wedgeCast_symm_self {d₁ d₂ : List ℕ+} (h : d₁ = d₂) :
    (wedgeCast h.symm).hom ≫ (wedgeCast h).hom = 𝟙 _ := by
  subst h; rfl

/-- A wedge transport is bi-pointed, so it carries the final vertex to the final vertex. -/
theorem wedgeCast_finalVertex {d₁ d₂ : List ℕ+} (h : d₁ = d₂) :
    (⋁d₁).finalVertex ≫ (wedgeCast h).hom = (⋁d₂).finalVertex := by
  subst h; exact Category.comp_id _

/-- `wedgeCast` of a `cons`, read on the head cube. -/
@[reassoc] theorem wedgeCast_cons_inl {d₁ d₂ : List ℕ+} (h : d₁ = d₂) (n : ℕ+) :
    Glue.inl (□(n : ℕ)).finalVertex (⋁d₁).initVertex
        ≫ (wedgeCast (congrArg (n :: ·) h)).hom
      = Glue.inl (□(n : ℕ)).finalVertex (⋁d₂).initVertex := by
  subst h; exact Category.comp_id _

/-- `wedgeCast` of a `cons`, read on the tail wedge. -/
@[reassoc] theorem wedgeCast_cons_inr {d₁ d₂ : List ℕ+} (h : d₁ = d₂) (n : ℕ+) :
    Glue.inr (□(n : ℕ)).finalVertex (⋁d₁).initVertex
        ≫ (wedgeCast (congrArg (n :: ·) h)).hom
      = (wedgeCast h).hom ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁d₂).initVertex := by
  subst h
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-! ### The half-inclusions on a `cons` -/

/-- Head-block computation rule for `wedgeInclL`. -/
@[reassoc] theorem inl_wedgeInclL_cons (n : ℕ+) (da' db : List ℕ+) :
    Glue.inl (□(n : ℕ)).finalVertex (⋁da').initVertex ≫ wedgeInclL (n :: da') db
      = Glue.inl (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex := by
  rw [wedgeInclL_cons]; exact Glue.inl_desc _ _ _

/-- Tail-block computation rule for `wedgeInclL`. -/
@[reassoc] theorem inr_wedgeInclL_cons (n : ℕ+) (da' db : List ℕ+) :
    Glue.inr (□(n : ℕ)).finalVertex (⋁da').initVertex ≫ wedgeInclL (n :: da') db
      = wedgeInclL da' db ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex := by
  rw [wedgeInclL_cons]; exact Glue.inr_desc _ _ _

/-- The `cons` unfolding of `wedgeInclR`. -/
theorem wedgeInclR_cons (n : ℕ+) (da' db : List ℕ+) :
    wedgeInclR (n :: da') db
      = wedgeInclR da' db ≫ Glue.inr (□(n : ℕ)).finalVertex (⋁(da' ++ db)).initVertex :=
  rfl

/-! ### The three associativity compatibilities of the half-inclusions

Write `α := wedgeCast (List.append_assoc A B C) : ⋁((A ++ B) ++ C) ⟶ ⋁(A ++ (B ++ C))`.  Each of
the three blocks of `(A ++ B) ++ C` reaches `A ++ (B ++ C)` through `α` as expected. -/

/-- `A`-block. -/
theorem wedgeInclL_assoc : ∀ (A B C : List ℕ+),
    wedgeInclL A B ≫ wedgeInclL (A ++ B) C ≫ (wedgeCast (List.append_assoc A B C)).hom
      = wedgeInclL A (B ++ C)
  | [], B, C => by
      have hid : (wedgeCast (List.append_assoc ([] : List ℕ+) B C)).hom
          = 𝟙 ((⋁(B ++ C)).toPsh) := rfl
      rw [hid]
      erw [Category.comp_id]
      exact wedgeInclL_initVertex B C
  | n :: A', B, C => by
      have hcast : (wedgeCast (List.append_assoc (n :: A') B C)).hom
          = (wedgeCast (congrArg (n :: ·) (List.append_assoc A' B C))).hom := rfl
      rw [hcast]
      refine Glue.hom_ext ?_ ?_
      · erw [inl_wedgeInclL_cons_assoc n A' B, inl_wedgeInclL_cons_assoc n (A' ++ B) C,
          wedgeCast_cons_inl (List.append_assoc A' B C) n, inl_wedgeInclL_cons n A' (B ++ C)]
      · erw [inr_wedgeInclL_cons_assoc n A' B, Category.assoc,
          inr_wedgeInclL_cons_assoc n (A' ++ B) C, Category.assoc,
          wedgeCast_cons_inr (List.append_assoc A' B C) n,
          reassoc_of% (wedgeInclL_assoc A' B C)]
        exact (inr_wedgeInclL_cons n A' (B ++ C)).symm

/-- `B`-block. -/
theorem wedgeInclR_wedgeInclL_assoc : ∀ (A B C : List ℕ+),
    wedgeInclR A B ≫ wedgeInclL (A ++ B) C ≫ (wedgeCast (List.append_assoc A B C)).hom
      = wedgeInclL B C ≫ wedgeInclR A (B ++ C)
  | [], B, C => by
      have hid : (wedgeCast (List.append_assoc ([] : List ℕ+) B C)).hom
          = 𝟙 ((⋁(B ++ C)).toPsh) := rfl
      rw [hid]
      erw [Category.comp_id]
      change 𝟙 _ ≫ wedgeInclL B C = wedgeInclL B C ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  | n :: A', B, C => by
      have hcast : (wedgeCast (List.append_assoc (n :: A') B C)).hom
          = (wedgeCast (congrArg (n :: ·) (List.append_assoc A' B C))).hom := rfl
      rw [hcast, wedgeInclR_cons n A' B]
      erw [Category.assoc, inr_wedgeInclL_cons_assoc n (A' ++ B) C, Category.assoc,
        wedgeCast_cons_inr (List.append_assoc A' B C) n,
        reassoc_of% (wedgeInclR_wedgeInclL_assoc A' B C), wedgeInclR_cons n A' (B ++ C)]
      rfl

/-- `C`-block. -/
theorem wedgeInclR_assoc : ∀ (A B C : List ℕ+),
    wedgeInclR (A ++ B) C ≫ (wedgeCast (List.append_assoc A B C)).hom
      = wedgeInclR B C ≫ wedgeInclR A (B ++ C)
  | [], B, C => by
      have hid : (wedgeCast (List.append_assoc ([] : List ℕ+) B C)).hom
          = 𝟙 ((⋁(B ++ C)).toPsh) := rfl
      rw [hid]
      erw [Category.comp_id]
  | n :: A', B, C => by
      have hcast : (wedgeCast (List.append_assoc (n :: A') B C)).hom
          = (wedgeCast (congrArg (n :: ·) (List.append_assoc A' B C))).hom := rfl
      have hsrc : wedgeInclR ((n :: A') ++ B) C = wedgeInclR (n :: (A' ++ B)) C := rfl
      rw [hcast, hsrc, wedgeInclR_cons n (A' ++ B) C]
      erw [Category.assoc, wedgeCast_cons_inr (List.append_assoc A' B C) n,
        reassoc_of% (wedgeInclR_assoc A' B C), wedgeInclR_cons n A' (B ++ C)]
      rfl

/-! ### The right-unit transport (`A ++ [] = A` is not definitional) -/

/-- `wedgeInclL A []` is inverse to the transport of `A ++ [] = A`. -/
theorem wedgeInclL_append_nil : ∀ (A : List ℕ+),
    wedgeInclL A [] ≫ (wedgeCast (List.append_nil A)).hom = 𝟙 ((⋁A).toPsh)
  | [] => by
      have hid : (wedgeCast (List.append_nil ([] : List ℕ+))).hom
          = 𝟙 ((⋁([] : List ℕ+)).toPsh) := rfl
      rw [hid]
      erw [Category.comp_id]
      exact cube0_initVertex_eq_id
  | n :: A' => by
      have hcast : (wedgeCast (List.append_nil (n :: A'))).hom
          = (wedgeCast (congrArg (n :: ·) (List.append_nil A'))).hom := rfl
      rw [hcast]
      refine Glue.hom_ext ?_ ?_
      · erw [inl_wedgeInclL_cons_assoc n A' [],
          wedgeCast_cons_inl (List.append_nil A') n, Category.comp_id]
      · erw [inr_wedgeInclL_cons_assoc n A' [], Category.assoc,
          wedgeCast_cons_inr (List.append_nil A') n,
          reassoc_of% (wedgeInclL_append_nil A'), Category.comp_id]

/-- `wedgeInclR A []` is the final vertex of the appended wedge. -/
theorem wedgeInclR_append_nil (A : List ℕ+) :
    wedgeInclR A [] = (⋁(A ++ [])).finalVertex := by
  have h := wedgeInclR_finalVertex A []
  rw [show (⋁([] : List ℕ+)).finalVertex = 𝟙 _ from cube0_finalVertex_eq_id] at h
  erw [Category.id_comp] at h
  exact h

/-! ## The fold map and the concatenation functor -/

variable {K : BPSet}

/-- The fold `(K;u,v) ∨ (K;v,w) ⟶ (K;u,w)`: both halves are `K` itself, glued at `v`. -/
noncomputable def foldWedge (K : BPSet) (u v w : K.cells 0) :
    wedge2 (K.repoint u v) (K.repoint v w) ⟶ K.repoint u w where
  -- the junction condition is `rfl`: both legs are the vertex map of `v`
  hom := Glue.desc (𝟙 K.toPsh) (𝟙 K.toPsh) rfl
  app_init := by
    rw [show (wedge2 (K.repoint u v) (K.repoint v w)).init
      = (Glue.inl (K.repoint u v).finalVertex (K.repoint v w).initVertex)⟪0⟫
          (K.repoint u v).init from rfl]
    exact inl_desc_app _
  app_final := by
    rw [show (wedge2 (K.repoint u v) (K.repoint v w)).final
      = (Glue.inr (K.repoint u v).finalVertex (K.repoint v w).initVertex)⟪0⟫
          (K.repoint v w).final from rfl]
    exact inr_desc_app _

@[simp] theorem inl_foldWedge (K : BPSet) (u v w : K.cells 0) :
    Glue.inl (K.repoint u v).finalVertex (K.repoint v w).initVertex
        ≫ (foldWedge K u v w).hom
      = 𝟙 K.toPsh :=
  Glue.inl_desc _ _ _

@[simp] theorem inr_foldWedge (K : BPSet) (u v w : K.cells 0) :
    Glue.inr (K.repoint u v).finalVertex (K.repoint v w).initVertex
        ≫ (foldWedge K u v w).hom
      = 𝟙 K.toPsh :=
  Glue.inr_desc _ _ _

/-- **Concatenation of chains** `Ch (K;u,v) × Ch (K;v,w) ⥤ Ch (K;u,w)`: Segal concatenation into
the wedge, then fold the wedge back onto `K`. -/
noncomputable def chConcatAt (K : BPSet) (u v w : K.cells 0) :
    Ch (K.repoint u v) × Ch (K.repoint v w) ⥤ Ch (K.repoint u w) :=
  chConcat (K.repoint u v) (K.repoint v w) ⋙ ChainCat.pushforward (foldWedge K u v w)

/-- Concatenation of cube chains: `dims` append, classifying maps glue at the junction. -/
noncomputable def chConc {u v w : K.cells 0}
    (a : Ch (K.repoint u v)) (b : Ch (K.repoint v w)) : Ch (K.repoint u w) :=
  (chConcatAt K u v w).obj (a, b)

@[simp] theorem chConc_dims {u v w : K.cells 0}
    (a : Ch (K.repoint u v)) (b : Ch (K.repoint v w)) :
    (chConc a b).dims = a.dims ++ b.dims := rfl

@[simp] theorem chConcatAt_obj {u v w : K.cells 0}
    (ab : Ch (K.repoint u v) × Ch (K.repoint v w)) :
    (chConcatAt K u v w).obj ab = chConc ab.1 ab.2 := rfl

@[simp] theorem chConcatAt_map_φ {u v w : K.cells 0}
    {ab ab' : Ch (K.repoint u v) × Ch (K.repoint v w)} (fg : ab ⟶ ab') :
    Hom.φ ((chConcatAt K u v w).map fg) = concatHomφ fg.1 fg.2 := rfl

/-! ### The defining restrictions of a concatenated chain -/

theorem chConc_map_inclL {u v w : K.cells 0}
    (a : Ch (K.repoint u v)) (b : Ch (K.repoint v w)) :
    wedgeInclL a.dims b.dims ≫ (chConc a b).map.hom = a.map.hom := by
  change wedgeInclL a.dims b.dims
      ≫ ((concatChainMap _ _ a b) ≫ foldWedge K u v w).hom = a.map.hom
  rw [comp_hom, ← Category.assoc, concatChainMap_inclL]
  change (a.map.hom ≫ Glue.inl (K.repoint u v).finalVertex (K.repoint v w).initVertex)
      ≫ (foldWedge K u v w).hom = a.map.hom
  rw [Category.assoc, inl_foldWedge]
  exact Category.comp_id _

theorem chConc_map_inclR {u v w : K.cells 0}
    (a : Ch (K.repoint u v)) (b : Ch (K.repoint v w)) :
    wedgeInclR a.dims b.dims ≫ (chConc a b).map.hom = b.map.hom := by
  change wedgeInclR a.dims b.dims
      ≫ ((concatChainMap _ _ a b) ≫ foldWedge K u v w).hom = b.map.hom
  rw [comp_hom, ← Category.assoc, concatChainMap_inclR]
  change (b.map.hom ≫ Glue.inr (K.repoint u v).finalVertex (K.repoint v w).initVertex)
      ≫ (foldWedge K u v w).hom = b.map.hom
  rw [Category.assoc, inr_foldWedge]
  exact Category.comp_id _

/-! ### Objects of `Ch K` are pinned by `dims` + classifying map -/

/-- Chain objects with equal dimension sequences and matching classifying maps (across the
transport) are equal. -/
theorem Obj.ext_cast {L : BPSet} : ∀ {a b : Ch L} (h : a.dims = b.dims),
    (wedgeCast h).hom ≫ b.map.hom = a.map.hom → a = b := by
  rintro ⟨d₁, m₁⟩ ⟨d₂, m₂⟩ h hm
  dsimp only at h
  subst h
  exact congrArg (ChainCat.Obj.mk d₁)
    (BPSet.hom_ext ((Category.id_comp m₂.hom).symm.trans hm)).symm

/-! ### Strict associativity -/

/-- **Associativity of chain concatenation** (strict, modulo the `List.append_assoc` transport). -/
theorem chConc_assoc {u v w x : K.cells 0}
    (a : Ch (K.repoint u v)) (b : Ch (K.repoint v w)) (c : Ch (K.repoint w x)) :
    chConc (chConc a b) c = chConc a (chConc b c) := by
  refine Obj.ext_cast (List.append_assoc a.dims b.dims c.dims) ?_
  refine concat_hom_ext (a.dims ++ b.dims) c.dims _ _ ?_ ?_
  · refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
    · erw [reassoc_of% (wedgeInclL_assoc a.dims b.dims c.dims),
        chConc_map_inclL a (chConc b c), chConc_map_inclL (chConc a b) c, chConc_map_inclL a b]
    · erw [reassoc_of% (wedgeInclR_wedgeInclL_assoc a.dims b.dims c.dims),
        chConc_map_inclR a (chConc b c), chConc_map_inclL b c,
        chConc_map_inclL (chConc a b) c, chConc_map_inclR a b]
  · erw [reassoc_of% (wedgeInclR_assoc a.dims b.dims c.dims),
      chConc_map_inclR a (chConc b c), chConc_map_inclR b c, chConc_map_inclR (chConc a b) c]

/-! ### Strict unitality -/

/-- The empty chain at a vertex — the identity 1-cell. -/
noncomputable def chId (K : BPSet) (v : K.cells 0) : Ch (K.repoint v v) where
  dims := []
  map :=
    { hom := yonedaEquiv.symm v
      app_init := by
        rw [show (⋁([] : List ℕ+)).init = (𝟙 ▫0 : (□0).cells 0) from
          Subsingleton.elim (α := (□0).cells 0) _ _]
        exact (yonedaEquiv_apply (yonedaEquiv.symm v)).symm.trans
          (yonedaEquiv.apply_symm_apply v)
      app_final := by
        rw [show (⋁([] : List ℕ+)).final = (𝟙 ▫0 : (□0).cells 0) from
          Subsingleton.elim (α := (□0).cells 0) _ _]
        exact (yonedaEquiv_apply (yonedaEquiv.symm v)).symm.trans
          (yonedaEquiv.apply_symm_apply v) }

@[simp] theorem chId_dims (K : BPSet) (v : K.cells 0) : (chId K v).dims = [] := rfl

@[simp] theorem chId_map_hom (K : BPSet) (v : K.cells 0) :
    (chId K v).map.hom = yonedaEquiv.symm v := rfl

/-- **Left unit** (definitional on `dims`: `[] ++ B = B`). -/
theorem chConc_id_left {v w : K.cells 0} (b : Ch (K.repoint v w)) :
    chConc (chId K v) b = b := by
  refine Obj.ext_cast (List.nil_append b.dims) ?_
  -- `wedgeInclR [] _ = 𝟙` and `wedgeCast` of a `rfl`-list-equality is `𝟙`, both definitionally
  have h : (chConc (chId K v) b).map.hom = b.map.hom := chConc_map_inclR (chId K v) b
  exact h.symm

/-- **Right unit** (needs the `A ++ [] = A` transport). -/
theorem chConc_id_right {u v : K.cells 0} (a : Ch (K.repoint u v)) :
    chConc a (chId K v) = a := by
  refine Obj.ext_cast (List.append_nil a.dims) ?_
  refine concat_hom_ext a.dims [] _ _ ?_ ?_
  · erw [reassoc_of% (wedgeInclL_append_nil a.dims), chConc_map_inclL a (chId K v)]
  · erw [chConc_map_inclR a (chId K v), ← Category.assoc, wedgeInclR_append_nil,
      wedgeCast_finalVertex]
    calc (⋁a.dims).finalVertex ≫ a.map.hom
        = yonedaEquiv.symm (a.map.hom⟪0⟫ ((⋁a.dims).final)) :=
          yonedaEquiv_symm_naturality_right ▫0 a.map.hom ((⋁a.dims).final)
      _ = (chId K v).map.hom := by rw [a.map.app_final]; rfl

/-! ## Strictness on morphisms: `chConcatAt` as a strictly associative, strictly unital functor

The object equalities above are upgraded to *functor* equalities.  The wedge transports show up as
`eqToHom`s in `Ch`; `eqToHom_φ` turns them back into `wedgeCast`s, and the three inverted
half-inclusion compatibilities below let `concat_hom_ext` finish. -/

/-- The underlying wedge map of an `eqToHom` of chains is the transport of its dimension
sequences. -/
theorem eqToHom_φ {L : BPSet} {X Y : Ch L} (p : X = Y) :
    Hom.φ (eqToHom p) = wedgeCast (congrArg ChainCat.Obj.dims p) := by
  subst p; rfl

/-- `A`-block, inverted. -/
theorem wedgeInclL_assoc_symm (A B C : List ℕ+) :
    wedgeInclL A (B ++ C) ≫ (wedgeCast (List.append_assoc A B C).symm).hom
      = wedgeInclL A B ≫ wedgeInclL (A ++ B) C := by
  rw [← wedgeInclL_assoc A B C, Category.assoc, Category.assoc, wedgeCast_self_symm,
    Category.comp_id]

/-- `B`-block, inverted. -/
theorem wedgeInclR_wedgeInclL_assoc_symm (A B C : List ℕ+) :
    wedgeInclL B C ≫ wedgeInclR A (B ++ C) ≫ (wedgeCast (List.append_assoc A B C).symm).hom
      = wedgeInclR A B ≫ wedgeInclL (A ++ B) C := by
  rw [← Category.assoc, ← wedgeInclR_wedgeInclL_assoc A B C, Category.assoc, Category.assoc,
    wedgeCast_self_symm, Category.comp_id]

/-- `C`-block, inverted. -/
theorem wedgeInclR_assoc_symm (A B C : List ℕ+) :
    wedgeInclR B C ≫ wedgeInclR A (B ++ C) ≫ (wedgeCast (List.append_assoc A B C).symm).hom
      = wedgeInclR (A ++ B) C := by
  rw [← Category.assoc, ← wedgeInclR_assoc A B C, Category.assoc, wedgeCast_self_symm,
    Category.comp_id]

/-- `wedgeInclL A []` inverted: it *is* the transport of `A ++ [] = A`. -/
theorem wedgeInclL_append_nil_symm (A : List ℕ+) :
    (wedgeCast (List.append_nil A).symm).hom = wedgeInclL A [] := by
  calc (wedgeCast (List.append_nil A).symm).hom
      = 𝟙 _ ≫ (wedgeCast (List.append_nil A).symm).hom := (Category.id_comp _).symm
    _ = (wedgeInclL A [] ≫ (wedgeCast (List.append_nil A)).hom)
          ≫ (wedgeCast (List.append_nil A).symm).hom := by rw [wedgeInclL_append_nil]
    _ = wedgeInclL A [] ≫ ((wedgeCast (List.append_nil A)).hom
          ≫ (wedgeCast (List.append_nil A).symm).hom) := Category.assoc _ _ _
    _ = wedgeInclL A [] := by rw [wedgeCast_self_symm]; exact Category.comp_id _

variable {u v w x : K.cells 0}

/-- `chConcatAt` on morphisms, folded. -/
noncomputable def chConcMor {a a' : Ch (K.repoint u v)} {b b' : Ch (K.repoint v w)}
    (f : a ⟶ a') (g : b ⟶ b') : chConc a b ⟶ chConc a' b' :=
  (chConcatAt K u v w).map (f, g)

@[simp] theorem chConcMor_φ {a a' : Ch (K.repoint u v)} {b b' : Ch (K.repoint v w)}
    (f : a ⟶ a') (g : b ⟶ b') : Hom.φ (chConcMor f g) = concatHomφ f g := rfl

theorem chConcMor_id (a : Ch (K.repoint u v)) (b : Ch (K.repoint v w)) :
    chConcMor (𝟙 a) (𝟙 b) = 𝟙 (chConc a b) := by
  apply ChainCat.hom_ext'
  rw [chConcMor_φ, id_φ]
  exact concatHomφ_id a b

theorem chConcMor_comp {a a' a'' : Ch (K.repoint u v)} {b b' b'' : Ch (K.repoint v w)}
    (f₁ : a ⟶ a') (f₂ : a' ⟶ a'') (g₁ : b ⟶ b') (g₂ : b' ⟶ b'') :
    chConcMor (f₁ ≫ f₂) (g₁ ≫ g₂) = chConcMor f₁ g₁ ≫ chConcMor f₂ g₂ := by
  apply ChainCat.hom_ext'
  rw [chConcMor_φ, comp_φ, chConcMor_φ, chConcMor_φ]
  exact concatHomφ_comp f₁ f₂ g₁ g₂

/-- A bi-pointed map carries the final vertex to the final vertex (vertex-map form). -/
theorem finalVertex_comp {X Y : BPSet} (e : X ⟶ Y) : X.finalVertex ≫ e.hom = Y.finalVertex :=
  (yonedaEquiv_symm_naturality_right ▫0 e.hom X.final).trans
    (congrArg yonedaEquiv.symm e.app_final)

/-- **Associativity of chain concatenation on morphisms.** -/
theorem chConcMor_assoc {a a' : Ch (K.repoint u v)} {b b' : Ch (K.repoint v w)}
    {c c' : Ch (K.repoint w x)} (f : a ⟶ a') (g : b ⟶ b') (h : c ⟶ c') :
    chConcMor (chConcMor f g) h
      = eqToHom (chConc_assoc a b c) ≫ chConcMor f (chConcMor g h)
        ≫ eqToHom (chConc_assoc a' b' c').symm := by
  apply ChainCat.hom_ext'
  rw [comp_φ, comp_φ, chConcMor_φ, chConcMor_φ, eqToHom_φ, eqToHom_φ]
  have hd : (wedgeCast (congrArg ChainCat.Obj.dims (chConc_assoc a b c))).hom
      = (wedgeCast (List.append_assoc a.dims b.dims c.dims)).hom := rfl
  have hd' : (wedgeCast (congrArg ChainCat.Obj.dims (chConc_assoc a' b' c').symm)).hom
      = (wedgeCast (List.append_assoc a'.dims b'.dims c'.dims).symm).hom := rfl
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, hd, hd']
  refine concat_hom_ext (a.dims ++ b.dims) c.dims _ _ ?_ ?_
  · refine concat_hom_ext a.dims b.dims _ _ ?_ ?_
    · erw [concatHomφ_inclL (chConcMor f g) h, reassoc_of% (concatHomφ_inclL f g),
        reassoc_of% (wedgeInclL_assoc a.dims b.dims c.dims),
        reassoc_of% (concatHomφ_inclL f (chConcMor g h)),
        wedgeInclL_assoc_symm a'.dims b'.dims c'.dims]
      rfl
    · erw [concatHomφ_inclL (chConcMor f g) h, reassoc_of% (concatHomφ_inclR f g),
        reassoc_of% (wedgeInclR_wedgeInclL_assoc a.dims b.dims c.dims),
        reassoc_of% (concatHomφ_inclR f (chConcMor g h)),
        reassoc_of% (concatHomφ_inclL g h),
        wedgeInclR_wedgeInclL_assoc_symm a'.dims b'.dims c'.dims]
      rfl
  · erw [concatHomφ_inclR (chConcMor f g) h,
      reassoc_of% (wedgeInclR_assoc a.dims b.dims c.dims),
      reassoc_of% (concatHomφ_inclR f (chConcMor g h)),
      reassoc_of% (concatHomφ_inclR g h),
      wedgeInclR_assoc_symm a'.dims b'.dims c'.dims]
    rfl

/-- **Left unit on morphisms.** -/
theorem chConcMor_id_left {b b' : Ch (K.repoint v w)} (g : b ⟶ b') :
    chConcMor (𝟙 (chId K v)) g
      = eqToHom (chConc_id_left b) ≫ g ≫ eqToHom (chConc_id_left b').symm := by
  apply ChainCat.hom_ext'
  rw [comp_φ, comp_φ, chConcMor_φ, eqToHom_φ, eqToHom_φ]
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom]
  -- both `wedgeCast`s and `wedgeInclR [] _` are `𝟙` definitionally
  exact concatHomφ_inclR (𝟙 (chId K v)) g

/-- **Right unit on morphisms.** -/
theorem chConcMor_id_right {a a' : Ch (K.repoint u v)} (f : a ⟶ a') :
    chConcMor f (𝟙 (chId K v))
      = eqToHom (chConc_id_right a) ≫ f ≫ eqToHom (chConc_id_right a').symm := by
  apply ChainCat.hom_ext'
  rw [comp_φ, comp_φ, chConcMor_φ, eqToHom_φ, eqToHom_φ]
  have hd : (wedgeCast (congrArg ChainCat.Obj.dims (chConc_id_right a))).hom
      = (wedgeCast (List.append_nil a.dims)).hom := rfl
  have hd' : (wedgeCast (congrArg ChainCat.Obj.dims (chConc_id_right a').symm)).hom
      = (wedgeCast (List.append_nil a'.dims).symm).hom := rfl
  apply BPSet.hom_ext
  rw [comp_hom, comp_hom, hd, hd']
  refine concat_hom_ext a.dims [] _ _ ?_ ?_
  · erw [concatHomφ_inclL f (𝟙 (chId K v)),
      reassoc_of% (wedgeInclL_append_nil a.dims), wedgeInclL_append_nil_symm a'.dims]
    rfl
  · erw [concatHomφ_inclR f (𝟙 (chId K v)), Category.id_comp, wedgeInclR_append_nil a'.dims,
      wedgeInclR_append_nil a.dims,
      reassoc_of% (wedgeCast_finalVertex (List.append_nil a.dims)),
      reassoc_of% (finalVertex_comp (ChainCat.Hom.φ f)),
      wedgeCast_finalVertex (List.append_nil a'.dims).symm]

end CubeChains
