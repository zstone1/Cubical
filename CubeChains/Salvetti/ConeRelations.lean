import CubeChains.Salvetti.SalExec

/-!
# Salvetti/ConeRelations — both Artin relations are one lemma

The relation half of a section `Artin ⟶ FreeGroupoid (Ch⋆ (□ⁿ))`.  Working on the `Sal` side
(`braidSalEquiv`), where the order is `⊑` of sign vectors and the cone lemma needs no subcategory.

`coneCmp hy hz : mk y ⟶ mk z` compares two objects **through a chosen lower bound**; `coneCmp_trans` says
such comparisons telescope, which is the cone lemma in the form a caller wants.

A tope absorbs (`comp_eq_left_of_isTope`), so *every* tope over a face `X` lies over the single cell
`(X, T₀)` — hence `cross`, and both Artin relations are `cross_trans` twice (`cross_square` at a
two-2-block face, `cross_hexagon` at a 3-block face).  `cross_eq_coneCmp_of_le` is what licenses reading
each factor as the geometric wall crossing, and it is also why `Δ²` survives: its apexes reverse a
pair the witness separates, so they are not over the witness.  Nothing about `n` enters.
-/

open CategoryTheory Opposite CubeChain BPSet SignType

namespace CategoryTheory.FreeGroupoid

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Comparison through a lower bound -/

/-- The comparison of `y` and `z` seen from a common lower bound `b`. -/
noncomputable def coneCmp {b y z : C} (hy : b ⟶ y) (hz : b ⟶ z) : mk y ⟶ mk z :=
  inv (homMk hy) ≫ homMk hz

@[simp] theorem coneCmp_self {b y : C} (hy : b ⟶ y) : coneCmp hy hy = 𝟙 _ := IsIso.inv_hom_id _

/-- **Comparisons under one basepoint telescope.**  The cone lemma in usable form: a route through
`↑b` collapses to its endpoints, so two routes with the same endpoints agree. -/
theorem coneCmp_trans {b y z w : C} (hy : b ⟶ y) (hz : b ⟶ z) (hw : b ⟶ w) :
    coneCmp hy hz ≫ coneCmp hz hw = coneCmp hy hw := by
  simp only [coneCmp, Category.assoc, IsIso.hom_inv_id_assoc]

@[simp] theorem inv_coneCmp {b y z : C} (hy : b ⟶ y) (hz : b ⟶ z) : inv (coneCmp hy hz) = coneCmp hz hy := by
  simp only [coneCmp, IsIso.inv_comp, IsIso.inv_inv]

/-- **A span is a comparison from anything under its apex**, so the basepoint may be pushed down
along `hb` freely.  (It may *not* be pushed sideways — that failure is exactly `π₁`.) -/
theorem coneCmp_comp {b p y z : C} (hb : b ⟶ p) (hy : p ⟶ y) (hz : p ⟶ z) :
    coneCmp (hb ≫ hy) (hb ≫ hz) = coneCmp hy hz := by
  simp only [coneCmp, homMk, Functor.map_comp, IsIso.inv_comp, Category.assoc,
    IsIso.inv_hom_id_assoc]

/-- Comparing with something further along the same arrow is just that step. -/
@[simp] theorem coneCmp_self_comp {b y z : C} (hy : b ⟶ y) (f : y ⟶ z) :
    coneCmp hy (hy ≫ f) = homMk f := by
  simp only [coneCmp, homMk, Functor.map_comp, IsIso.inv_hom_id_assoc]

/-- In a thin category the comparison depends only on the three objects. -/
theorem coneCmp_congr [Quiver.IsThin C] {b y z : C} (hy hy' : b ⟶ y) (hz hz' : b ⟶ z) :
    coneCmp hy hz = coneCmp hy' hz' := by
  rw [Subsingleton.elim hy hy', Subsingleton.elim hz hz']

/-- **A cospan over `b` is a comparison too.**  With `coneCmp_comp` this covers both zigzag steps, so
every route through `↑b` rewrites to a single `cmp` — which is what replaces the up-set/initial
-object form of the cone lemma. -/
theorem coneCmp_cospan [Quiver.IsThin C] {b y z w : C} (hy : b ⟶ y) (hz : b ⟶ z)
    (hyw : y ⟶ w) (hzw : z ⟶ w) : homMk hyw ≫ inv (homMk hzw) = coneCmp hy hz := by
  have he : homMk hy ≫ homMk hyw = homMk hz ≫ homMk hzw := by
    rw [← Functor.map_comp, ← Functor.map_comp, Subsingleton.elim (hy ≫ hyw) (hz ≫ hzw)]
  have hA : homMk hyw = inv (homMk hy) ≫ homMk hz ≫ homMk hzw := by
    rw [← he, IsIso.inv_hom_id_assoc]
  rw [coneCmp, hA, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end CategoryTheory.FreeGroupoid

namespace CubeChains

open COM SignVec FreeGroupoid

variable {n : ℕ}

/-! ## The wall-crossing generator

`faceCell_le_topeCell` (`Salvetti/SalExec`) is the one line that collapses both Artin relations to
`cross_trans`: every tope over `X` lies over the single cell `(X, T₀)`. -/

/-- **The wall-crossing generator**: two topes above a common face `X`, compared through the apex
`(X, T₀)`.  The apex genuinely matters — `cross` at two different apexes over the same pair differs
by a loop, and that is where `π₁` lives. -/
noncomputable def cross {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T T' : Tope n} (hT : X.1 ⊑ T.1) (hT' : X.1 ⊑ T'.1) :
    (mk (topeCell T) : FreeGroupoid (Sal (braidCOM n))) ⟶ mk (topeCell T') :=
  coneCmp (homOfLE (faceCell_le_topeCell h hT)) (homOfLE (faceCell_le_topeCell h hT'))

@[simp] theorem cross_self {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T : Tope n} (hT : X.1 ⊑ T.1) : cross h hT hT = 𝟙 _ := coneCmp_self _

@[simp] theorem inv_cross {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T T' : Tope n} (hT : X.1 ⊑ T.1) (hT' : X.1 ⊑ T'.1) :
    inv (cross h hT hT') = cross h hT' hT := inv_coneCmp _ _

/-- **The apex may be refined.**  Crossing through *any* cell `p` over `(X, T₀)` gives the same
morphism — in particular through the wall between `T` and `T'`, which is the geometric `σᵢ`.  This
is what makes the single-apex `cross` above the Artin generator rather than a convenient fiction. -/
theorem cross_eq_coneCmp_of_le {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T T' : Tope n} (hT : X.1 ⊑ T.1) (hT' : X.1 ⊑ T'.1)
    {p : Sal (braidCOM n)} (hp : faceCell X T₀ h ≤ p)
    (hpT : p ≤ topeCell T) (hpT' : p ≤ topeCell T') :
    cross h hT hT' = coneCmp (homOfLE hpT) (homOfLE hpT') := by
  rw [cross, ← coneCmp_comp (homOfLE hp) (homOfLE hpT) (homOfLE hpT')]
  exact coneCmp_congr _ _ _ _

/-- **Crossings at one face telescope.** -/
theorem cross_trans {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T T' T'' : Tope n} (hT : X.1 ⊑ T.1) (hT' : X.1 ⊑ T'.1) (hT'' : X.1 ⊑ T''.1) :
    cross h hT hT' ≫ cross h hT' hT'' = cross h hT hT'' := coneCmp_trans _ _ _

/-! ## The Artin relations

Two routes over the same face agree.  Commutation `sᵢsⱼ = sⱼsᵢ` (`|i-j| ≥ 2`) is the four topes over
a face with 2-blocks at `i` and `j`; the braid relation `sᵢsᵢ₊₁sᵢ = sᵢ₊₁sᵢsᵢ₊₁` is the six topes
over a face with a 3-block at `i`.  Only the choice of `X` differs. -/

/-- **Commutation.**  Four topes over one face: the two routes agree. -/
theorem cross_square {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T₁ T₂ T₃ T₄ : Tope n} (h₁ : X.1 ⊑ T₁.1) (h₂ : X.1 ⊑ T₂.1) (h₃ : X.1 ⊑ T₃.1)
    (h₄ : X.1 ⊑ T₄.1) :
    cross h h₁ h₂ ≫ cross h h₂ h₄ = cross h h₁ h₃ ≫ cross h h₃ h₄ := by
  rw [cross_trans, cross_trans]

/-- **The braid relation.**  Six topes over one face: the two hexagon routes agree. -/
theorem cross_hexagon {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T₁ T₂ T₃ T₄ T₅ T₆ : Tope n} (h₁ : X.1 ⊑ T₁.1) (h₂ : X.1 ⊑ T₂.1) (h₃ : X.1 ⊑ T₃.1)
    (h₄ : X.1 ⊑ T₄.1) (h₅ : X.1 ⊑ T₅.1) (h₆ : X.1 ⊑ T₆.1) :
    cross h h₁ h₂ ≫ cross h h₂ h₃ ≫ cross h h₃ h₄
      = cross h h₁ h₅ ≫ cross h h₅ h₆ ≫ cross h h₆ h₄ := by
  rw [← Category.assoc, cross_trans, cross_trans, ← Category.assoc, cross_trans, cross_trans]

/-! ## Every arrow is a chamber comparison

Generation wants the opposite move from the relations: not "route through a face" but "route through
a *word*".  The chamber of a word is the cell `(0, wordTope σ)` — the execution whose chain is the
cube's top cell — and an execution lies over the chamber of its own run word, because that is its
cell condition `X ⊑ T` yet again.  Transitivity then puts the target of every arrow over the
*source's* chamber, so every generator is a `cmp` there. -/

/-- The zero covector is a face. -/
theorem zero_mem_covectors : (0 : SignVec (BraidGround n)) ∈ (braidCOM n).covectors :=
  ⟨0, funext fun e => by simp⟩

/-- **The chamber of a word** — the minimal cell with that tope. -/
def chamber (σ : Equiv.Perm (Fin n)) : Sal (braidCOM n) :=
  ⟨(0, wordTope σ), zero_mem_covectors, isTope_wordTope σ, fun _ => Or.inl rfl⟩

/-- **A cell lies over its own word's chamber.**  The wall-crossing clause is the cell condition
`X ⊑ T` (`comp_eq_right_of_faceLE`); the face clause is `0 ⊑ X`. -/
theorem chamber_le {a : Sal (braidCOM n)} {σ : Equiv.Perm (Fin n)} (h : wordTope σ = a.tope) :
    chamber σ ≤ a := by
  refine ⟨fun _ => Or.inl rfl, ?_⟩
  change a.tope = a.face ⊙ wordTope σ
  rw [h]
  exact (comp_eq_right_of_faceLE a.2.2.2).symm

/-- **Every arrow is a comparison at the source's chamber.**  With `coneCmp_trans` this is the shape a
generation argument wants: a zigzag rewrites to an alternating product of chamber comparisons, and
what is left to show is that consecutive chambers differ by wall crossings. -/
theorem homMk_eq_coneCmp_chamber {a b : Sal (braidCOM n)} {σ : Equiv.Perm (Fin n)}
    (h : wordTope σ = a.tope) (hab : a ≤ b) :
    homMk (homOfLE hab)
      = coneCmp (homOfLE (chamber_le h)) (homOfLE ((chamber_le h).trans hab)) := by
  rw [Subsingleton.elim (homOfLE ((chamber_le h).trans hab))
    (homOfLE (chamber_le h) ≫ homOfLE hab), coneCmp_self_comp]

/-! ## Reading the hypothesis geometrically

`X ⊑ T` says `T` preserves every strict comparison `X` makes.  So the topes over the face of an
ordered partition are exactly the words refining it *within* blocks — which is why a `Δ²` hexagon,
whose apexes reverse a pair the witness separates, is not over the witness and is *not* killed. -/

/-- **The topes over a face, as order agreement.** -/
theorem faceLE_wordTope_iff {v : Fin n → ℤ} {w : Equiv.Perm (Fin n)} :
    braidSign v ⊑ wordTope w ↔
      ∀ i j, v i ≠ v j → (v i < v j ↔ (w.symm i : ℕ) < (w.symm j : ℕ)) := by
  rw [wordTope_eq_braidSign, braidSign_faceLE_iff]
  simp only [Nat.cast_lt]

/-! ## Faithfulness of `Conc`

The theorem this is all for.  A functor out of a groupoid is faithful as soon as it kills no
non-identity **loop** (`Groupoid.faithful_of_loop`), so `Conc` is faithful on `□ⁿ` exactly when a
loop of the execution poset with trivial braid word is trivial.  `conc_map_cmp` computes the braid
of a chamber comparison: the word out to `z`, over the word out to `y`. -/

/-- **A functor out of a groupoid is faithful once it kills no non-identity loop.**  Two parallel
arrows differ by a loop, which is the only thing there is to check. -/
theorem _root_.CategoryTheory.Groupoid.faithful_of_loop {G H : Type*} [Groupoid G] [Category H]
    (F : G ⥤ H) (h : ∀ (x : G) (u : x ⟶ x), F.map u = 𝟙 (F.obj x) → u = 𝟙 x) : F.Faithful where
  map_injective {x y} f g hfg := by
    have hloop : F.map (f ≫ Groupoid.inv g) = 𝟙 (F.obj x) := by
      rw [F.map_comp, hfg, ← F.map_comp, Groupoid.comp_inv, F.map_id]
    have := h x _ hloop
    rw [← Category.comp_id f, ← Groupoid.inv_comp g, ← Category.assoc, this, Category.id_comp]

/-- The braid of a generator is `ConcPos`'s label. -/
@[simp] theorem conc_map_homMk {K : BPSet} {x y : Ch⋆ K} (f : x ⟶ y) :
    (Conc K).map (homMk f) = (ConcPos K).map f :=
  FreeGroupoid.lift_map_homMk _ f

/-- **The braid of a chamber comparison**: it takes the label out to `y` to the label out to `z`. -/
theorem conc_map_coneCmp {K : BPSet} {b y z : Ch⋆ K} (hy : b ⟶ y) (hz : b ⟶ z) :
    (Conc K).map (homMk hy) ≫ (Conc K).map (coneCmp hy hz) = (ConcPos K).map hz := by
  rw [← Functor.map_comp, coneCmp, IsIso.hom_inv_id_assoc, conc_map_homMk]

/-- **`Conc` is faithful on the standard cube**, reduced to loops — the remaining obligation is
that `ConcPos`'s braid word detects every non-trivial loop of the execution poset.  With
`homMk_eq_coneCmp_chamber` every generator is a `cmp` at a chamber, and `coneCmp_trans` collapses runs at
one chamber, so what must be shown is that the surviving chamber-to-chamber transitions are
generated by the wall crossings whose relations are `cross_square` / `cross_hexagon`. -/
theorem conc_faithful_of_loop (n : ℕ)
    (h : ∀ (x : FreeGroupoid (Ch⋆ (□n))) (u : x ⟶ x),
      (Conc (□n)).map u = 𝟙 ((Conc (□n)).obj x) → u = 𝟙 x) :
    (Conc (□n)).Faithful :=
  Groupoid.faithful_of_loop _ h

/-! ## Transport to executions

`braidSalEquiv` carries all of the above to `Ch⋆ (□ⁿ)`, where `Conc` lives. -/

/-- The wall-crossing generator, on executions.  The endpoints are left to inference — spelling
`braidSalEquiv.functor.obj (topeCell T)` out forces `salChStarEquiv` through `whnf`. -/
noncomputable def crossExec {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T T' : Tope n} (hT : X.1 ⊑ T.1) (hT' : X.1 ⊑ T'.1) :=
  (FreeGroupoid.map (C := Sal (braidCOM n)) (D := Ch⋆ (□n)) braidSalEquiv.functor).map
    (cross h hT hT')

theorem crossExec_trans {X : Face (braidCOM n)} {T₀ : Tope n} (h : X.1 ⊑ T₀.1)
    {T T' T'' : Tope n} (hT : X.1 ⊑ T.1) (hT' : X.1 ⊑ T'.1) (hT'' : X.1 ⊑ T''.1) :
    crossExec h hT hT' ≫ crossExec h hT' hT'' = crossExec h hT hT'' := by
  rw [crossExec, crossExec, crossExec, ← Functor.map_comp, cross_trans]

end CubeChains
