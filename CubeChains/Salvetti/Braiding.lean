import CubeChains.Salvetti.FreeGroupoidProd
import Mathlib.CategoryTheory.SingleObj

/-!
# Salvetti/Braiding — the interchange of concurrent blocks is a braid, not a symmetry

The box category is **symmetry-free**: there is no map `□ⁿ ⊗ □ᵐ ≅ □ᵐ ⊗ □ⁿ`.  But the concurrency
category *does* have a tensor,

    concTensor n m : ConcCat □ⁿ × ConcCat □ᵐ ⥤ ConcCat □^{n+m}

(Segal-split the wedge, then push forward along `cubeSplit n m : □ⁿ ∨ □ᵐ ⟶ □^{n+m}`), and in its
groupoidification the interchange of two blocks of concurrent events **exists** as an isomorphism.
It is a *braid*, not a symmetry: performing it twice is the full twist, a nontrivial pure braid.

The smallest instance is `□²` — two independent events.  `Sal (braidCOM 2) ≌ ConcCat □²` is the
`4`-cycle: two concurrent cells (the square with a chamber) each mapping to both runs (the two edge
paths).  The two interchanges `salBraid`/`salBraid'` — one through each cell — do not cancel
(`salBraid_comp_ne_id`).  The invariant that sees this is the **wall-crossing cocycle** `salCross`,
additive along the Salvetti order, hence a functor `salWind : Sal L ⥤ SingleObj (Multiplicative ℤ)`;
the full twist crosses the wall `x₀ = x₁` twice, so it winds, so it is not `𝟙`.  It generates
`π₁(Sal (braidCOM 2)) = P₂ = ℤ`.
-/

open CategoryTheory Opposite BPSet CubeChain StdCube

namespace CubeChains

open SignVec

/-! ## Functoriality of the concurrency category -/

/-- A map of bi-pointed sets pushes executions forward.  `ChainCat.pushforward` leaves the
dimension sequence *and* the underlying wedge map of every chain morphism untouched, and `Lines`
sees only those — so the chamber tuple carries over on the nose.

    ConcCat K --concPushforward f--> ConcCat L
        |                                |
        π                                π
        v                                v
     (Ch K)ᵒᵖ --(pushforward f)ᵒᵖ--> (Ch L)ᵒᵖ
-/
noncomputable def concPushforward {K L : BPSet} (f : K ⟶ L) : ConcCat K ⥤ ConcCat L where
  obj x := ⟨op ((ChainCat.pushforward f).obj x.1.unop), x.2⟩
  map {_ _} u := ⟨((ChainCat.pushforward f).map u.1.unop).op, u.2⟩
  map_id x := CategoryOfElements.ext (Lines L) _ _ (by
    show ((ChainCat.pushforward f).map (𝟙 x.1.unop)).op = _
    rw [CategoryTheory.Functor.map_id]; rfl)
  map_comp u v := CategoryOfElements.ext (Lines L) _ _ (by
    show ((ChainCat.pushforward f).map (v.1.unop ≫ u.1.unop)).op = _
    rw [CategoryTheory.Functor.map_comp]; rfl)

/-! ## The two-bead splitting of a cube -/

theorem card_filter_lt (n m : ℕ) :
    (Finset.univ.filter (fun j : Fin (n + m) => (j : ℕ) < n)).card = n := by
  classical
  have h : Finset.univ.filter (fun j : Fin (n + m) => (j : ℕ) < n)
      = Finset.univ.map (Fin.castAddEmb (n := n) m) := by
    ext j
    rw [Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨-, hj⟩
      exact ⟨⟨j.1, hj⟩, Finset.mem_univ _, Fin.ext (by simp [Fin.castAddEmb])⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨Finset.mem_univ _, by simpa [Fin.castAddEmb] using i.isLt⟩
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem card_filter_not_lt (n m : ℕ) :
    (Finset.univ.filter (fun j : Fin (n + m) => ¬ ((j : ℕ) < n))).card = m := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + m)))) (p := fun j : Fin (n + m) => (j : ℕ) < n)
  rw [card_filter_lt, Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The **front** `n`-face of `□^{n+m}`: the last `m` coordinates fixed to `0`. -/
def frontCell (n m : ℕ) : Cell (n + m) n :=
  ⟨fun j => if (j : ℕ) < n then none else some false, by
    have : noneSet (fun j : Fin (n + m) => if (j : ℕ) < n then none else some false)
        = Finset.univ.filter (fun j : Fin (n + m) => (j : ℕ) < n) := by
      ext j; by_cases h : (j : ℕ) < n <;> simp [mem_noneSet, h]
    rw [this, card_filter_lt]⟩

/-- The **back** `m`-face of `□^{n+m}`: the first `n` coordinates fixed to `1`. -/
def backCell (n m : ℕ) : Cell (n + m) m :=
  ⟨fun j => if (j : ℕ) < n then some true else none, by
    have : noneSet (fun j : Fin (n + m) => if (j : ℕ) < n then some true else none)
        = Finset.univ.filter (fun j : Fin (n + m) => ¬ ((j : ℕ) < n)) := by
      ext j; by_cases h : (j : ℕ) < n <;> simp [mem_noneSet, h] <;> omega
    rw [this, card_filter_not_lt]⟩

/-- The front face as a `Box` morphism `▫n ⟶ ▫(n+m)`. -/
noncomputable def frontMap (n m : ℕ) : ▫n ⟶ ▫(n + m) := canonicalMap (frontCell n m)

/-- The back face as a `Box` morphism `▫m ⟶ ▫(n+m)`. -/
noncomputable def backMap (n m : ℕ) : ▫m ⟶ ▫(n + m) := canonicalMap (backCell n m)

/-- The **junction** vertex of the splitting: first `n` coordinates `1`, last `m` coordinates `0`
(the final vertex of the front face = the initial vertex of the back face). -/
def junctionCell (n m : ℕ) : Cell (n + m) 0 :=
  ⟨fun j => if (j : ℕ) < n then some true else some false, by
    have : noneSet (fun j : Fin (n + m) => if (j : ℕ) < n then some true else some false)
        = (∅ : Finset (Fin (n + m))) := by
      ext j; by_cases h : (j : ℕ) < n <;> simp [mem_noneSet, h]
    rw [this]; rfl⟩

/-- The junction vertex as a `Box` morphism `▫0 ⟶ ▫(n+m)`. -/
noncomputable def junctionMap (n m : ℕ) : ▫0 ⟶ ▫(n + m) := canonicalMap (junctionCell n m)

/-- Two `Box` maps out of `▫k` agree as soon as they agree on the top cell. -/
theorem box_hom_ext {k N : ℕ} {f g : ▫k ⟶ ▫N} (h : ev f = ev g) : f = g :=
  (cubeRepr (stdPre N) k).injective h

theorem ev_frontMap (n m : ℕ) : ev (frontMap n m) = frontCell n m := ev_canonicalMap _
theorem ev_backMap (n m : ℕ) : ev (backMap n m) = backCell n m := ev_canonicalMap _

theorem ev_initVertexMap (k : ℕ) : ev (PrecubicalSet.initVertexMap k) = constVertex k false :=
  ev_canonicalMap _

theorem ev_finalVertexMap (k : ℕ) : ev (PrecubicalSet.finalVertexMap k) = constVertex k true :=
  ev_canonicalMap _

/-- `ev` of a `Box` composite, with the two `ev`s already computed.  Written with `ev`-driven
elaboration of `≫` so that `ev_comp_app` fires (the `Box` and `PrecubicalConstructions`
compositions are defeq but not syntactically equal). -/
theorem ev_comp_cells {k e N : ℕ} (p : ▫k ⟶ ▫e) (q : ▫e ⟶ ▫N)
    {c : Cell N e} {d : Cell e k} (hq : ev q = c) (hp : ev p = d) :
    ev (p ≫ q) = act (K := stdPre N) c d := by
  rw [ev_comp_app, hq, hp]

theorem front_init (n m : ℕ) :
    (PrecubicalSet.initVertexMap n ≫ frontMap n m : ▫0 ⟶ ▫(n + m))
      = PrecubicalSet.initVertexMap (n + m) := by
  refine box_hom_ext
    ((ev_comp_cells _ _ (ev_frontMap n m) (ev_initVertexMap n)).trans ?_)
  rw [ev_initVertexMap]
  refine Subtype.ext (funext fun c => ?_)
  rw [app_val]
  by_cases hc : c ∈ noneSet (frontCell n m).val
  · rw [dif_pos hc]; rfl
  · rw [dif_neg hc]
    rw [mem_noneSet] at hc
    have hn : ¬ ((c : ℕ) < n) := fun h => hc (by simp [frontCell, h])
    simp [frontCell, constVertex, hn]

theorem front_final (n m : ℕ) :
    (PrecubicalSet.finalVertexMap n ≫ frontMap n m : ▫0 ⟶ ▫(n + m)) = junctionMap n m := by
  refine box_hom_ext
    ((ev_comp_cells _ _ (ev_frontMap n m) (ev_finalVertexMap n)).trans ?_)
  rw [junctionMap, ev_canonicalMap]
  refine Subtype.ext (funext fun c => ?_)
  rw [app_val]
  by_cases hc : (c : ℕ) < n
  · rw [dif_pos (by simp [mem_noneSet, frontCell, hc])]
    simp [junctionCell, constVertex, hc]
  · rw [dif_neg (by simp [mem_noneSet, frontCell, hc])]
    simp [frontCell, junctionCell, hc]

theorem back_init (n m : ℕ) :
    (PrecubicalSet.initVertexMap m ≫ backMap n m : ▫0 ⟶ ▫(n + m)) = junctionMap n m := by
  refine box_hom_ext
    ((ev_comp_cells _ _ (ev_backMap n m) (ev_initVertexMap m)).trans ?_)
  rw [junctionMap, ev_canonicalMap]
  refine Subtype.ext (funext fun c => ?_)
  rw [app_val]
  by_cases hc : (c : ℕ) < n
  · rw [dif_neg (by simp [mem_noneSet, backCell, hc])]
    simp [backCell, junctionCell, hc]
  · rw [dif_pos (by simp [mem_noneSet, backCell, hc])]
    simp [junctionCell, constVertex, hc]

theorem back_final (n m : ℕ) :
    (PrecubicalSet.finalVertexMap m ≫ backMap n m : ▫0 ⟶ ▫(n + m))
      = PrecubicalSet.finalVertexMap (n + m) := by
  refine box_hom_ext
    ((ev_comp_cells _ _ (ev_backMap n m) (ev_finalVertexMap m)).trans ?_)
  rw [ev_finalVertexMap]
  refine Subtype.ext (funext fun c => ?_)
  rw [app_val]
  by_cases hc : c ∈ noneSet (backCell n m).val
  · rw [dif_pos hc]; rfl
  · rw [dif_neg hc]
    rw [mem_noneSet] at hc
    have hn : (c : ℕ) < n := by
      by_contra h
      exact hc (by simp [backCell, h])
    simp [backCell, constVertex, hn]

/-- The Yoneda inverse of a `Box` morphism is the represented map. -/
theorem yonedaEquiv_symm_yoneda_map {X Y : Box} (g : X ⟶ Y) :
    (yonedaEquiv (X := X) (F := yoneda.obj Y)).symm g = yoneda.map g :=
  yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map g).symm

theorem cube_initVertex (n : ℕ) :
    (□n).initVertex = yoneda.map (PrecubicalSet.initVertexMap n) :=
  yonedaEquiv_symm_yoneda_map _

theorem cube_finalVertex (n : ℕ) :
    (□n).finalVertex = yoneda.map (PrecubicalSet.finalVertexMap n) :=
  yonedaEquiv_symm_yoneda_map _

/-- The front and back faces agree at the junction vertex — the pushout condition. -/
theorem cubeSplit_compat (n m : ℕ) :
    (□n).finalVertex ≫ yoneda.map (frontMap n m)
      = (□m).initVertex ≫ yoneda.map (backMap n m) := by
  have e1 : (□n).finalVertex ≫ yoneda.map (frontMap n m)
      = yoneda.map (junctionMap n m) := by
    rw [cube_finalVertex]
    exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (front_final n m))
  have e2 : (□m).initVertex ≫ yoneda.map (backMap n m)
      = yoneda.map (junctionMap n m) := by
    rw [cube_initVertex]
    exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map (back_init n m))
  rw [e1, e2]

/-- The underlying presheaf map of `cubeSplit`. -/
noncomputable def cubeSplitHom (n m : ℕ) :
    (wedge2 (□n) (□m)).toPsh ⟶ (□(n + m)).toPsh :=
  Limits.pushout.desc (yoneda.map (frontMap n m)) (yoneda.map (backMap n m))
    (cubeSplit_compat n m)

theorem cubeSplitHom_init (n m : ℕ) :
    (cubeSplitHom n m)⟪0⟫ ((wedge2 (□n) (□m)).init) = (□(n + m)).init := by
  have h : (Limits.pushout.inl ((□n).finalVertex) ((□m).initVertex) ≫ cubeSplitHom n m)⟪0⟫
      ((□n).init) = (yoneda.map (frontMap n m))⟪0⟫ ((□n).init) := by
    rw [cubeSplitHom, Limits.pushout.inl_desc]; rfl
  exact h.trans (front_init n m)

theorem cubeSplitHom_final (n m : ℕ) :
    (cubeSplitHom n m)⟪0⟫ ((wedge2 (□n) (□m)).final) = (□(n + m)).final := by
  have h : (Limits.pushout.inr ((□n).finalVertex) ((□m).initVertex) ≫ cubeSplitHom n m)⟪0⟫
      ((□m).final) = (yoneda.map (backMap n m))⟪0⟫ ((□m).final) := by
    rw [cubeSplitHom, Limits.pushout.inr_desc]; rfl
  exact h.trans (back_final n m)

/-- **The two-bead splitting of a cube.**  `□ⁿ` goes to the front face of `□^{n+m}` (last `m`
coordinates `0`), `□ᵐ` to the back face (first `n` coordinates `1`); they meet at the junction
vertex, so the wedge pushout descends.

    □ⁿ ∨ □ᵐ --cubeSplit--> □^{n+m}

Its `Ch`-pushforward is the interleaving of an execution of `□ⁿ` with one of `□ᵐ`. -/
noncomputable def cubeSplit (n m : ℕ) : wedge2 (□n) (□m) ⟶ □(n + m) :=
  ⟨cubeSplitHom n m, cubeSplitHom_init n m, cubeSplitHom_final n m⟩

/-! ## The tensor on concurrency categories -/

/-- **The tensor of executions.**  Segal splits an execution of the wedge into one of each bead
(`linesWedgeEquiv`); `cubeSplit` then pushes the pair into `□^{n+m}` as the two-bead chain.

    ConcCat □ⁿ × ConcCat □ᵐ ≌ ConcCat (□ⁿ ∨ □ᵐ) --concPushforward (cubeSplit n m)--> ConcCat □^{n+m}
-/
noncomputable def concTensor (n m : ℕ) :
    ConcCat (□n) × ConcCat (□m) ⥤ ConcCat (□(n + m)) :=
  (linesWedgeEquiv (□n) (□m) (cube_admitsAltitude n) (cube_admitsAltitude m)).inverse ⋙
    concPushforward (cubeSplit n m)

/-- The tensor on concurrency braid *groupoids*: `concTensor` groupoidified, through
`freeGroupoidProdEquiv : FreeGroupoid (C × D) ≌ FreeGroupoid C × FreeGroupoid D`. -/
noncomputable def concGrpdTensor (n m : ℕ) :
    ConcGrpd (□n) × ConcGrpd (□m) ⥤ ConcGrpd (□(n + m)) :=
  (freeGroupoidProdEquiv (ConcCat (□n)) (ConcCat (□m))).inverse ⋙
    FreeGroupoid.map (concTensor n m)

/-! ## The winding cocycle on a Salvetti poset -/

/-- A covector that vanishes nowhere is a tope: nothing is strictly above it. -/
theorem COM.isTope_of_ne_zero {E : Type*} (L : COM E) {T : SignVec E}
    (hT : T ∈ L.covectors) (h : ∀ e, T e ≠ 0) : L.IsTope T :=
  ⟨hT, fun _ _ hle => funext fun e => ((hle e).resolve_left (h e)).symm⟩

/-- `X ⊙ Y = X` when `X` vanishes nowhere. -/
theorem SignVec.comp_eq_left {E : Type*} {X : SignVec E} (h : ∀ e, X e ≠ 0) (Y : SignVec E) :
    X ⊙ Y = X := by
  funext e; rw [comp_apply, if_neg (h e)]

variable {E : Type*} [Fintype E] {L : COM E}

/-- The **wall-crossing number** of a Salvetti relation: the number of ground-set elements at
which the two topes disagree.  This is the winding `1`-cocycle of `Sal L`. -/
def salCross (a b : Sal L) : ℤ :=
  (Finset.univ.filter (fun e => a.tope e ≠ b.tope e)).card

theorem salCross_eq_zero_of_tope_eq {a b : Sal L} (h : a.tope = b.tope) : salCross a b = 0 := by
  simp [salCross, h]

theorem salCross_eq_card {a b : Sal L} (h : ∀ e, a.tope e ≠ b.tope e) :
    salCross a b = Fintype.card E := by
  rw [salCross, Finset.filter_true_of_mem (fun e _ => h e), Finset.card_univ]

/-! The two halves of `b.tope = b.face ⊙ a.tope`. -/

theorem tope_eq_of_face_zero {a b : Sal L} (h : a ≤ b) {e : E} (he : b.face e = 0) :
    b.tope e = a.tope e := by
  conv_lhs => rw [h.2]
  rw [SignVec.comp_apply, if_pos he]

theorem tope_eq_of_face_ne_zero {a b : Sal L} (h : a ≤ b) {e : E} (he : b.face e ≠ 0) :
    b.tope e = b.face e := by
  conv_lhs => rw [h.2]
  rw [SignVec.comp_apply, if_neg he]

/-- Along `a ≤ b ≤ c`, a wall crossed by `a ≤ b` is already crossed at `c`: it is *not* crossed
again by `b ≤ c`.  (Once a coordinate is fixed by `b.face` it stays fixed in `c.face`.) -/
theorem tope_eq_of_cross {a b c : Sal L} (hab : a ≤ b) (hbc : b ≤ c) {e : E}
    (h : a.tope e ≠ b.tope e) : c.tope e = b.tope e := by
  have hbf : b.face e ≠ 0 := fun h0 => h (tope_eq_of_face_zero hab h0).symm
  have hbt : b.tope e = b.face e := tope_eq_of_face_ne_zero hab hbf
  have hcf : c.face e = b.face e := ((hbc.1 e).resolve_left hbf).symm
  rw [tope_eq_of_face_ne_zero hbc (hcf ▸ hbf), hcf, hbt]

/-- Along `a ≤ b ≤ c`, a wall crossed by `b ≤ c` was not already crossed by `a ≤ b`. -/
theorem tope_eq_of_cross' {a b c : Sal L} (hab : a ≤ b) (hbc : b ≤ c) {e : E}
    (h : b.tope e ≠ c.tope e) : b.tope e = a.tope e := by
  have hcf : c.face e ≠ 0 := fun h0 => h (tope_eq_of_face_zero hbc h0).symm
  have hct : c.tope e = c.face e := tope_eq_of_face_ne_zero hbc hcf
  have hbf : b.face e = 0 := by
    by_contra hbf
    exact h (by rw [tope_eq_of_face_ne_zero hab hbf, hct,
      ((hbc.1 e).resolve_left hbf)])
  exact tope_eq_of_face_zero hab hbf

/-- **The crossing number is additive** along `a ≤ b ≤ c`: the walls separating `a` from `c` are
exactly those separating `a` from `b` together with those separating `b` from `c`, disjointly. -/
theorem salCross_add {a b c : Sal L} (hab : a ≤ b) (hbc : b ≤ c) :
    salCross a c = salCross a b + salCross b c := by
  classical
  set S₁ := Finset.univ.filter (fun e => a.tope e ≠ b.tope e) with hS₁
  set S₂ := Finset.univ.filter (fun e => b.tope e ≠ c.tope e) with hS₂
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [hS₁, Finset.mem_filter] at he₁
    rw [hS₂, Finset.mem_filter] at he₂
    exact he₂.2 (tope_eq_of_cross hab hbc he₁.2).symm
  have hunion : Finset.univ.filter (fun e => a.tope e ≠ c.tope e) = S₁ ∪ S₂ := by
    ext e
    simp only [hS₁, hS₂, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h
      by_cases hb : a.tope e = b.tope e
      · exact Or.inr (fun hc => h (hb.trans hc))
      · exact Or.inl hb
    · rintro (h | h)
      · rw [tope_eq_of_cross hab hbc h]; exact h
      · rw [← tope_eq_of_cross' hab hbc h]; exact h
  rw [salCross, salCross, salCross, hunion, Finset.card_union_of_disjoint hdisj]
  push_cast
  ring

/-- **The winding functor.**  `Sal L` is a poset, and the crossing number is an additive cocycle on
it, hence a functor to the one-object category of `ℤ`.  It measures how many walls a Salvetti path
crosses, counted with sign once inverted in the groupoid — the winding number. -/
def salWind (L : COM E) : Sal L ⥤ SingleObj (Multiplicative ℤ) where
  obj _ := SingleObj.star _
  map {a b} f := Multiplicative.ofAdd (salCross a b)
  map_id a := by
    change Multiplicative.ofAdd (salCross a a) = 1
    rw [salCross_eq_zero_of_tope_eq rfl]; rfl
  map_comp {a b c} f g := by
    change Multiplicative.ofAdd (salCross a c) = _
    rw [SingleObj.comp_as_mul, salCross_add (leOfHom f) (leOfHom g), add_comm]
    rfl

/-! ## The braid arrangement of two strands -/

instance instFintypeBraidGround (n : ℕ) : Fintype (BraidGround n) :=
  inferInstanceAs (Fintype { p : Fin n × Fin n // p.1 < p.2 })

instance instDecidableEqBraidGround (n : ℕ) : DecidableEq (BraidGround n) :=
  inferInstanceAs (DecidableEq { p : Fin n × Fin n // p.1 < p.2 })

/-- The unique wall of the two-strand braid arrangement, `x₀ = x₁`. -/
def wall2 : BraidGround 2 := ⟨(0, 1), by decide⟩

theorem eq_wall2 : ∀ e : BraidGround 2, e = wall2 := by decide

instance : Nonempty (BraidGround 2) := ⟨wall2⟩

theorem card_braidGround_two_pos : 0 < Fintype.card (BraidGround 2) :=
  Fintype.card_pos

/-- The chamber `x₀ > x₁`. -/
def topeP : SignVec (BraidGround 2) := braidSign ![1, 0]

/-- The chamber `x₀ < x₁`. -/
def topeN : SignVec (BraidGround 2) := braidSign ![0, 1]

@[simp] theorem topeP_apply (e : BraidGround 2) : topeP e = 1 := by
  rw [eq_wall2 e]; decide +kernel

@[simp] theorem topeN_apply (e : BraidGround 2) : topeN e = -1 := by
  rw [eq_wall2 e]; decide +kernel

theorem topeP_mem : topeP ∈ (braidCOM 2).covectors := ⟨_, rfl⟩
theorem topeN_mem : topeN ∈ (braidCOM 2).covectors := ⟨_, rfl⟩

theorem topeP_ne_zero (e : BraidGround 2) : topeP e ≠ 0 := by simp
theorem topeN_ne_zero (e : BraidGround 2) : topeN e ≠ 0 := by simp

theorem topeP_isTope : (braidCOM 2).IsTope topeP :=
  COM.isTope_of_ne_zero _ topeP_mem topeP_ne_zero

theorem topeN_isTope : (braidCOM 2).IsTope topeN :=
  COM.isTope_of_ne_zero _ topeN_mem topeN_ne_zero

theorem zero_faceLE (T : SignVec (BraidGround 2)) : (0 : SignVec (BraidGround 2)) ⊑ T :=
  fun _ => Or.inl rfl

/-! ### The four cells of `Sal (braidCOM 2)`

Two **cells** — the open 2-dimensional face `0` (both events concurrent) tagged with a chamber —
and two **runs** — the chambers themselves.  Under `braidSalEquiv 2` these are the two ways of
running `□²` as a single 2-bead-free chain, and the two edge paths around the square. -/

/-- The concurrent cell tagged with the chamber `x₀ > x₁`. -/
def cellP : Sal (braidCOM 2) :=
  ⟨(0, topeP), braidCOM_isOM 2, topeP_isTope, zero_faceLE _⟩

/-- The concurrent cell tagged with the chamber `x₀ < x₁`. -/
def cellN : Sal (braidCOM 2) :=
  ⟨(0, topeN), braidCOM_isOM 2, topeN_isTope, zero_faceLE _⟩

/-- The run `x₀ > x₁`. -/
def runP : Sal (braidCOM 2) :=
  ⟨(topeP, topeP), topeP_mem, topeP_isTope, faceLE_refl _⟩

/-- The run `x₀ < x₁`. -/
def runN : Sal (braidCOM 2) :=
  ⟨(topeN, topeN), topeN_mem, topeN_isTope, faceLE_refl _⟩

theorem cellP_le_runP : cellP ≤ runP :=
  ⟨zero_faceLE _, (comp_eq_left topeP_ne_zero topeP).symm⟩

theorem cellP_le_runN : cellP ≤ runN :=
  ⟨zero_faceLE _, (comp_eq_left topeN_ne_zero topeP).symm⟩

theorem cellN_le_runP : cellN ≤ runP :=
  ⟨zero_faceLE _, (comp_eq_left topeP_ne_zero topeN).symm⟩

theorem cellN_le_runN : cellN ≤ runN :=
  ⟨zero_faceLE _, (comp_eq_left topeN_ne_zero topeN).symm⟩

/-! ### The crossing numbers of the four arrows -/

theorem salCross_cellP_runP : salCross cellP runP = 0 :=
  salCross_eq_zero_of_tope_eq rfl

theorem salCross_cellN_runN : salCross cellN runN = 0 :=
  salCross_eq_zero_of_tope_eq rfl

theorem salCross_cellP_runN : salCross cellP runN = Fintype.card (BraidGround 2) :=
  salCross_eq_card (fun e => by simp [cellP, runN, COM.SalCell.tope])

theorem salCross_cellN_runP : salCross cellN runP = Fintype.card (BraidGround 2) :=
  salCross_eq_card (fun e => by simp [cellN, runP, COM.SalCell.tope])

/-! ## The braiding of the two independent events of `□²`

`Sal (braidCOM 2)` is the four-object height-`1` poset (the `4`-cycle).  In its free groupoid the
two runs become isomorphic — the **interchange** of the two concurrent events — but in two
inequivalent ways, one through each concurrent cell.  The two interchanges do not cancel: their
composite is the **full twist**, the generator of `π₁(Sal (braidCOM 2)) = P₂ = ℤ`. -/

open FreeGroupoid in
/-- The interchange `runP ≅ runN` through the concurrent cell tagged `x₀ > x₁`. -/
noncomputable def salBraid : mk runP ⟶ mk runN :=
  inv (homMk (homOfLE cellP_le_runP)) ≫ homMk (homOfLE cellP_le_runN)

open FreeGroupoid in
/-- The interchange `runN ≅ runP` through the *other* concurrent cell, tagged `x₀ < x₁`. -/
noncomputable def salBraid' : mk runN ⟶ mk runP :=
  inv (homMk (homOfLE cellN_le_runN)) ≫ homMk (homOfLE cellN_le_runP)

/-- The winding number of a Salvetti arrow, read off in the free groupoid. -/
theorem lift_salWind_homMk {a b : Sal (braidCOM 2)} (h : a ≤ b) :
    (FreeGroupoid.lift (salWind (braidCOM 2))).map (FreeGroupoid.homMk (homOfLE h))
      = Multiplicative.ofAdd (salCross a b) :=
  FreeGroupoid.lift_map_homMk _ _

/-- **The braiding is not a symmetry.**  Interchanging the two concurrent events of `□²` twice —
once through each of the two concurrent cells — is the *full twist*, not the identity: it winds
twice around the wall `x₀ = x₁`.  Independent actions do not commute; they braid. -/
theorem salBraid_comp_ne_id : salBraid ≫ salBraid' ≠ 𝟙 (FreeGroupoid.mk runP) := by
  intro h
  have key := congrArg (FreeGroupoid.lift (salWind (braidCOM 2))).map h
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, salBraid, salBraid',
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv] at key
  simp only [SingleObj.comp_as_mul, SingleObj.inv_as_inv, SingleObj.id_as_one] at key
  rw [lift_salWind_homMk, lift_salWind_homMk, lift_salWind_homMk, lift_salWind_homMk,
    salCross_cellP_runP, salCross_cellP_runN, salCross_cellN_runN, salCross_cellN_runP] at key
  simp only [ofAdd_zero, inv_one, mul_one, ← ofAdd_add] at key
  have h2 : ((Fintype.card (BraidGround 2) : ℤ) + Fintype.card (BraidGround 2)) = 0 :=
    Multiplicative.ofAdd.injective (key.trans (ofAdd_zero (α := ℤ)).symm)
  have := card_braidGround_two_pos
  omega

/-! ## Transport to the concurrency braid groupoid of `□²` -/

/-- The interchange of the two concurrent events of `□²`, in `ConcGrpd □²`. -/
noncomputable def concBraid :
    (concCubeEquiv 2).functor.obj (FreeGroupoid.mk runP) ⟶
      (concCubeEquiv 2).functor.obj (FreeGroupoid.mk runN) :=
  (concCubeEquiv 2).functor.map salBraid

/-- The interchange through the other concurrent cell. -/
noncomputable def concBraid' :
    (concCubeEquiv 2).functor.obj (FreeGroupoid.mk runN) ⟶
      (concCubeEquiv 2).functor.obj (FreeGroupoid.mk runP) :=
  (concCubeEquiv 2).functor.map salBraid'

/-- **The concurrency braiding of `□²` is not a symmetry.**  Swapping the two independent events
back and forth is the full twist of the pure braid group `P₂ = ℤ`, not the identity. -/
theorem concBraid_comp_ne_id : concBraid ≫ concBraid' ≠ 𝟙 _ := by
  intro h
  refine salBraid_comp_ne_id ((concCubeEquiv 2).functor.map_injective ?_)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
  exact h

end CubeChains
