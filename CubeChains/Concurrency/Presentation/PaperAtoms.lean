import CubeChains.Concurrency.Presentation.PaperArtin
import CubeChains.Concurrency.Presentation.PaperFunctor
import CubeChains.Foundations.Polygraph.Presheaf
import CubeChains.Machinery.Grading

/-!
# Concurrency/Presentation/PaperAtoms — what a presentation of `Ch(K)[W⁻¹]` cannot choose

A word costs what it crosses (`length_cutWord`): its length is the number of concurrent pairs the
refinement commutes, which is a grading of `Ch(K)[W⁻¹]` vanishing only on the isomorphisms, with
nothing read off Artin's presentation.  Such a grading pins the cells below dimension two: a
codimension-one arrow has a single letter spelling it, and 0-cells name pairwise non-isomorphic
objects.

In dimension two it makes every 2-cell a **critical pair** — two *different* words of at most three
letters naming one arrow — and the critical pairs present (`critPresents`).

The closing section states the characterisation and the two counterexamples that bound it.
-/

universe w' w u'' u' v u w₂' w₂ v₂ u₂

open CategoryTheory CategoryTheory.Polygraph Opposite BPSet CubeChains Equiv

namespace CategoryTheory

/-! ## Gradings, pulled back and rigid -/

namespace Grading

variable {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]

/-- **A grading pulled back along a functor.** -/
def comap (F : C ⥤ D) (G : Grading D) : Grading C where
  codim f := G.codim (F.map f)
  codim_id a := by rw [F.map_id]; exact G.codim_id _
  codim_comp f g := by rw [F.map_comp]; exact G.codim_comp _ _

@[simp] theorem comap_codim (F : C ⥤ D) (G : Grading D) {a b : C} (f : a ⟶ b) :
    (G.comap F).codim f = G.codim (F.map f) := rfl

/-- **A grading that detects invertibility**: codimension zero exactly on the isomorphisms.  One
direction is formal (`codim_eq_zero_of_isIso`); this is the other. -/
def Rigid (G : Grading C) : Prop := ∀ {a b : C} (f : a ⟶ b), G.codim f = 0 → IsIso f

/-- **Rigidity is reflected by a fully faithful functor.** -/
theorem Rigid.comap {G : Grading D} (F : C ⥤ D) [F.Full] [F.Faithful] (hG : G.Rigid) :
    (G.comap F).Rigid := fun f hf =>
  haveI : IsIso (F.map f) := hG (F.map f) hf
  isIso_of_fully_faithful F f

/-- **A grading, from a functor to the delooping** — the inverse of `Grading.functor`. -/
def ofFunctor (F : D ⥤ Grade) : Grading D where
  codim f := Multiplicative.toAdd (F.map f)
  codim_id a := by rw [F.map_id]; rfl
  codim_comp f g := by rw [F.map_comp]; exact Nat.add_comm _ _

@[simp] theorem ofFunctor_codim (F : D ⥤ Grade) {a b : D} (f : a ⟶ b) :
    (ofFunctor F).codim f = Multiplicative.toAdd (F.map f) := rfl

/-- **An isomorphism on either side costs nothing.** -/
theorem codim_iso_comp (G : Grading C) {a b c d : C} (s : a ≅ b) (f : b ⟶ c) (t : c ≅ d) :
    G.codim (s.hom ≫ f ≫ t.hom) = G.codim f := by
  rw [G.codim_comp, G.codim_comp, G.codim_eq_zero_of_isIso s.hom,
    G.codim_eq_zero_of_isIso t.hom]
  omega

end Grading

/-- **Two interpretations that agree up to natural isomorphism equate the same parallel pairs** —
so "these two words name one arrow" is a condition on the words, not on the functor naming the
arrow.  A localization functor is pinned exactly this tightly. -/
theorem map_eq_of_natIso {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) {x y : C} {u v : x ⟶ y} (h : F.map u = F.map v) :
    G.map u = G.map v := by
  have key : ∀ w : x ⟶ y, e.inv.app x ≫ F.map w ≫ e.hom.app y = G.map w := fun w => by
    rw [e.hom.naturality w, ← Category.assoc, ← NatTrans.comp_app, e.inv_hom_id, NatTrans.id_app,
      Category.id_comp]
  rw [← key u, ← key v, h]

@[inherit_doc map_eq_of_natIso]
theorem map_eq_iff_of_natIso {C : Type u} [Category.{v} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) {x y : C} (u v : x ⟶ y) :
    F.map u = F.map v ↔ G.map u = G.map v :=
  ⟨map_eq_of_natIso e, map_eq_of_natIso e.symm⟩

/-! ## Homogeneous polygraphs

A 2-cell whose two sides have different lengths destroys the word-length grading; forbidding that is
the whole hypothesis.  It is *reflected* by a morphism of polygraphs — a morphism pushes a 2-cell's
boundary forward letter by letter — which is how the paper's polygraph inherits it from Artin's. -/

namespace Polygraph

/-- **A polygraph whose 2-cells relate words of equal length.** -/
def Homogeneous (P : Polygraph.{w, u', w₂}) : Prop :=
  ∀ {x y : GenObj P.Gen} (α : P.Rel x y), (P.src α).length = (P.tgt α).length

/-- **Homogeneity is reflected along a morphism of polygraphs.** -/
theorem Homogeneous.of_hom {P : Polygraph.{w, u', w₂}} {Q : Polygraph.{w', u'', w₂'}} (F : Hom P Q)
    (h : Homogeneous Q) : Homogeneous P := fun α => by
  have hα := h (F.two α)
  rw [F.src_two, F.tgt_two, Prefunctor.length_mapPath, Prefunctor.length_mapPath] at hα
  exact hα

/-! ## Word length, as a grading of the presented category -/

variable {P : Polygraph.{w, u', w₂}}

/-- Every 1-cell costs one. -/
def lengthPre (P : Polygraph.{w, u', w₂}) : GenObj P.Gen ⥤q Grade where
  obj _ := SingleObj.star (Multiplicative ℕ)
  map _ := Multiplicative.ofAdd 1

theorem lengthPre_mapPath {x y : GenObj P.Gen} (u : Quiver.Path x y) :
    (Paths.lift (lengthPre P)).map u = Multiplicative.ofAdd u.length := by
  induction u with
  | nil => exact (Paths.lift_nil (lengthPre P) _).trans (congrArg Multiplicative.ofAdd rfl)
  | @cons b c u e ih =>
      refine (Paths.lift_cons (lengthPre P) u e).trans ?_
      change Multiplicative.ofAdd 1 * (Paths.lift (lengthPre P)).map u = _
      rw [ih]
      exact congrArg Multiplicative.ofAdd (Nat.add_comm 1 u.length)

/-- Homogeneity is exactly what the length functor's descent needs. -/
theorem lengthSound (h : P.Homogeneous) :
    ∀ (x y : P.Word) (f₁ f₂ : x ⟶ y), P.homRel f₁ f₂ →
      (Paths.lift (lengthPre P)).map f₁ = (Paths.lift (lengthPre P)).map f₂ := by
  rintro x y f₁ f₂ ⟨α, rfl, rfl⟩
  rw [lengthPre_mapPath, lengthPre_mapPath, h α]

/-- **The length of a word, on the presented category** — well defined exactly when the 2-cells are
homogeneous. -/
def lengthFunctor (h : P.Homogeneous) : P.presented ⥤ Grade :=
  Quotient.lift P.homRel (Paths.lift (lengthPre P)) (lengthSound h)

/-- **The word-length grading of a homogeneous polygraph's category.** -/
def lengthGrading (h : P.Homogeneous) : Grading P.presented := Grading.ofFunctor (lengthFunctor h)

@[simp] theorem lengthGrading_quot (h : P.Homogeneous) {x y : GenObj P.Gen}
    (u : Quiver.Path x y) : (lengthGrading h).codim (P.quot.map u) = u.length :=
  congrArg Multiplicative.toAdd
    ((Quotient.lift_map_functor_map P.homRel (Paths.lift (lengthPre P)) (lengthSound h) u).trans
      (lengthPre_mapPath u))

/-- **A homogeneous polygraph's 0-cells name pairwise non-isomorphic objects** — an isomorphism and
its inverse are words of total length zero, hence both empty.  So there is no room to name one
object twice, and no room for a non-identity automorphism to be spelled. -/
theorem eq_of_iso_of_homogeneous (h : P.Homogeneous) {x y : GenObj P.Gen}
    (e : (⟨x⟩ : P.presented) ≅ ⟨y⟩) : x = y := by
  obtain ⟨u, hu⟩ := P.quot.map_surjective e.hom
  have h0 : (lengthGrading h).codim (P.quot.map u) = 0 := by
    rw [hu]
    exact (lengthGrading h).codim_eq_zero_of_isIso e.hom
  exact Quiver.Path.eq_of_length_zero u ((lengthGrading_quot h u).symm.trans h0)

/-- **A word of length zero is the identity**, so the word-length grading is rigid. -/
theorem lengthGrading_rigid (h : P.Homogeneous) : (lengthGrading h).Rigid := by
  rintro ⟨x⟩ ⟨y⟩ f hf
  obtain ⟨u, rfl⟩ := P.quot.map_surjective f
  have hlen : u.length = 0 := (lengthGrading_quot h u).symm.trans hf
  obtain rfl := Quiver.Path.eq_of_length_zero u hlen
  obtain rfl := Quiver.Path.eq_nil_of_length_zero u hlen
  rw [P.quot_map_nil]
  exact IsIso.id _

end Polygraph

/-! ## …and of any category it presents -/

namespace Presents

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (h : P.Homogeneous)

/-- **The word-length grading, read on the presented category.** -/
noncomputable def grading : Grading C := (Polygraph.lengthGrading h).comap p.equiv.inverse

theorem grading_rigid : (p.grading h).Rigid :=
  Grading.Rigid.comap _ (Polygraph.lengthGrading_rigid h)

/-- **The grading is the word length**, read through the comparison functor: the unit of the
equivalence is an isomorphism, hence costs nothing. -/
theorem grading_codim_E {x y : P.presented} (g : x ⟶ y) :
    (p.grading h).codim (p.E.map g) = (Polygraph.lengthGrading h).codim g := by
  have hnat := p.equiv.unitIso.hom.naturality g
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have hv : p.equiv.inverse.map (p.equiv.functor.map g)
      = (p.equiv.unitIso.app x).symm.hom ≫ g ≫ (p.equiv.unitIso.app y).hom :=
    ((Iso.inv_comp_eq (p.equiv.unitIso.app x)).mpr hnat).symm
  change (Polygraph.lengthGrading h).codim (p.equiv.inverse.map (p.equiv.functor.map g)) = _
  rw [hv]
  exact (Polygraph.lengthGrading h).codim_iso_comp _ g _

include h in
/-- **A homogeneous polygraph's 0-cells name pairwise non-isomorphic objects of `C`** — the
comparison functor is fully faithful, hence reflects isomorphisms. -/
theorem at'_eq_of_iso {x y : GenObj P.Gen} (e : p.at' x ≅ p.at' y) : x = y :=
  Polygraph.eq_of_iso_of_homogeneous h (p.E.preimageIso e)

/-- **A 1-cell names an arrow of codimension one** — the word it is has one letter. -/
@[simp] theorem grading_arrow {x y : GenObj P.Gen} (e : x ⟶ y) :
    (p.grading h).codim (p.arrow e) = 1 :=
  (p.grading_codim_E h (P.quot.map e.toPath)).trans (Polygraph.lengthGrading_quot h e.toPath)

end Presents

/-! ## What a grading forces on every presentation

A codimension-one arrow of a category whose codimension-zero arrows are invertible is
indecomposable: the letters of a word spelling it have codimensions summing to one, so every other
letter is invertible.  Hence *every* presentation has a 1-cell for each codimension-one arrow. -/

namespace Presents

variable {P : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C] (p : Presents P C)
  (G : Grading C) (hrig : G.Rigid)

include hrig in
/-- **A word of codimension one has a letter that spells it** — the other letters have codimension
zero, hence are invertible. -/
theorem exists_cell_of_eval_codim_eq_one :
    ∀ {x y : GenObj P.Gen} (u : Quiver.Path x y), G.codim (p.eval.map u) = 1 →
      ∃ (x' y' : GenObj P.Gen) (e : x' ⟶ y') (s : p.at' x ≅ p.at' x') (t : p.at' y' ≅ p.at' y),
        p.eval.map u = s.hom ≫ p.arrow e ≫ t.hom := by
  intro x y u
  induction u with
  | nil =>
      intro hu
      rw [p.eval_nil, G.codim_id] at hu
      exact absurd hu (by omega)
  | cons u e ih =>
      intro hu
      rw [p.eval_cons, G.codim_comp] at hu
      rcases Nat.eq_zero_or_pos (G.codim (p.arrow e)) with he | he
      · haveI := hrig _ he
        obtain ⟨x', y', e', s, t, hfac⟩ := ih (by omega)
        refine ⟨x', y', e', s, t ≪≫ asIso (p.arrow e), ?_⟩
        rw [p.eval_cons, hfac, Iso.trans_hom, asIso_hom]
        simp only [Category.assoc]
      · haveI := hrig (p.eval.map u) (by omega)
        exact ⟨_, _, e, asIso (p.eval.map u), Iso.refl _,
          by rw [p.eval_cons, Iso.refl_hom, Category.comp_id, asIso_hom]⟩

include hrig in
/-- **Every codimension-one arrow is the arrow of a single 1-cell**, up to an isomorphism at each
end: a lower bound on *every* presentation of `C`. -/
theorem exists_cell_of_codim_eq_one {a b : C} (f : a ⟶ b) (hf : G.codim f = 1) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y) (u : a ≅ p.at' x) (v : p.at' y ≅ b),
      f = u.hom ≫ p.arrow e ≫ v.hom := by
  obtain ⟨⟨wa⟩, ⟨α₀⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) a
  obtain ⟨⟨wb⟩, ⟨β₀⟩⟩ := Functor.EssSurj.mem_essImage (F := p.E) b
  have α : p.at' wa ≅ a := α₀
  have β : p.at' wb ≅ b := β₀
  obtain ⟨u, hu⟩ : ∃ u : wa ⟶ wb, p.eval.map u = α.hom ≫ f ≫ β.inv := p.eval.map_surjective _
  have hcod : G.codim (p.eval.map u) = 1 := by
    rw [hu, G.codim_comp α.hom (f ≫ β.inv), G.codim_comp f β.inv,
      G.codim_eq_zero_of_isIso α.hom, G.codim_eq_zero_of_isIso β.inv, hf]
  obtain ⟨x', y', e, s, t, hfac⟩ := p.exists_cell_of_eval_codim_eq_one G hrig u hcod
  have key : α.inv ≫ (s.hom ≫ p.arrow e ≫ t.hom) ≫ β.hom = f := by
    rw [hfac.symm.trans hu]; simp
  exact ⟨x', y', e, α.symm ≪≫ s, t ≪≫ β,
    by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using key.symm⟩

end Presents

/-! ## A generator of a polygraph over another is that one's

A morphism of polygraphs sends a 1-cell to a *single* 1-cell, so a presentation admitting a
comparison to a homogeneous one has only codimension-one generators.  That is the obstruction to
homogeneity being a terminal condition: a presentation naming a composite by one letter admits no
comparison at all. -/

namespace Presents

variable {P Q : Polygraph.{w, u', w₂}} {C : Type u} [Category.{v} C]

/-- **A 1-cell of `P` names the arrow its image in `Q` names**, up to the comparison. -/
theorem arrow_eq_of_hom (F : P ⟶ Q) (p : Presents P C) (q : Presents Q C)
    (comm : F.functor ⋙ q.E ≅ p.E) {x y : GenObj P.Gen} (e : x ⟶ y) :
    p.arrow e = (comm.app ⟨x⟩).symm.hom ≫ q.arrow (F.pre.map e) ≫ (comm.app ⟨y⟩).hom := by
  have key : F.functor.map (P.quot.map e.toPath) = Q.quot.map (F.pre.map e).toPath := by
    have h := Functor.congr_hom F.quot_comp_functor e.toPath
    simpa [Prefunctor.mapPath_toPath] using h
  have hnat := comm.hom.naturality (P.quot.map e.toPath)
  simp only [Functor.comp_map, key] at hnat
  exact ((Iso.inv_comp_eq (comm.app ⟨x⟩)).mpr hnat).symm

/-- **A presentation comparable to a homogeneous one has only codimension-one 1-cells.** -/
theorem codim_arrow_of_hom (F : P ⟶ Q) (p : Presents P C) (q : Presents Q C) (hQ : Q.Homogeneous)
    (comm : F.functor ⋙ q.E ≅ p.E) {x y : GenObj P.Gen} (e : x ⟶ y) :
    (q.grading hQ).codim (p.arrow e) = 1 :=
  ((congrArg (q.grading hQ).codim (arrow_eq_of_hom F p q comm e)).trans
    ((q.grading hQ).codim_iso_comp _ _ _)).trans (q.grading_arrow hQ _)

end Presents

/-- **A word of kept letters has the letters it had.** -/
theorem length_keptWord {P : Polygraph.{w, u', w₂}} (T : ∀ {a b : P.V}, P.Gen a b → Prop)
    {x y : GenObj P.Gen} (u : Quiver.Path x y)
    (h : Quiver.Path.All (fun ⦃_ _⦄ e => T e) u) : (keptWord T u h).length = u.length :=
  (Prefunctor.length_mapPath (keptPre T) _).symm.trans
    (congrArg Quiver.Path.length (keptPre_mapPath_keptWord T u h))

/-! ## Word length in a monoid presentation and in a coproduct -/

namespace MonoidPoly

theorem length_word {S : Type} {rels : FreeMonoid S → FreeMonoid S → Prop}
    {x y : GenObj (monoidGen rels)} (P : Quiver.Path x y) : (word P).length = P.length := by
  induction P with
  | nil => rfl
  | cons P e ih =>
      rw [word_cons, FreeMonoid.length_mul, Quiver.Path.length_cons, ih, FreeMonoid.length_of]

end MonoidPoly

namespace Polygraph

/-- **A monoid presentation is homogeneous exactly when its relations preserve word length.** -/
theorem homogeneous_monoidPoly {S : Type} {rels : FreeMonoid S → FreeMonoid S → Prop}
    (h : ∀ {x y : FreeMonoid S}, rels x y → x.length = y.length) :
    (monoidPoly rels).Homogeneous :=
  fun α => (MonoidPoly.length_word _).symm.trans ((h α.2).trans (MonoidPoly.length_word _))

/-- **A coproduct is homogeneous when its legs are** — a 2-cell is a leg's, included. -/
theorem Homogeneous.coprod {ι : Type} {P : ι → Polygraph.{0, 0, 0}}
    (h : ∀ i, (P i).Homogeneous) : (Polygraph.coprod P).Homogeneous := by
  rintro _ _ ⟨α⟩
  exact (Prefunctor.length_mapPath _ _).trans
    ((h _ α).trans (Prefunctor.length_mapPath _ _).symm)

end Polygraph

end CategoryTheory

/-! ## The paper's polygraph is homogeneous

Artin's relations are `aba = bab` and `ab = ba`: three letters against three, two against two.  The
paper's polygraph maps to Artin's at the terminal `Zbp` (`paperArtinIso`) and to that one for every
`K` (`polyFunctor`), and homogeneity is reflected along both. -/

namespace ChainCat

open CategoryTheory.Polygraph CategoryTheory.Limits

/-! ## Word length is the crossing number

A letter of the paper's polygraph is a degree-one object, which crosses one pair; so a word costs
what it crosses, and the count is the same for both words of a 2-cell because crossings **add**
along a composite (`permLen_crossPerm_comp`) and the two are factorisations of one refinement.  The
contraction spells a cut by a **climb** in the weak order, and a climb takes one letter per
crossing — which is the whole of the computation. -/

namespace Paper

variable {K : BPSet}

/-- **A codimension-one refinement reads as one letter per crossing** — a merge as the empty word,
a cut out of a run as its own letter (its target holding one concurrent pair, which it must cross
because it is no merge), and any other cut as the climb its conjugate spells. -/
theorem length_cutWord {c d : Ch K} (u : c ⟶ d) (hu : codim u = 1) {N : ℕ}
    (h : dimSum c.dims = N) : (cutWord u hu).length = permLen (crossPerm h u) := by
  by_cases hW : W K u
  · rw [cutWord, dif_pos hW, readAt, Quiver.Path.length_cellCongr,
      crossPerm_eq_one_of_W h hW, permLen_one]
    rfl
  · have h0 : dimSum (zObj c.dims).dims = N := h
    have hφ : permLen (crossPerm h0 (baseMap u)) = permLen (crossPerm h u) :=
      congrArg permLen (crossPerm_eq_of_φ (g := baseMap u) (g' := u) h (zHom_φ u.φ))
    by_cases hc : IsRun K c
    · rw [cutWord_of_run (X := (⟨c, hc⟩ : Run K)) (degree_eq_one_of_isRun hc hu) hu hW, readAt,
        Quiver.Path.length_cellCongr,
        permLen_crossPerm_eq_one (X := ⟨c, hc⟩) u (degree_eq_one_of_isRun hc hu) hW h]
      rfl
    · rw [cutWord_eq_climbWord hu hW hc, readAt, Quiver.Path.length_cellCongr, cutClimbWord,
        ← runPre_atomPath (e := d) (cutClimb u)]
      refine (Prefunctor.length_mapPath runPre _).trans ((length_keptWord _ _ _).trans ?_)
      have hcl : ((atomPre (z := chV d)).mapPath (cutClimb u)).length = permLen (cutTop u).1 := by
        rw [Prefunctor.length_mapPath]
        have h := Climb.permLen_eq (cutClimb u)
        rw [shapeDescents_perm, shapeDescents_perm, shapeBot_val, permLen_one] at h
        omega
      refine hcl.trans ?_
      rw [cutTop, runOf_val, permLen_crossPerm_comp,
        show crossPerm (dimSum_replicate (dimSum d.dims)) (cutMerge u) = 1 from
          crossPerm_eq_one_of_W _ (W_runMerge _ _),
        permLen_one, Nat.zero_add, permLen_crossPerm h0]
      exact hφ

/-- **A factorisation costs what its refinement crosses** — crossings add along a composite, and
neither leg is asked where it starts. -/
theorem length_comp_cutWord {X : Run K} {m b : Ch K} {f₁ : X.chain ⟶ m} (h₁ : codim f₁ = 1)
    {f₂ : m ⟶ b} (h₂ : codim f₂ = 1) :
    ((cutWord f₂ h₂).comp (cutWord f₁ h₁)).length = permLen (runCross (f₁ ≫ f₂)) := by
  have hfst : dimSum X.chain.dims = dimSum b.dims := dimSum_eq_of_hom (f₁ ≫ f₂)
  rw [Quiver.Path.length_comp, length_cutWord f₂ h₂ (tgtStrands f₁ hfst),
    length_cutWord f₁ h₁ hfst, Nat.add_comm, ← permLen_crossPerm_comp hfst f₁ f₂]
  rfl

/-- **Both words of a codimension-two refinement out of a run cost what it crosses** — which is
homogeneity, with no relation to Artin's and no case split on the species. -/
theorem length_factorWords {X : Run K} {b : Ch K} (f : X.chain ⟶ b) (hf : codim f = 2) (ε : Bool) :
    (factorWords f hf ε).length = permLen (runCross f) :=
  (Quiver.Path.length_cellCongr _ _ _).trans
    ((length_comp_cutWord _ _).trans
      (congrArg (fun g : X.chain ⟶ b => permLen (runCross g))
        ((oneCutEquivBool f hf).symm ε).1.comp))

/-- **A 2-cell's two words are as long as its object's capacity** — the greatest refinement attains
it, and a word costs what it crosses. -/
theorem length_cellWords {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    (cellWords α ε).length = crossCap α.obj.dims :=
  (Quiver.Path.length_cellCongr _ _ _).trans
    ((length_factorWords α.hom α.codim_hom ε).trans (permLen_runCross_hom α))

/-! ## Both legs of a factorisation cross

The capacity bounds every crossing onto a shape, so the middle chain's own capacity is already
spent: the second leg cannot cross what the middle has crossed inside its beads.  Hence the first
leg crosses, and a 2-cell's two words have a last letter each. -/

/-- **A cell's first leg is not a merge** — otherwise the middle chain's own reversal, followed by
the second leg, would outrun the capacity of the cell's object. -/
theorem not_W_fst_cellFactor {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    ¬ W K (cellFactor α ε).1.fst := fun hWf => by
  have hY : dimSum Y.chain.dims = dimSum α.obj.dims := dimSum_eq_of_hom α.hom
  have hmid : degree (cellFactor α ε).1.mid = 1 := by
    have hd := degree_eq_add_codim (cellFactor α ε).1.fst
    rw [(isRun_iff_degree_eq_zero _).mp Y.property, codim_fst_cellFactor] at hd
    simpa using hd
  have hflat : permLen (crossPerm hY (cellFactor α ε).1.fst) = 0 := by
    rw [crossPerm_eq_one_of_W hY hWf, permLen_one]
  have hsplit : permLen (crossPerm hY (cellFactor α ε).1.fst)
      + permLen (crossPerm (tgtStrands (cellFactor α ε).1.fst hY) (cellFactor α ε).1.snd)
      = crossCap α.obj.dims := by
    rw [← permLen_crossPerm_comp hY, ← permLen_runCross_hom α]
    exact congrArg (fun g : Y.chain ⟶ α.obj => permLen (crossPerm hY g)) (comp_cellFactor α ε)
  have hT : dimSum (topOf (cellFactor α ε).1.mid).1.chain.dims
      = dimSum (cellFactor α ε).1.mid.dims :=
    dimSum_eq_of_hom (topOf (cellFactor α ε).1.mid).2
  have hclimb : permLen (crossPerm hT ((topOf (cellFactor α ε).1.mid).2 ≫ (cellFactor α ε).1.snd))
      = 1 + permLen (crossPerm (tgtStrands (cellFactor α ε).1.fst hY) (cellFactor α ε).1.snd) := by
    rw [permLen_crossPerm_comp hT, permLen_crossPerm (tgtStrands (cellFactor α ε).1.fst hY),
      permLen_crossPerm_eq_one (topOf (cellFactor α ε).1.mid).2 hmid
        (not_W_topOf _ (by rw [hmid]; exact one_ne_zero)) hT]
  have hbound := permLen_crossPerm_le_crossCap
    ((topOf (cellFactor α ε).1.mid).2 ≫ (cellFactor α ε).1.snd) hT
  omega

/-! ## No relation of the paper's polygraph is trivial

A word's letters are the objects they are, and the letter a first leg reads is the leg's own
target.  The two first legs of a 2-cell have different targets — a one-cut factorisation is its
middle — so the two words differ, in their last letter. -/

/-- A letter is the object it is. -/
def objPre (K : BPSet) : GenObj (Gen (K := K)) ⥤q SingleObj (FreeMonoid (Ch K)) where
  obj _ := SingleObj.star _
  map e := FreeMonoid.of e.obj

/-- **The letters of a word**, in the order the word applies them. -/
noncomputable abbrev objWord {x y : GenObj (Gen (K := K))} (w : Quiver.Path x y) :
    FreeMonoid (Ch K) := (Paths.lift (objPre K)).map w

theorem objWord_comp {x y z : GenObj (Gen (K := K))} (p : Quiver.Path x y) (q : Quiver.Path y z) :
    objWord (p.comp q) = objWord q * objWord p :=
  (Paths.lift (objPre K)).map_comp p q

@[simp] theorem objWord_cellCongr {x y x' y' : GenObj (Gen (K := K))} (hx : x = x') (hy : y = y')
    (w : Quiver.Path x y) : objWord (cellCongr Quiver.Path hx hy w) = objWord w :=
  cellCongr_const (F := Quiver.Path) (fun w => objWord w) hx hy w

/-- **A crossing cut out of a run reads as its own target** — one letter, and that letter is the
degree-one object the cut lands on. -/
theorem objWord_cutWord_of_run {X : Run K} {m : Ch K} (f : X.chain ⟶ m) (hf : codim f = 1)
    (hW : ¬ W K f) : objWord (cutWord f hf) = FreeMonoid.of m := by
  have hdeg : degree m = 1 := degree_eq_one_of_isRun X.property hf
  rw [cutWord_of_run hdeg hf hW, readAt, objWord_cellCongr]
  exact Paths.lift_toPath (objPre K) _

/-- **A factorisation's word ends in its middle** — the first leg is one letter, and that letter is
the chain it lands on. -/
theorem objWord_factorWords {X : Run K} {b : Ch K} {f : X.chain ⟶ b} (hf : codim f = 2)
    (F : OneCut f) (hW : ¬ W K F.1.fst) :
    objWord (readAt rfl (bottomRun_self X)
        ((cutWord F.1.snd (F.codim_snd hf)).comp (cutWord F.1.fst F.2)))
      = FreeMonoid.of F.1.mid * objWord (cutWord F.1.snd (F.codim_snd hf)) := by
  rw [readAt, objWord_cellCongr, objWord_comp, objWord_cutWord_of_run _ _ hW]

@[inherit_doc objWord_factorWords]
theorem objWord_cellWords {X Y : Run K} (α : Cell 2 X Y) (ε : Bool) :
    objWord (cellWords α ε) = FreeMonoid.of (cellFactor α ε).1.mid
      * objWord (cutWord (cellFactor α ε).1.snd (codim_snd_cellFactor α ε)) :=
  (objWord_cellCongr _ _ _).trans
    (objWord_factorWords α.codim_hom (cellFactor α ε) (not_W_fst_cellFactor α ε))

/-- **No relation of the paper's polygraph is trivial** — the two factorisations have different
middles, and each word ends in the letter its own middle is. -/
theorem cellWords_ne {X Y : Run K} (α : Cell 2 X Y) :
    cellWords α false ≠ cellWords α true := fun hw => by
  have hmid : (cellFactor α false).1.mid = (cellFactor α true).1.mid :=
    (List.cons.inj (congrArg FreeMonoid.toList
      ((objWord_cellWords α false).symm.trans
        ((congrArg objWord hw).trans (objWord_cellWords α true))))).1
  exact Bool.false_ne_true
    ((oneCutEquivBool α.hom α.codim_hom).symm.injective
      (Subtype.ext (Factorisation.ext hmid)))

/-! ## The cells of a dimension are the objects of that degree

A cell is its object (`Cell.ext`) and both of its ends are functions of that object, so there is no
choice in the cell *set* of any dimension: it is the fibre of `degree`. -/

/-- **The cells of dimension `n` are the objects of degree `n`** — the two runs a cell spans are
read off the object, so nothing beside it is named. -/
noncomputable def cellEquivObj (K : BPSet) (n : ℕ) :
    (Σ X Y : Run K, Cell n X Y) ≃ {e : Ch K // degree e = n} where
  toFun α := ⟨α.2.2.obj, α.2.2.degree_obj⟩
  invFun e := ⟨bottomRun e.1, (topOf e.1).1, ⟨e.1, e.2, rfl, rfl⟩⟩
  left_inv := by rintro ⟨X, Y, e, hdeg, rfl, rfl⟩; rfl
  right_inv e := Subtype.ext rfl

/-! ## The 2-cells, cut out of the tautological ones

A parallel pair of words is a **critical pair** when the two words differ, are short, and name one
arrow.  Nothing is chosen there: it is an equalizer, intersected with the complement of a diagonal,
restricted along a bound.  Every 2-cell of the paper's polygraph is a critical pair — that is
homogeneity (`length_cellWords`) and non-triviality (`cellWords_ne`) — and the critical pairs
present, because the paper's own cells are among them.

The bound is not what makes that work: *any* family of different-sided true relations containing
the paper's cells presents, by the same proof.  What the bound buys is a description of the family
with nothing chosen in it. -/

/-- A **critical pair** of the paper's 1-skeleton: two *different* words, of at most three letters
each, naming one arrow of `Ch(K)[W⁻¹]`.  Which functor names the arrow is immaterial
(`map_eq_iff_of_natIso`), so the condition is on the words alone. -/
structure Critical (K : BPSet) (x y : GenObj (Gen (K := K))) where
  /-- one word -/
  src : Quiver.Path x y
  /-- …and another -/
  tgt : Quiver.Path x y
  /-- …which is a different word -/
  ne : src ≠ tgt
  /-- …naming the same arrow -/
  sound : (paperPresents K).eval.map src = (paperPresents K).eval.map tgt
  /-- …both being short -/
  len_src : src.length ≤ 3
  /-- …both being short -/
  len_tgt : tgt.length ≤ 3

/-- **The polygraph of critical pairs**: the forced 0- and 1-cells, and *every* short non-trivial
relation that holds. -/
noncomputable def critPoly (K : BPSet) : Polygraph where
  V := Run K
  Gen := Gen
  Rel := Critical K
  src c := c.src
  tgt c := c.tgt

/-- **Every 2-cell of the paper's polygraph is a critical pair.** -/
noncomputable def criticalOfCell {X Y : Run K} (α : Cell 2 X Y) :
    Critical K (runPt X) (runPt Y) where
  src := cellWords α false
  tgt := cellWords α true
  ne := cellWords_ne α
  sound := (paperPresents K).sound α
  len_src := by
    rw [length_cellWords]
    rcases crossCap_of_degree_eq_two α.degree_obj with h | h <;> omega
  len_tgt := by
    rw [length_cellWords]
    rcases crossCap_of_degree_eq_two α.degree_obj with h | h <;> omega

/-- **…so the paper's polygraph maps to the critical one**, by the identity below dimension two. -/
noncomputable def toCritPoly (K : BPSet) : poly K ⟶ critPoly K where
  pre := 𝟭q _
  two α := criticalOfCell α
  src_two _ := (Prefunctor.mapPath_id _).symm
  tgt_two _ := (Prefunctor.mapPath_id _).symm

/-- **The critical pairs present `Ch(K)[W⁻¹]`** — sound because each names one arrow, complete
because the paper's cells are among them.  So the paper's choice of 2-cells is a choice of
*generators* for a relation that is itself canonical. -/
noncomputable def critPresents (K : BPSet) : Presents (critPoly K) (((W K).op).Localization) := by
  refine Presents.ofDesc (P := critPoly K) (paperPresents K).evalPre (fun c => ?_)
    (fun {x y u v} h => ?_) ?_ ?_
  · exact (((paperPresents K).eval_map_eq_lift _).symm.trans c.sound).trans
      ((paperPresents K).eval_map_eq_lift _)
  · have hpoly : (poly K).quot.map u = (poly K).quot.map v :=
      (paperPresents K).E.map_injective
        ((((paperPresents K).eval_map_eq_lift u).trans h).trans
          ((paperPresents K).eval_map_eq_lift v).symm)
    have hsound : ∀ (a b : (poly K).Word) (f g : a ⟶ b), (poly K).homRel f g →
        (critPoly K).quot.map f = (critPoly K).quot.map g := by
      rintro a b f g ⟨α, rfl, rfl⟩
      exact (critPoly K).quot_src_tgt (criticalOfCell α)
    have key := fun {a b : (poly K).Word} (w : a ⟶ b) =>
      Quotient.lift_map_functor_map (poly K).homRel (critPoly K).quot hsound w
    exact ((key u).symm.trans (congrArg _ hpoly)).trans (key v)
  · haveI : ((paperPresents K).eval).Full := inferInstance
    exact (Paths.lift_unique (paperPresents K).evalPre (paperPresents K).eval rfl) ▸ this
  · haveI : ((paperPresents K).eval).EssSurj := inferInstance
    exact (Paths.lift_unique (paperPresents K).evalPre (paperPresents K).eval rfl) ▸ this

/-! ## Dimension zero: a cell is its run

At degree zero there is nothing to reverse, so the merge below a chain *is* its greatest refinement
and the two runs a chain spans coincide.  A `Cell 0` is therefore the identity relation on runs —
`Run K` is `Cell 0`'s skeleton, not data beside it. -/

/-- **At degree zero the greatest refinement is the merge below** — the capacity is zero, and only
the reversals attain it. -/
theorem topOf_of_degree_eq_zero {e : Ch K} (he : degree e = 0) :
    topOf e = ⟨bottomRun e, bottomHom e⟩ :=
  (isTop_iff_eq (bottomHom e)).mp
    ((isTop_iff_wedgeRun (bottomHom e)).mpr
      (Run.compl_eq_self (wedgeRun (bottomHom e)) he).symm)

/-- **A dimension-zero cell is its source run**, read as a chain. -/
theorem Cell.obj_eq_of_zero {X Y : Run K} (α : Cell 0 X Y) : X.chain = α.obj :=
  congrArg Run.chain
    (α.below.symm.trans (bottomRun_self ⟨α.obj, (degree_eq_zero_iff _).mp α.degree_obj⟩))

/-- **…and it relates a run to itself.** -/
theorem Cell.eq_of_zero {X Y : Run K} (α : Cell 0 X Y) : X = Y :=
  (α.below.symm.trans (congrArg Sigma.fst (topOf_of_degree_eq_zero α.degree_obj)).symm).trans α.top

/-- **Every run carries one.** -/
noncomputable def Cell.zero (X : Run K) : Cell 0 X X :=
  ⟨X.chain, (isRun_iff_degree_eq_zero _).mp X.property, bottomRun_self X,
    congrArg Sigma.fst (topOf_of_degree_eq_zero ((isRun_iff_degree_eq_zero _).mp X.property))
      |>.trans (bottomRun_self X)⟩

/-- **Dimension zero is the identity relation on runs** — so the paper's 0-cells are a
*skeletalisation* of `Cell 0`, and the runs are not a fourth kind of datum. -/
noncomputable def cellZeroEquiv (X Y : Run K) : Cell 0 X Y ≃ PLift (X = Y) where
  toFun α := ⟨α.eq_of_zero⟩
  invFun h := h.down ▸ Cell.zero X
  left_inv α := Cell.ext ((Cell.obj_eq_of_zero _).symm.trans (Cell.obj_eq_of_zero α))
  right_inv _ := rfl

end Paper

/-- **The paper's polygraph is homogeneous**, for every `K` — both words of a 2-cell cost the
capacity of its object. -/
theorem homogeneous_paperPoly (K : BPSet) : (Paper.poly K).Homogeneous := fun α =>
  (Paper.length_cellWords α false).trans (Paper.length_cellWords α true).symm

/-- **Every relation of the paper's polygraph is a square or a hexagon** — two letters on each
side, or three: the commutation/braid dichotomy, uniform in `K`, and it is the capacity of a
degree-two shape. -/
theorem length_paper_src {K : BPSet} {x y : GenObj (Paper.poly K).Gen}
    (α : (Paper.poly K).Rel x y) :
    ((Paper.poly K).src α).length = 2 ∨ ((Paper.poly K).src α).length = 3 :=
  (Paper.length_cellWords α false) ▸ crossCap_of_degree_eq_two α.degree_obj

/-- **Artin's polygraph is homogeneous** — `aba = bab` and `ab = ba` preserve the letter count. -/
theorem homogeneous_artinBP : artinBP.poly.Homogeneous :=
  Homogeneous.coprod fun N => homogeneous_monoidPoly (rels := ArtinRel N) fun h => by
    cases h <;> simp [FreeMonoid.length_mul, FreeMonoid.length_of]

theorem length_paper_tgt {K : BPSet} {x y : GenObj (Paper.poly K).Gen}
    (α : (Paper.poly K).Rel x y) :
    ((Paper.poly K).tgt α).length = 2 ∨ ((Paper.poly K).tgt α).length = 3 := by
  rw [← homogeneous_paperPoly K α]
  exact length_paper_src α

/-- **As a presheaf on `PolyShape` the paper's polygraph lives on the diagonal, at 2 and at 3** —
`cell m n` is the 2-cells with an `m`-letter source and an `n`-letter target, and only the square
and the hexagon occur. -/
theorem isEmpty_shapedCell (K : BPSet) {m n : ℕ} (h : ¬ (m = n ∧ (m = 2 ∨ m = 3))) :
    IsEmpty (ShapedCell (Paper.poly K) m n) := by
  refine ⟨fun c => h ⟨c.len_src.symm.trans ((homogeneous_paperPoly K c.cell).trans c.len_tgt), ?_⟩⟩
  rcases length_paper_src c.cell with h2 | h3
  · exact Or.inl (c.len_src.symm.trans h2)
  · exact Or.inr (c.len_src.symm.trans h3)

/-! ## …so `Ch(K)[W⁻¹]` is graded, and the paper's 1-cells are its atoms -/

/-- **The crossing grading of `Ch(K)[W⁻¹]`**: the length of any word of degree-one objects spelling
an arrow.  A merge costs nothing, a degree-one object costs one. -/
noncomputable def locGrading (K : BPSet) : Grading (((W K).op).Localization) :=
  (Paper.paperPresents K).grading (homogeneous_paperPoly K)

/-- **Only the isomorphisms are free** — a word of length zero is the empty word. -/
theorem locGrading_rigid (K : BPSet) : (locGrading K).Rigid :=
  (Paper.paperPresents K).grading_rigid _

namespace Paper

variable {K : BPSet}

/-- **The arrow a cell names**: the merge below its object, inverted, then the object's greatest
refinement — from the run below the object to the run its top comes out of. -/
noncomputable abbrev cellArrow {X Y : Run K} (α : Gen X Y) :
    (paperPresents K).at' (runPt X) ⟶ (paperPresents K).at' (runPt Y) :=
  (paperPresents K).arrow (Polygraph.cell (P := poly K) α)

/-- **A degree-one object names a codimension-one arrow.** -/
@[simp] theorem codim_cellArrow {X Y : Run K} (α : Gen X Y) :
    (locGrading K).codim (cellArrow α) = 1 :=
  (paperPresents K).grading_arrow _ _

/-- **Every presentation of `Ch(K)[W⁻¹]` carries every degree-one object of `Ch K`** as a single
1-cell, up to an isomorphism at each end: the paper's 1-cells are a lower bound on every
presentation, not only on a cut-like one. -/
theorem exists_cell_of_gen {P : Polygraph.{0, 0, 0}}
    (q : Presents P (((W K).op).Localization)) {X Y : Run K} (α : Gen X Y) :
    ∃ (x y : GenObj P.Gen) (e : x ⟶ y)
      (u : (paperPresents K).at' (runPt X) ≅ q.at' x)
      (v : q.at' y ≅ (paperPresents K).at' (runPt Y)),
      cellArrow α = u.hom ≫ q.arrow e ≫ v.hom :=
  q.exists_cell_of_codim_eq_one (locGrading K) (locGrading_rigid K) _ (codim_cellArrow α)

/-- **…and the paper's 1-cells are exactly those arrows**: a codimension-one arrow of
`Ch(K)[W⁻¹]` is a degree-one object's, up to an isomorphism at each end.  With the previous result:
the 1-cells are forced, and nothing beyond them is present. -/
theorem exists_gen_of_codim_eq_one {a b : ((W K).op).Localization} (f : a ⟶ b)
    (hf : (locGrading K).codim f = 1) :
    ∃ (X Y : Run K) (α : Gen X Y) (u : a ≅ (paperPresents K).at' (runPt X))
      (v : (paperPresents K).at' (runPt Y) ≅ b),
      f = u.hom ≫ cellArrow α ≫ v.hom := by
  obtain ⟨⟨X⟩, ⟨Y⟩, e, u, v, hfac⟩ :=
    (paperPresents K).exists_cell_of_codim_eq_one (locGrading K) (locGrading_rigid K) f hf
  exact ⟨X, Y, e, u, v, hfac⟩

/-! ### …and so are the 0-cells -/

/-- **Distinct runs are non-isomorphic in `Ch(K)[W⁻¹]`** — a word from one to the other and back
has total length zero, so both are empty. -/
theorem run_eq_of_iso {X Y : Run K}
    (e : (paperPresents K).at' (runPt X) ≅ (paperPresents K).at' (runPt Y)) : X = Y :=
  congrArg GenObj.as ((paperPresents K).at'_eq_of_iso (homogeneous_paperPoly K) e)

/-- **Every presentation of `Ch(K)[W⁻¹]` has a 0-cell for each run** — essential surjectivity. -/
theorem exists_zeroCell {P : Polygraph.{0, 0, 0}} (q : Presents P (((W K).op).Localization))
    (X : Run K) : ∃ x : GenObj P.Gen, Nonempty (q.at' x ≅ (paperPresents K).at' (runPt X)) := by
  obtain ⟨⟨x⟩, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := q.E) ((paperPresents K).at' (runPt X))
  exact ⟨x, ⟨i⟩⟩

/-- **…and no 0-cell serves two runs.**  With `exists_cell_of_gen`: a presentation of
`Ch(K)[W⁻¹]` carries the paper's 0-cells and 1-cells, whatever else it carries. -/
theorem zeroCell_run_unique {P : Polygraph.{0, 0, 0}} (q : Presents P (((W K).op).Localization))
    {x : GenObj P.Gen} {X Y : Run K} (hX : q.at' x ≅ (paperPresents K).at' (runPt X))
    (hY : q.at' x ≅ (paperPresents K).at' (runPt Y)) : X = Y :=
  run_eq_of_iso (hX.symm.trans hY)

/-- **A codimension-two arrow, at three events** — an atom performed twice.  No 1-cell of the
paper's polygraph names it, so a presentation that names it by a single 1-cell admits no comparison
to the paper's (`Presents.codim_arrow_of_hom`): `poly` is not terminal among presentations. -/
theorem exists_codim_eq_two :
    ∃ (a : ((W Zbp).op).Localization) (f : a ⟶ a), (locGrading Zbp).codim f = 2 := by
  let s : artinBP.S 3 := (⟨0, by norm_num⟩ : Fin (3 - 1))
  refine ⟨_, cellArrow ((genArtinEquiv 3).symm s) ≫ cellArrow ((genArtinEquiv 3).symm s), ?_⟩
  rw [(locGrading Zbp).codim_comp, codim_cellArrow]

/-! ## What is forced, and what is not

**Dimensions 0 and 1 are minimal.**  Every presentation of `Ch(K)[W⁻¹]` carries a 0-cell per run
and a 1-cell per degree-one object (`exists_zeroCell`, `exists_cell_of_gen`), and names nothing else
of codimension one (`exists_gen_of_codim_eq_one`).

**Dimension 2 is not forced cell by cell** — a relation set is pinned only up to Tietze moves, and a
trivial relation can always be added — **and not chosen either**: the 2-cells are critical pairs,
and the critical pairs already present (`critPresents`), described with no choice and without Artin.
What the cells add is the geometry, that a degree-two object *exists* over the pair.  That is
genuinely extra: a `K` with no 3-cube has a hexagonal branching with no resolution, and must have
none, its two words being distinct arrows there.

**Where the cells come from**: `poly K` is assembled from the fibres of the discrete fibration
`Ch K ⟶ Ch Zbp`, as `poly K ≅ colim_{a ∈ Ch K} poly (zObj a.dims)` — explanatory, not proved here;
formalising it wants colimits in `Polygraph` and `Ch K ≃ Ch Zbp ↓ K`.  Read over the *cubes* instead
of the wedges it is false twice: `Run` is a coproduct of covariant hom-functors, so the pushout of
two two-edge paths at their midpoints has four runs where the colimit of the polygraphs has two; and
`BPSet.Hom` bundles the basepoints, so a bipointed `□ⁿ ⟶ K` is a cube spanning *both* of them and
`Box ↓ K` is already empty at the two-edge path. -/

end Paper

end ChainCat
