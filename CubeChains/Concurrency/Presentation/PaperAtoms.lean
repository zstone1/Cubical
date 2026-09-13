import CubeChains.Concurrency.Presentation.PaperArtin
import CubeChains.Concurrency.Presentation.PaperFunctor
import CubeChains.Foundations.Polygraph.Presheaf
import CubeChains.Machinery.Grading

/-!
# Concurrency/Presentation/PaperAtoms — the paper's 1-cells are forced

A polygraph is **homogeneous** when each 2-cell relates two words of the *same* length; word length
is then a grading of the category it presents, vanishing only on the isomorphisms.  Such a grading
pins the cells of *every* presentation: a codimension-one arrow has a single letter spelling it, and
0-cells name pairwise non-isomorphic objects.

`poly K` is homogeneous, mapping to Artin's polygraph (`aba = bab`, `ab = ba`) through the terminal
`Zbp`.  So its 0-cells and 1-cells are forced, and its 2-cells are squares and hexagons and nothing
else.
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

/-- **An Artin relation relates words of equal length** — of two letters, or of three: commutation
or braiding, and nothing else. -/
theorem artinRel_length {n : ℕ} {x y : FreeMonoid (Fin (n - 1))} (h : ArtinRel n x y) :
    x.length = y.length ∧ (x.length = 2 ∨ x.length = 3) := by
  cases h
  · exact ⟨by simp [FreeMonoid.length_mul, FreeMonoid.length_of],
      Or.inl (by simp [FreeMonoid.length_mul, FreeMonoid.length_of])⟩
  · exact ⟨by simp [FreeMonoid.length_mul, FreeMonoid.length_of],
      Or.inr (by simp [FreeMonoid.length_mul, FreeMonoid.length_of])⟩

theorem homogeneous_artinP (N : ℕ) : (artinBP.P N).Homogeneous :=
  homogeneous_monoidPoly (rels := ArtinRel N) fun h => (artinRel_length h).1

theorem length_src_artinP {N : ℕ} {x y : GenObj (artinBP.P N).Gen} (β : (artinBP.P N).Rel x y) :
    ((artinBP.P N).src β).length = 2 ∨ ((artinBP.P N).src β).length = 3 :=
  (MonoidPoly.length_word (rels := ArtinRel N) β.1.1) ▸ (artinRel_length β.2).2

theorem length_src_artin {A B : GenObj artinBP.poly.Gen} (γ : artinBP.poly.Rel A B) :
    (artinBP.poly.src γ).length = 2 ∨ (artinBP.poly.src γ).length = 3 := by
  cases γ with
  | @mk N x y β =>
      have h : (artinBP.poly.src (CoprodRel.mk β)).length = ((artinBP.P N).src β).length :=
        Prefunctor.length_mapPath _ _
      rw [h]
      exact length_src_artinP β

theorem homogeneous_artinBP : artinBP.poly.Homogeneous :=
  Homogeneous.coprod homogeneous_artinP

/-- **The paper's polygraph maps to Artin's, for every `K`** — through the terminal `Zbp`, where it
*is* Artin's. -/
noncomputable def artinCompare (K : BPSet) : Paper.poly K ⟶ artinBP.poly :=
  Paper.polyMap (isTerminalZbp.from K) ≫ Paper.paperArtinIso.hom

/-- **The paper's polygraph is homogeneous**, for every `K`. -/
theorem homogeneous_paperPoly (K : BPSet) : (Paper.poly K).Homogeneous :=
  Homogeneous.of_hom (artinCompare K) homogeneous_artinBP

/-- **Every relation of the paper's polygraph is a square or a hexagon** — two letters on each
side, or three: the commutation/braid dichotomy, uniform in `K`. -/
theorem length_paper_src {K : BPSet} {x y : GenObj (Paper.poly K).Gen}
    (α : (Paper.poly K).Rel x y) :
    ((Paper.poly K).src α).length = 2 ∨ ((Paper.poly K).src α).length = 3 := by
  have h : (artinBP.poly.src ((artinCompare K).two α)).length = ((Paper.poly K).src α).length := by
    rw [(artinCompare K).src_two α, Prefunctor.length_mapPath]
  rw [← h]
  exact length_src_artin _

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

end Paper

end ChainCat
