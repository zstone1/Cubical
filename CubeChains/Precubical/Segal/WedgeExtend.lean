import CubeChains.Precubical.Segal.Segal
import Mathlib.Logic.Equiv.Sum

/-!
# Precubical/Segal/WedgeExtend — lifting a (co)presheaf on `Box` to serial wedges

A functor on cubes extends to the serial wedges, functorially in every wedge map, because `⋁a` is an
iterated colimit of cubes.  Two variances, one duality, each degenerating on `F ▫0`:

* **contravariant** `F↑ X := (X.toPsh ⟶ F)` (precomposition) turns the wedge colimit into a *limit*:
  `F ▫0` a single vertex ⟹ `F↑ (⋁a)` is the product `∏ᵢ F ▫aᵢ` (`pshExtWedge2`, `pshExtProd`);
* **covariant** `F↓ X := X.toPsh ⊗_Box F`, the cubical coend `∫^n X(n) × F(n)` as a plain `Quot`
  (computable — no `Functor.lan`), turns it into a *colimit*: `F ▫0` empty ⟹ `F↓ (⋁a)` is the
  coproduct `⊕ᵢ F ▫aᵢ` (`cotensorSigmaEquiv`), a coend class then living on exactly one bead.
-/

open CategoryTheory Opposite BPSet

namespace ChainCat

/-! ## The covariant lift `F↓ X = X ⊗_Box F` — a cubical coend

`∫^n X(n) × F(n)` as a `Quot`.  The forward functoriality in `X` is what lifts a wedge map, and it
is free (post-compose the `X`-cell); co-Yoneda collapses the coend at a cube to the bead value. -/

/-- A generator of the coend `X ⊗_Box F`: an `n`-cell of `X` decorated by an element of `F ▫n`. -/
abbrev CotensorGen (F : Box ⥤ Type) (X : PrecubicalSet) : Type :=
  Σ n : ℕ, X.obj (op ▫n) × F.obj ▫n

/-- The coend (dinaturality) relation: restricting the `X`-cell along `φ` equals pushing the
`F`-decoration along `φ`.  These are exactly the morphisms of `X`'s category of elements. -/
inductive CotensorRel (F : Box ⥤ Type) (X : PrecubicalSet) :
    CotensorGen F X → CotensorGen F X → Prop
  | mk {n n' : ℕ} (φ : ▫n ⟶ ▫n') (x : X.obj (op ▫n')) (y : F.obj ▫n) :
      CotensorRel F X ⟨n, (X.map φ.op) x, y⟩ ⟨n', x, (F.map φ) y⟩

/-- `X ⊗_Box F` — the cubical coend of a precubical set `X` with a copresheaf `F`. -/
def Cotensor (F : Box ⥤ Type) (X : PrecubicalSet) : Type := Quot (CotensorRel F X)

/-- A decorated cell, as a coend class. -/
def Cotensor.mk (F : Box ⥤ Type) {X : PrecubicalSet} (n : ℕ) (x : X.obj (op ▫n))
    (y : F.obj ▫n) : Cotensor F X := Quot.mk _ ⟨n, x, y⟩

/-- **The coend identity.**  Restrict-then-decorate = decorate-then-push. -/
theorem Cotensor.map_mk (F : Box ⥤ Type) {X : PrecubicalSet} {n n' : ℕ} (φ : ▫n ⟶ ▫n')
    (x : X.obj (op ▫n')) (y : F.obj ▫n) :
    Cotensor.mk F n ((X.map φ.op) x) y = Cotensor.mk F n' x ((F.map φ) y) :=
  Quot.sound (CotensorRel.mk φ x y)

@[elab_as_elim]
theorem Cotensor.ind (F : Box ⥤ Type) {X : PrecubicalSet} {motive : Cotensor F X → Prop}
    (h : ∀ (n : ℕ) (x : X.obj (op ▫n)) (y : F.obj ▫n), motive (Cotensor.mk F n x y)) :
    ∀ t, motive t := fun t => Quot.ind (fun p => h p.1 p.2.1 p.2.2) t

/-- **Functoriality of the coend in `X`** — precompose the `X`-cell with `g`.  This is the whole
lift; it needs nothing but naturality of `g`. -/
def Cotensor.map (F : Box ⥤ Type) {X Y : PrecubicalSet} (g : X ⟶ Y) :
    Cotensor F X → Cotensor F Y :=
  Quot.lift (fun p => Cotensor.mk F p.1 (g⟪p.1⟫ p.2.1) p.2.2) <| by
    rintro _ _ ⟨φ, x, y⟩
    change Cotensor.mk F _ (g⟪_⟫ ((X.map φ.op) x)) y = Cotensor.mk F _ (g⟪_⟫ x) ((F.map φ) y)
    rw [NatTrans.naturality_apply g φ.op x]
    exact Cotensor.map_mk F φ (g⟪_⟫ x) y

@[simp] theorem Cotensor.map_apply (F : Box ⥤ Type) {X Y : PrecubicalSet} (g : X ⟶ Y)
    (n : ℕ) (x : X.obj (op ▫n)) (y : F.obj ▫n) :
    Cotensor.map F g (Cotensor.mk F n x y) = Cotensor.mk F n (g⟪n⟫ x) y := rfl

theorem Cotensor.map_id (F : Box ⥤ Type) (X : PrecubicalSet) :
    Cotensor.map F (𝟙 X) = id := by
  funext t
  refine Cotensor.ind F (fun n x y => ?_) t
  simp only [Cotensor.map_apply, id_eq, NatTrans.id_app, types_id_apply]

theorem Cotensor.map_comp (F : Box ⥤ Type) {X Y Z : PrecubicalSet} (g : X ⟶ Y) (h : Y ⟶ Z) :
    Cotensor.map F (g ≫ h) = Cotensor.map F h ∘ Cotensor.map F g := by
  funext t
  refine Cotensor.ind F (fun n x y => ?_) t
  simp only [Function.comp_apply, Cotensor.map_apply, NatTrans.comp_app, types_comp_apply]

/-- **The coend as a bundled functor** `PrecubicalSet ⥤ Type`. -/
def CotensorFunctor (F : Box ⥤ Type) : PrecubicalSet ⥤ Type where
  obj X := Cotensor F X
  map g := TypeCat.ofHom (Cotensor.map F g)
  map_id X := by
    apply ConcreteCategory.hom_ext; intro t
    change Cotensor.map F (𝟙 X) t = t
    simp only [Cotensor.map_id, id_eq]
  map_comp g h := by
    apply ConcreteCategory.hom_ext; intro t
    change Cotensor.map F (g ≫ h) t = Cotensor.map F h (Cotensor.map F g t)
    simp only [Cotensor.map_comp, Function.comp_apply]

/-- **The covariant lift** `F↓ : BPSet ⥤ Type`, `X ↦ X.toPsh ⊗_Box F`. -/
def cotensorLift (F : Box ⥤ Type) : BPSet ⥤ Type := BPSet.toPshFunctor ⋙ CotensorFunctor F

/-- Fuse two coend functorialities: post-composing the underlying maps. -/
theorem Cotensor.map_map (F : Box ⥤ Type) {X Y Z : PrecubicalSet} (g : X ⟶ Y) (h : Y ⟶ Z)
    (t : Cotensor F X) : Cotensor.map F h (Cotensor.map F g t) = Cotensor.map F (g ≫ h) t :=
  (congrFun (Cotensor.map_comp F g h) t).symm

/-- `F↓`'s action on a coend value is the underlying map's coend functoriality. -/
@[simp] theorem cotensorLift_map_apply (F : Box ⥤ Type) {X Y : BPSet} (f : X ⟶ Y)
    (t : (cotensorLift F).obj X) : (cotensorLift F).map f t = Cotensor.map F f.hom t := rfl

def Cotensor.cubeEquiv (F : Box ⥤ Type) (m : ℕ) :
    Cotensor F (yoneda.obj ▫m) ≃ F.obj ▫m where
  toFun := Quot.lift (fun p => (F.map p.2.1) p.2.2) <| by
    rintro _ _ ⟨φ, x, y⟩
    change (F.map ((yoneda.obj ▫m).map φ.op x)) y = (F.map x) ((F.map φ) y)
    have hx : (yoneda.obj ▫m).map φ.op x = φ ≫ x := rfl
    rw [hx, Functor.map_comp_apply]
  invFun z := Cotensor.mk F m (𝟙 ▫m) z
  left_inv := by
    refine Cotensor.ind F (fun n x y => ?_)
    change Cotensor.mk F m (𝟙 ▫m) ((F.map x) y) = Cotensor.mk F n x y
    have key := Cotensor.map_mk F (X := yoneda.obj ▫m) x (𝟙 ▫m) y
    have hx : (yoneda.obj ▫m).map x.op (𝟙 ▫m) = x := by
      change x ≫ 𝟙 ▫m = x
      rw [Category.comp_id]
    rw [hx] at key
    exact key.symm
  right_inv z := by
    change (F.map (𝟙 ▫m)) z = z
    rw [Functor.map_id_apply]

section Wedge2
variable {F : Box ⥤ Type}

/-- Split a coend class of `X ∨ Y` onto its bead.  `descCell` cases the wedge cell; the glue
condition is vacuous because a shared vertex would decorate the empty `F ▫0`. -/
def Cotensor.wedge2Fwd (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) :
    Cotensor F (X ∨ Y).toPsh → Cotensor F X.toPsh ⊕ Cotensor F Y.toPsh :=
  Quot.lift
    (fun p => Glue.descCell (f := X.finalVertex) (g := Y.initVertex) (op ▫p.1)
      (fun x => Sum.inl (Cotensor.mk F p.1 x p.2.2))
      (fun z => Sum.inr (Cotensor.mk F p.1 z p.2.2))
      (fun s => (hF.false ((F.map s) p.2.2)).elim) p.2.1) <| by
    rintro _ _ ⟨φ, c, y⟩
    rcases CubeChain.glue0_cell_cases X.finalVertex Y.initVertex _ c with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · dsimp only
      have hnat : (X ∨ Y).toPsh.map φ.op ((Glue.inl X.finalVertex Y.initVertex)⟪_⟫ x)
          = (Glue.inl X.finalVertex Y.initVertex)⟪_⟫ (X.toPsh.map φ.op x) :=
        (NatTrans.naturality_apply (Glue.inl X.finalVertex Y.initVertex) φ.op x).symm
      rw [hnat, Glue.descCell_inl, Glue.descCell_inl]
      exact congrArg Sum.inl (Cotensor.map_mk F φ x y)
    · dsimp only
      have hnat : (X ∨ Y).toPsh.map φ.op ((Glue.inr X.finalVertex Y.initVertex)⟪_⟫ z)
          = (Glue.inr X.finalVertex Y.initVertex)⟪_⟫ (Y.toPsh.map φ.op z) :=
        (NatTrans.naturality_apply (Glue.inr X.finalVertex Y.initVertex) φ.op z).symm
      rw [hnat, Glue.descCell_inr, Glue.descCell_inr]
      exact congrArg Sum.inr (Cotensor.map_mk F φ z y)

/-- Assemble bead classes into a coend class of `X ∨ Y` — the two wedge inclusions. -/
def Cotensor.wedge2Bwd (X Y : BPSet) :
    Cotensor F X.toPsh ⊕ Cotensor F Y.toPsh → Cotensor F (X ∨ Y).toPsh :=
  Sum.elim (Cotensor.map F (Glue.inl X.finalVertex Y.initVertex))
    (Cotensor.map F (Glue.inr X.finalVertex Y.initVertex))

@[simp] theorem Cotensor.wedge2Fwd_inl (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) (n : ℕ)
    (x : X.cells n) (y : F.obj ▫n) :
    Cotensor.wedge2Fwd hF X Y
        (Cotensor.mk F n ((Glue.inl X.finalVertex Y.initVertex)⟪n⟫ x) y)
      = Sum.inl (Cotensor.mk F n x y) :=
  Glue.descCell_inl (f := X.finalVertex) (g := Y.initVertex) (op ▫n)
    (h := fun x => Sum.inl (Cotensor.mk F n x y))
    (k := fun z => Sum.inr (Cotensor.mk F n z y))
    (w := fun s => (hF.false ((F.map s) y)).elim) x

@[simp] theorem Cotensor.wedge2Fwd_inr (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) (n : ℕ)
    (z : Y.cells n) (y : F.obj ▫n) :
    Cotensor.wedge2Fwd hF X Y
        (Cotensor.mk F n ((Glue.inr X.finalVertex Y.initVertex)⟪n⟫ z) y)
      = Sum.inr (Cotensor.mk F n z y) :=
  Glue.descCell_inr (f := X.finalVertex) (g := Y.initVertex) (op ▫n)
    (h := fun x => Sum.inl (Cotensor.mk F n x y))
    (k := fun z => Sum.inr (Cotensor.mk F n z y))
    (w := fun s => (hF.false ((F.map s) y)).elim) z

/-- **`F↓` sends the wedge to a coproduct.**  The dual of `pshExtWedge2`. -/
def Cotensor.wedge2Equiv (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet) :
    Cotensor F (X ∨ Y).toPsh ≃ Cotensor F X.toPsh ⊕ Cotensor F Y.toPsh where
  toFun := Cotensor.wedge2Fwd hF X Y
  invFun := Cotensor.wedge2Bwd X Y
  left_inv := by
    refine Cotensor.ind F (fun n c y => ?_)
    rcases CubeChain.glue0_cell_cases X.finalVertex Y.initVertex n c with ⟨x, rfl⟩ | ⟨z, rfl⟩
    · rw [Cotensor.wedge2Fwd_inl]
      exact Cotensor.map_apply F (Glue.inl X.finalVertex Y.initVertex) n x y
    · rw [Cotensor.wedge2Fwd_inr]
      exact Cotensor.map_apply F (Glue.inr X.finalVertex Y.initVertex) n z y
  right_inv := by
    rintro (u | u)
    · exact Cotensor.ind F (fun n x y => Cotensor.wedge2Fwd_inl hF X Y n x y) u
    · exact Cotensor.ind F (fun n z y => Cotensor.wedge2Fwd_inr hF X Y n z y) u

/-- **Monoidality, binary**: under the decomposition, a wedge inclusion is a coproduct injection. -/
@[simp] theorem Cotensor.wedge2Equiv_map_inl (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet)
    (u : Cotensor F X.toPsh) :
    Cotensor.wedge2Equiv hF X Y (Cotensor.map F (wedgeInl X Y) u) = Sum.inl u :=
  (Cotensor.wedge2Equiv hF X Y).apply_symm_apply (Sum.inl u)

@[simp] theorem Cotensor.wedge2Equiv_map_inr (hF : IsEmpty (F.obj ▫0)) (X Y : BPSet)
    (u : Cotensor F Y.toPsh) :
    Cotensor.wedge2Equiv hF X Y (Cotensor.map F (wedgeInr X Y) u) = Sum.inr u :=
  (Cotensor.wedge2Equiv hF X Y).apply_symm_apply (Sum.inr u)

/-- Fin-surgery moving the head bead to index `0`: `F ▫c ⊕ (⊕ over rest) ≃ ⊕ over (c :: rest)` in
`Sigma` form.  The `get`-index rewrites are all definitional (`(c::rest).get 0 = c`,
`(c::rest).get j.succ = rest.get j`), so no transport is spelled. -/
def cotensorSigmaSurgery (F : Box ⥤ Type) (c : ℕ+) (rest : List ℕ+) :
    F.obj ▫(c : ℕ) ⊕ (Σ i : Fin rest.length, F.obj ▫((rest.get i : ℕ)))
      ≃ Σ i : Fin (c :: rest).length, F.obj ▫(((c :: rest).get i : ℕ)) where
  toFun := Sum.elim (fun x => ⟨0, x⟩) (fun p => ⟨p.1.succ, p.2⟩)
  invFun p :=
    Fin.cases (motive := fun i => F.obj ▫(((c :: rest).get i : ℕ)) →
        F.obj ▫(c : ℕ) ⊕ (Σ i : Fin rest.length, F.obj ▫((rest.get i : ℕ))))
      (fun x => Sum.inl x) (fun j x => Sum.inr ⟨j, x⟩) p.1 p.2
  left_inv := by rintro (x | ⟨j, x⟩) <;> simp [Fin.cases_succ]
  right_inv := by rintro ⟨i, x⟩; induction i using Fin.cases <;> simp

/-- **The flat `Sigma` presentation of the covariant lift** — one bead value `F ▫aᵢ` per bead,
indexed by `Fin a.length`. -/
def cotensorSigmaEquiv (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) :
    (a : List ℕ+) → Cotensor F (⋁a).toPsh ≃ Σ i : Fin a.length, F.obj ▫((a.get i : ℕ))
  | [] =>
    haveI : IsEmpty (F.obj ▫0) := hF
    haveI : IsEmpty (Cotensor F (⋁([] : List ℕ+)).toPsh) := (Cotensor.cubeEquiv F 0).isEmpty
    haveI : IsEmpty (Σ i : Fin ([] : List ℕ+).length, F.obj ▫(([] : List ℕ+).get i : ℕ)) :=
      ⟨fun x => x.1.elim0⟩
    Equiv.equivOfIsEmpty _ _
  | c :: rest =>
    (Cotensor.wedge2Equiv hF (□(c : ℕ)) (⋁rest)).trans
      (((Cotensor.cubeEquiv F (c : ℕ)).sumCongr (cotensorSigmaEquiv F hF rest)).trans
        (cotensorSigmaSurgery F c rest))

/-- **Computing `cotensorSigmaEquiv.symm`**: `⟨i, x⟩` is bead `i`'s inclusion `ιᵂ a i` decorated by
`x`.  The β-rule for the flattened coproduct equiv — short because the backward maps *are*
`Cotensor.map` of the wedge injections (`wedge2Bwd`), so each cons step is one `map` fusion. -/
theorem cotensorSigmaEquiv_symm_apply (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0)) :
    ∀ (a : List ℕ+) (i : Fin a.length) (x : F.obj ▫((a.get i : ℕ))),
      (cotensorSigmaEquiv F hF a).symm ⟨i, x⟩
        = Cotensor.map F (ιᵂ a i) ((Cotensor.cubeEquiv F (a.get i : ℕ)).symm x)
  | [], i, _ => i.elim0
  | c :: rest, i, x => by
      induction i using Fin.cases with
      | zero => rfl
      | succ j =>
          change Cotensor.map F (wedgeInr (□(c : ℕ)) (⋁rest))
              ((cotensorSigmaEquiv F hF rest).symm ⟨j, x⟩) = _
          rw [cotensorSigmaEquiv_symm_apply F hF rest j x]
          exact (congrFun (Cotensor.map_comp F (ιᵂ rest j) (wedgeInr (□(c : ℕ)) (⋁rest))) _).symm

/-- Forward form of `cotensorSigmaEquiv_symm_apply`. -/
theorem cotensorSigmaEquiv_apply_map (F : Box ⥤ Type) (hF : IsEmpty (F.obj ▫0))
    (a : List ℕ+) (i : Fin a.length) (x : F.obj ▫((a.get i : ℕ))) :
    cotensorSigmaEquiv F hF a
        (Cotensor.map F (ιᵂ a i) ((Cotensor.cubeEquiv F (a.get i : ℕ)).symm x)) = ⟨i, x⟩ :=
  (Equiv.eq_symm_apply _).mp (cotensorSigmaEquiv_symm_apply F hF a i x).symm

end Wedge2

/-! ## The contravariant lift `F↑ X = (X.toPsh ⟶ F)`

The `Concurrency/Executions/Runs` machinery, abstracted off `runPresheaf`.  `F↑` is a hom-set, so it
needs no carrier of its own: the functor is `pshExtFunctor` (`Precubical/Segal/PshExtMonoidal`) and
the classifying object is `(⋁a).toPsh ⟶ F` itself — no descent to a product of bead-values is
forced; that descent is the *monoidal* content (`pshExtWedge2`), the general form of "`Run` is
monoidal". -/

def pshExtWedge2 (F : PrecubicalSet) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) (X Y : BPSet) :
    ((X ∨ Y).toPsh ⟶ F) ≃ (X.toPsh ⟶ F) × (Y.toPsh ⟶ F) where
  toFun φ := (Glue.inl X.finalVertex Y.initVertex ≫ φ, Glue.inr X.finalVertex Y.initVertex ≫ φ)
  invFun p := Glue.desc (f := X.finalVertex) (g := Y.initVertex) p.1 p.2 (hF _ _)
  left_inv φ := Glue.hom_ext (by rw [Glue.inl_desc]) (by rw [Glue.inr_desc])
  right_inv p := by
    refine Prod.ext ?_ ?_
    · exact Glue.inl_desc _ _ _
    · exact Glue.inr_desc _ _ _

/-- The iterated product a wedge decomposes to: one bead value per bead. -/
def pshExtProdType (F : PrecubicalSet) : List ℕ+ → Type
  | [] => PUnit
  | c :: rest => ((□(c : ℕ)).toPsh ⟶ F) × pshExtProdType F rest

/-- **`F↑` sends a serial wedge to the iterated product of bead values** — the general
`runSegalProd`.  `pt` inhabits the empty-wedge value, `hF` collapses it. -/
def pshExtProd (F : PrecubicalSet) (pt : (□0).toPsh ⟶ F) (hF : ∀ p q : (□0).toPsh ⟶ F, p = q) :
    (a : List ℕ+) → ((⋁a).toPsh ⟶ F) ≃ pshExtProdType F a
  | [] =>
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => pt
      left_inv := fun φ => hF pt φ
      right_inv := fun _ => rfl }
  | c :: rest =>
    (pshExtWedge2 F hF (□(c : ℕ)) (⋁rest)).trans
      ((Equiv.refl ((□(c : ℕ)).toPsh ⟶ F)).prodCongr (pshExtProd F pt hF rest))

end ChainCat
