import CubeChains.Braid.SalvettiQuotient
import CubeChains.Braid.CubePureBraidResult
import CubeChains.Foundations.DeckExact
import CubeChains.Foundations.ShortFive
import Mathlib.CategoryTheory.SingleObj

/-!
# Braid/SalvettiDeckCompat — the right square of the braid five-lemma ladder (dev)
-/

open CategoryTheory CategoryTheory.FreeGroupoid OrderQuotient

namespace CubeChains

/-! ## Step 1 — the free-groupoid frame formula -/

/-- The iso `star ≅ star` in `SingleObj G` given by a group element. -/
def singleObjIso {G : Type*} [Group G] (g : G) :
    (SingleObj.star G ≅ SingleObj.star G) where
  hom := g
  inv := g⁻¹
  hom_inv_id := by rw [SingleObj.comp_as_mul, SingleObj.id_as_one, inv_mul_cancel]
  inv_hom_id := by rw [SingleObj.comp_as_mul, SingleObj.id_as_one, mul_inv_cancel]

@[simp] theorem singleObjIso_hom {G : Type*} [Group G] (g : G) : (singleObjIso g).hom = g := rfl

/-- The natural iso witnessing the frame formula: `lift (differenceFunctor fn) ≅ const star`, with
component `(fn c)⁻¹` at `mk c`. -/
noncomputable def frameNatIso {C G : Type*} [Category C] [Group G] (fn : C → G) :
    FreeGroupoid.lift (SingleObj.differenceFunctor fn)
      ≅ (Functor.const (FreeGroupoid C)).obj (SingleObj.star G) :=
  liftNatIso _ _ (NatIso.ofComponents (fun c => singleObjIso ((fn c)⁻¹)) (by
    intro c c' e
    have hlift : (FreeGroupoid.lift (SingleObj.differenceFunctor fn)).map (homMk e)
        = (SingleObj.differenceFunctor fn).map e := by
      have h := Functor.congr_hom (lift_spec (SingleObj.differenceFunctor fn)) e
      simpa using h
    show (FreeGroupoid.lift (SingleObj.differenceFunctor fn)).map (homMk e)
        ≫ (singleObjIso ((fn c')⁻¹)).hom
      = (singleObjIso ((fn c)⁻¹)).hom ≫ _
    rw [hlift]
    simp only [SingleObj.differenceFunctor_map, singleObjIso_hom, Functor.comp_map,
      Functor.const_obj_map, SingleObj.comp_as_mul, SingleObj.id_as_one]
    group))

/-- **Frame formula.**  The free-groupoid lift of a difference functor sends a morphism
`mk u ⟶ mk v` to `fn v * (fn u)⁻¹`. -/
theorem lift_differenceFunctor_map {C G : Type*} [Category C] [Group G] (fn : C → G)
    {u v : C} (w : (mk u : FreeGroupoid C) ⟶ mk v) :
    (FreeGroupoid.lift (SingleObj.differenceFunctor fn)).map w = fn v * (fn u)⁻¹ := by
  have hnat := (frameNatIso fn).hom.naturality w
  simp only [frameNatIso, liftNatIso_hom_app, NatIso.ofComponents_hom_app, singleObjIso_hom,
    Functor.const_obj_map, SingleObj.comp_as_mul, SingleObj.id_as_one, one_mul] at hnat
  rw [inv_mul_eq_iff_eq_mul] at hnat
  exact hnat

/-- The lift of a functor into a groupoid, postcomposed, is the lift of the composite. -/
theorem lift_comp {C H K : Type*} [Category C] [Groupoid H] [Groupoid K]
    (F : C ⥤ H) (P : H ⥤ K) : FreeGroupoid.lift F ⋙ P = FreeGroupoid.lift (F ⋙ P) := by
  apply FreeGroupoid.lift_unique
  rw [← Functor.assoc, lift_spec]

/-! ## Step 2 — the covering carries `ThetaQ` to the upstairs frame -/

variable {n : ℕ}

/-- `permHom n` as a functor between single-object groupoids. -/
noncomputable def permFunctor (n : ℕ) :
    SingleObj (Braid n) ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  SingleObj.mapHom (Braid n) (Equiv.Perm (Fin n)) (permHom n)

@[simp] theorem permFunctor_map {a b : SingleObj (Braid n)} (g : a ⟶ b) :
    (permFunctor n).map g = permHom n g := rfl

/-- The `Sₙ`-valued crossing grading on the quotient category. -/
noncomputable def crossGradQuot (n : ℕ) :
    QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)) ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  salvettiGradingQuot n ⋙ permFunctor n

theorem crossGradQuot_map {X Y : QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))} (f : X ⟶ Y) :
    (crossGradQuot n).map f = crossPermQuot f := by
  show permHom n ((salvettiGradingQuot n).map f) = crossPermQuot f
  rw [salvettiGradingQuot_map, permHom_ofPerm]

/-- The underlying-permutation reduction of the middle vertical map, as a free-groupoid lift. -/
noncomputable def ThetaQ (n : ℕ) :
    FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))
      ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  FreeGroupoid.lift (crossGradQuot n)

/-- The upstairs frame functor: the Salvetti crossing difference on the poset. -/
noncomputable def frameUp (n : ℕ) :
    FreeGroupoid (Sal (braidCOM n)) ⥤ SingleObj (Equiv.Perm (Fin n)) :=
  FreeGroupoid.lift (SingleObj.differenceFunctor
    (fun a : Sal (braidCOM n) => topePerm a))

/-- The middle vertical map, then `permHom`, is `ThetaQ`. -/
theorem salvettiConstructionQuot_comp_permFunctor (n : ℕ) :
    salvettiConstructionQuot n ⋙ permFunctor n = ThetaQ n := by
  rw [salvettiConstructionQuot, ThetaQ, lift_comp]; rfl

/-- `permHom` of the descended braid is `ThetaQ` (bridge to the crossing grading). -/
theorem permHom_salvettiConstructionQuot
    {γ Y : FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))} (g : γ ⟶ Y) :
    permHom n ((salvettiConstructionQuot n).map g) = (ThetaQ n).map g := by
  have h := Functor.congr_hom (salvettiConstructionQuot_comp_permFunctor n) g
  simpa using h

/-- The `Sₙ`-quotient covering carries `ThetaQ` to the upstairs frame. -/
theorem quotCover_comp_ThetaQ (n : ℕ) : quotCover n ⋙ ThetaQ n = frameUp n := by
  have hbase : OrderQuotient.quotFunctor (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n))
        ⋙ crossGradQuot n
      = SingleObj.differenceFunctor (fun a : Sal (braidCOM n) => topePerm a) := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) (fun a b f => ?_)
    show (crossGradQuot n).map (OrderQuotient.quotFunctor.map f)
        = (SingleObj.differenceFunctor (fun a : Sal (braidCOM n) => topePerm a)).map f
    rw [crossGradQuot_map, SingleObj.differenceFunctor_map]
    rfl
  rw [quotCover, ThetaQ, FreeGroupoid.map_comp_lift, hbase, frameUp]

/-! ## Step 3 — the loop frame identity -/

/-- **Loop frame identity.**  `ThetaQ` of a loop at `⟦x⟧` is the frame difference between the lift
endpoint and `x`: `topePerm (endpt x γ) * (topePerm x)⁻¹`. -/
theorem thetaQ_map_loop (n : ℕ) (x : Sal (braidCOM n))
    (γ : (mk (Quotient.mk'' x) :
          FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))) ⟶ mk (Quotient.mk'' x)) :
    (ThetaQ n).map γ = topePerm (OrderQuotient.endpt x γ) * (topePerm x)⁻¹ := by
  set w := (wordFunctor (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))).preimage γ with hwdef
  have hw : (wordFunctor (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))).map w = γ :=
    (wordFunctor (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))).map_preimage γ
  set L := liftPS (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)) x ⟨_, w⟩ with hLdef
  have hsym : pathLiftEquiv (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)) x L = ⟨_, w⟩ :=
    (pathLiftEquiv (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)) x).apply_symm_apply _
  rw [pathLiftEquiv_apply, Prefunctor.pathStar_apply] at hsym
  set Ψ := wordFunctor (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))) ⋙ ThetaQ n with hΨdef
  have hcong := congrArg
    (fun s : Quiver.PathStar ((quotFunctor (G := Equiv.Perm (Fin n))
        (P := Sal (braidCOM n))).toPrefunctor.symmetrify.obj x) =>
      Ψ.map (X := (quotFunctor (G := Equiv.Perm (Fin n))
        (P := Sal (braidCOM n))).toPrefunctor.symmetrify.obj x) (Y := s.1) s.2)
    hsym
  simp only at hcong
  -- hcong : Ψ.map (φ.mapPath L.2) = Ψ.map w
  have key : Ψ.map ((quotFunctor (G := Equiv.Perm (Fin n))
        (P := Sal (braidCOM n))).toPrefunctor.symmetrify.mapPath L.2)
      = (frameUp n).map ((wordFunctor (Sal (braidCOM n))).map L.2) := by
    show (ThetaQ n).map ((wordFunctor (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))).map
        ((quotFunctor (G := Equiv.Perm (Fin n))
          (P := Sal (braidCOM n))).toPrefunctor.symmetrify.mapPath L.2)) = _
    rw [← map_quotFunctor_wordFunctor (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)) L.2]
    show (quotCover n ⋙ ThetaQ n).map ((wordFunctor (Sal (braidCOM n))).map L.2) = _
    rw [quotCover_comp_ThetaQ]
  have hendpt : OrderQuotient.endpt x γ = L.1 := rfl
  rw [hendpt]
  calc (ThetaQ n).map γ
      = Ψ.map w := by rw [← hw]; rfl
    _ = Ψ.map ((quotFunctor (G := Equiv.Perm (Fin n))
          (P := Sal (braidCOM n))).toPrefunctor.symmetrify.mapPath L.2) := hcong.symm
    _ = (frameUp n).map ((wordFunctor (Sal (braidCOM n))).map L.2) := key
    _ = topePerm L.1 * (topePerm x)⁻¹ :=
        lift_differenceFunctor_map (fun a : Sal (braidCOM n) => topePerm a)
          ((wordFunctor (Sal (braidCOM n))).map L.2)

/-! ## Step 4 — upstairs loops are pure braids -/

/-- The upstairs grading, then `permHom`, is the frame difference on the poset. -/
theorem salvettiGrading_comp_permFunctor (n : ℕ) :
    salvettiGrading n ⋙ permFunctor n
      = SingleObj.differenceFunctor (fun a : Sal (braidCOM n) => topePerm a) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) (fun a b f => ?_)
  show permHom n (ofPerm (crossPerm a b))
      = (SingleObj.differenceFunctor (fun a : Sal (braidCOM n) => topePerm a)).map f
  rw [permHom_ofPerm, SingleObj.differenceFunctor_map]
  rfl

theorem salvettiConstruction_comp_permFunctor (n : ℕ) :
    salvettiConstruction n ⋙ permFunctor n = frameUp n := by
  rw [salvettiConstruction, frameUp, lift_comp, salvettiGrading_comp_permFunctor]

theorem permHom_salvettiConstruction {u v : FreeGroupoid (Sal (braidCOM n))} (g : u ⟶ v) :
    permHom n ((salvettiConstruction n).map g) = (frameUp n).map g := by
  have h := Functor.congr_hom (salvettiConstruction_comp_permFunctor n) g
  simpa using h

/-- **Loops upstairs are pure.**  A loop at `mk x` upstairs maps to a braid with trivial underlying
permutation — its frame difference is `topePerm x * (topePerm x)⁻¹ = 1`. -/
theorem permHom_salvettiConstruction_loop (x : Sal (braidCOM n))
    (a : (mk x : FreeGroupoid (Sal (braidCOM n))) ⟶ mk x) :
    permHom n ((salvettiConstruction n).map a) = 1 := by
  rw [permHom_salvettiConstruction]
  show (FreeGroupoid.lift (SingleObj.differenceFunctor
    (fun a : Sal (braidCOM n) => topePerm a))).map a = 1
  rw [lift_differenceFunctor_map, mul_inv_cancel]

/-! ## Steps 5–8 — the vertical maps, the squares, and the five lemma -/

/-- The monodromy homomorphism of a braid-valued functor: a vertex-group loop to its braid. -/
noncomputable def autToBraid {C : Type*} [Category C]
    (F : FreeGroupoid C ⥤ SingleObj (Braid n)) (X : FreeGroupoid C) :
    Aut X →* Braid n where
  toFun a := F.map a.hom
  map_one' := CategoryTheory.Functor.map_id F X
  map_mul' a b :=
    (congrArg F.map (show (a * b).hom = b.hom ≫ a.hom from rfl)).trans (F.map_comp b.hom a.hom)

/-- **The middle vertical map** `Aut(mk⟦x⟧) →* Bₙ`. -/
noncomputable def braidMonodromy (n : ℕ) (x : Sal (braidCOM n)) :
    Aut (mk (Quotient.mk'' x) :
        FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n)))) →* Braid n :=
  autToBraid (salvettiConstructionQuot n) (mk (Quotient.mk'' x))

/-- **The left vertical map** `Aut(mk x) →* Pₙ` (loops upstairs are pure). -/
noncomputable def pureMonodromy (n : ℕ) (x : Sal (braidCOM n)) :
    Aut (mk x : FreeGroupoid (Sal (braidCOM n))) →* PureBraid n :=
  (autToBraid (salvettiConstruction n) (mk x)).codRestrict (PureBraid n)
    (fun a => MonoidHom.mem_ker.mpr (permHom_salvettiConstruction_loop x a.hom))

/-- **The left square.**  On the covering, the middle map restricts to the upstairs pure map. -/
theorem braid_ladder_commL (n : ℕ) (x : Sal (braidCOM n))
    (a : Aut (mk x : FreeGroupoid (Sal (braidCOM n)))) :
    braidMonodromy n x
        ((FreeGroupoid.map (OrderQuotient.quotFunctor
          (G := Equiv.Perm (Fin n)) (P := Sal (braidCOM n)))).mapAut (mk x) a)
      = (PureBraid n).subtype (pureMonodromy n x a) := by
  change (quotCover n ⋙ salvettiConstructionQuot n).map a.hom = (salvettiConstruction n).map a.hom
  rw [quotCover_comp_salvettiConstructionQuot]

/-- **The right square.**  `permHom` of the braid of a loop is the deck permutation, conjugated by
the frame `topePerm x`. -/
theorem braid_ladder_commR (n : ℕ) (x : Sal (braidCOM n))
    (a : Aut (mk (Quotient.mk'' x) :
        FreeGroupoid (QuotCat (Sal (braidCOM n)) (Equiv.Perm (Fin n))))) :
    permHom n (braidMonodromy n x a)
      = (MulAut.conj (topePerm x)).toMonoidHom (OrderQuotient.deck x a) := by
  change permHom n ((salvettiConstructionQuot n).map a.hom)
    = topePerm x * OrderQuotient.deck x a * (topePerm x)⁻¹
  rw [permHom_salvettiConstructionQuot, thetaQ_map_loop, ← deckM_smul x a.hom, topePerm_reindex]
  have hkey : deckM x a.hom * deckM x a.inv = 1 := by
    rw [← deckM_comp, show a.hom ≫ a.inv = 𝟙 _ from a.hom_inv_id, deckM_one]
  rw [OrderQuotient.deck_apply, ← inv_eq_of_mul_eq_one_right hkey, mul_assoc]

/-- **`braidGrpd ≌ Bₙ` at a basepoint.**  Given the left iso (the cube/pure-braid equivalence) and
fibre connectivity (deck surjectivity), the middle vertical map of the ladder — hence the descended
Salvetti construction on the vertex group — is a bijection.  The short five lemma of `ShortFive`
closes the diagram; both rows are exact (`deck_ker_eq_range`, `PureBraid = permHom.ker`). -/
theorem braidMonodromy_bijective (n : ℕ) (x : Sal (braidCOM n))
    (hconn : ∀ g : Equiv.Perm (Fin n),
      Nonempty ((mk x : FreeGroupoid (Sal (braidCOM n))) ⟶ mk (g • x)))
    (hf : Function.Bijective (pureMonodromy n x)) :
    Function.Bijective (braidMonodromy n x) :=
  ShortFive.bijective_middle
    (ι := (FreeGroupoid.map OrderQuotient.quotFunctor).mapAut (mk x))
    (π := OrderQuotient.deck x) (ι' := (PureBraid n).subtype) (π' := permHom n)
    (f := pureMonodromy n x) (g := braidMonodromy n x)
    (h := (MulAut.conj (topePerm x)).toMonoidHom)
    (braid_ladder_commL n x) (braid_ladder_commR n x)
    (OrderQuotient.deck_ker_eq_range x) (Subgroup.range_subtype (PureBraid n)).symm
    (OrderQuotient.deck_surjective x hconn) (Subgroup.subtype_injective _)
    hf (MulAut.conj (topePerm x)).bijective

/-! ## The left iso is injective from the Salvetti axiom -/

/-- A faithful braid-valued functor's monodromy is injective. -/
theorem autToBraid_injective_of_faithful {C : Type*} [Category C]
    (F : FreeGroupoid C ⥤ SingleObj (Braid n)) [F.Faithful] (X : FreeGroupoid C) :
    Function.Injective (autToBraid F X) :=
  fun _ _ h => Aut.ext (F.map_injective h)

/-- **The upstairs pure map is injective** — Salvetti asphericity (`salvettiConstruction_faithful`).
Only its surjectivity onto `Pₙ` (the cube/pure-braid isomorphism `cube_concBraid_pureBraid`) is left
to feed `braidMonodromy_bijective`. -/
theorem pureMonodromy_injective (n : ℕ) (x : Sal (braidCOM n)) :
    Function.Injective (pureMonodromy n x) := by
  haveI := salvettiConstruction_faithful n
  exact fun _ _ h =>
    autToBraid_injective_of_faithful (salvettiConstruction n) (mk x) (Subtype.ext_iff.mp h)

/-- **The two braid framings agree** at strand-count `n`: `readBraid` (the Salvetti/`ofPerm` side)
and `endBraid` (the cube/`autStrandsBraid` side) read the same braid off a `Braids` endomorphism.
So `salvettiConstruction.map` *is* `concBraidHom` in disguise — the only gap between `pureMonodromy`
and `cube_concBraid_pureBraid` is a change of basepoint, not of framing. -/
theorem readBraid_map_eq_endBraid (n : ℕ) (g : strands n ⟶ strands n) :
    (readBraid n).map g = endBraid g := by
  conv_lhs => rw [← braidHom_endBraid g]
  rw [readBraid_map_braidHom, braidSelfHom_eq n rfl, braidCast_rfl]

/-- **The five lemma, with injectivity discharged.**  The descended Salvetti construction on the
vertex group `Aut(mk⟦x⟧)` is a bijection onto `Bₙ` once the fibre is connected (`hconn`) and the
upstairs pure map is *onto* `Pₙ` (`hsurj` — the content of `cube_concBraid_pureBraid`). -/
theorem braidMonodromy_bijective' (n : ℕ) (x : Sal (braidCOM n))
    (hconn : ∀ g : Equiv.Perm (Fin n),
      Nonempty ((mk x : FreeGroupoid (Sal (braidCOM n))) ⟶ mk (g • x)))
    (hsurj : Function.Surjective (pureMonodromy n x)) :
    Function.Bijective (braidMonodromy n x) :=
  braidMonodromy_bijective n x hconn ⟨pureMonodromy_injective n x, hsurj⟩

end CubeChains
