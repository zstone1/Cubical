import CubeChains.Machinery.Presentation.Contract
import CubeChains.Machinery.Presentation.LocalizeCut
import CubeChains.Concurrency.Presentation.LocPresentation

/-!
# Concurrency/Presentation/RunContract — the cut presentation contracted onto the runs

Every chain is entered from the run on its own events by exactly one merge (`existsUnique_W_ones`),
so the merges `Machinery/Presentation/LocalizeCut` inverts contract away: `zRunPresentation` keeps
one 0-cell per run and one 1-cell per bead cut that braids.

`word_comp_of_S` is the only content, and it is that uniqueness: both sides of the square are
`W`-arrows out of the run on the same events, so `eq_of_W` identifies them.
-/

open CategoryTheory CubeChains BPSet Opposite

namespace ChainCat

local notation "ZG" => Polygraph.InvGen Cut.poly Cut.mergeGen

local notation "ZP" => Polygraph.invPoly Cut.poly Cut.mergeGen

/-! ## A factor of a merge is a merge

Crossings add along a composite, and a merge makes none. -/

theorem W_of_comp_left {K : BPSet} {a b d : Ch K} (f : a ⟶ b) (g : b ⟶ d) (h : W K (f ≫ g)) :
    W K f := by
  have h0 := permLen_crossPerm_comp (rfl : dimSum a.dims = dimSum a.dims) f g
  rw [(W_iff_crossPerm_eq_one rfl (f ≫ g)).mp h, permLen_one] at h0
  exact (W_iff_crossPerm_eq_one rfl f).mpr (eq_one_of_permLen_eq_zero _ (by omega))

theorem W_of_comp_right {K : BPSet} {a b d : Ch K} (f : a ⟶ b) (g : b ⟶ d) (h : W K (f ≫ g)) :
    W K g := by
  have h0 := permLen_crossPerm_comp (rfl : dimSum a.dims = dimSum a.dims) f g
  rw [(W_iff_crossPerm_eq_one rfl (f ≫ g)).mp h, permLen_one] at h0
  exact (W_iff_crossPerm_eq_one (tgtStrands f rfl) g).mpr
    (eq_one_of_permLen_eq_zero _ (by omega))

/-- **A renaming of a chain is a merge** — it is an identity. -/
theorem W_eqToHom {K : BPSet} {a b : Ch K} (h : a = b) : W K (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact MorphismProperty.id_mem _ _

/-! ## Cut words, evaluated -/

theorem Cut.ev_comp {x y z : GenObj Cut.Refine} (R : Quiver.Path x y) (R' : Quiver.Path y z) :
    Cut.ev (R.comp R') = Cut.ev R' ≫ Cut.ev R :=
  congrArg Quiver.Hom.unop (Paths.lift_map_comp Cut.interp R R')

theorem Cut.ev_toPath {x y : GenObj Cut.Refine} (e : x ⟶ y) :
    Cut.ev e.toPath = Cut.genHom e ≫ 𝟙 x.as :=
  Cut.ev_cons Quiver.Path.nil e

theorem Cut.ev_cellCongr {x y y' : GenObj Cut.Refine} (h : y = y') (R : Quiver.Path x y) :
    Cut.ev (cellCongr Quiver.Path rfl h R) = eqToHom (congrArg GenObj.as h).symm ≫ Cut.ev R := by
  subst h
  rw [cellCongr_self]
  simp

/-- **Every letter of a crossing-free cut word is a merge.** -/
theorem Cut.all_mergeGen_of_W : ∀ {x y : GenObj Cut.Refine} (R : Quiver.Path x y),
    W Zbp (Cut.ev R) → Quiver.Path.All (fun ⦃_ _⦄ e => Cut.mergeGen e) R := by
  intro x y R
  induction R with
  | nil => exact fun _ => Quiver.Path.all_nil _
  | cons R e ih =>
      intro hW
      rw [Cut.ev_cons] at hW
      refine (Quiver.Path.all_cons_iff R e).mpr ⟨ih (W_of_comp_right _ _ hW), ?_⟩
      exact (merge_iff (Cut.genHom e)).mpr ⟨W_of_comp_left _ _ hW, Cut.codim_genHom e⟩

/-! ## The run on a chain's own events -/

/-- The run on a chain's own events. -/
def zRep (d : Ch Zbp) : Ch Zbp := zObj (𝟙^(dimSum d.dims))

@[simp] theorem dimSum_zRep (d : Ch Zbp) : dimSum (zRep d).dims = dimSum d.dims :=
  dimSum_replicate _

theorem zRep_idem (d : Ch Zbp) : zRep (zRep d) = zRep d :=
  congrArg (fun N => zObj (𝟙^N)) (dimSum_zRep d)

/-- The merge from the run on a chain's own events. -/
noncomputable def zRunMerge (d : Ch Zbp) : zRep d ⟶ d := runMerge d rfl

theorem W_zRunMerge (d : Ch Zbp) : W Zbp (zRunMerge d) := W_runMerge d rfl

/-- …spelled by bead cuts. -/
noncomputable def runCutWord (d : Ch Zbp) : Quiver.Path (Cut.vert d) (Cut.vert (zRep d)) :=
  (Cut.exists_path (codim (zRunMerge d)) (zRunMerge d) le_rfl).choose

theorem ev_runCutWord (d : Ch Zbp) : Cut.ev (runCutWord d) = zRunMerge d :=
  (Cut.exists_path (codim (zRunMerge d)) (zRunMerge d) le_rfl).choose_spec

theorem all_runCutWord (d : Ch Zbp) :
    Quiver.Path.All (fun ⦃_ _⦄ e => Cut.mergeGen e) (runCutWord d) :=
  Cut.all_mergeGen_of_W _ (by rw [ev_runCutWord]; exact W_zRunMerge d)

/-! ## The generators the localization inverts -/

/-- The cut generators `zCutLocPresentation` makes invertible: the merges, and the formal inverses
it adjoins to them. -/
def Cut.merged {a b : Ch Zbp} : ZG a b → Prop
  | .inl e => Cut.mergeGen e
  | .inr _ => True

/-- **No generator changes the strand count**, so none changes the run. -/
theorem zRep_eq_of_gen {a b : Ch Zbp} (g : ZG a b) : zRep a = zRep b := by
  rcases g with e | ⟨e, -⟩
  · exact congrArg (fun N => zObj (𝟙^N)) (dimSum_eq_of_hom e.1).symm
  · exact congrArg (fun N => zObj (𝟙^N)) (dimSum_eq_of_hom e.1)

/-! ## Merging to the run, as an arrow of the extension

Two `W`-arrows out of the run on the same events are equal (`eq_of_W`), and a cut word is pinned in
`Cut.poly.presented` by the arrow it evaluates to (`Cut.quot_eq_of_ev_eq`); together they make the
merge onto the run a natural transformation of the 1-cells. -/

/-- The merge onto the run, as a word of the extension. -/
noncomputable def runInvWord (d : Ch Zbp) :
    Quiver.Path (⟨d⟩ : GenObj ZG) ⟨zRep d⟩ :=
  (Polygraph.fwdPre Cut.poly Cut.mergeGen).mapPath (runCutWord d)

/-- …and as an arrow. -/
noncomputable def zRunArrow (d : Ch Zbp) : (⟨⟨d⟩⟩ : (ZP).presented) ⟶ ⟨⟨zRep d⟩⟩ :=
  (ZP).quot.map (runInvWord d)

/-- The renaming of runs a generator induces. -/
noncomputable def zRepHom {a b : Ch Zbp} (g : ZG a b) :
    (⟨⟨zRep a⟩⟩ : (ZP).presented) ⟶ ⟨⟨zRep b⟩⟩ :=
  eqToHom (congrArg (fun z : Ch Zbp => (⟨⟨z⟩⟩ : (ZP).presented)) (zRep_eq_of_gen g))

theorem zRepHom_trans {a b : Ch Zbp} (g : ZG a b) (g' : ZG b a) :
    zRepHom g ≫ zRepHom g' = 𝟙 (⟨⟨zRep a⟩⟩ : (ZP).presented) := by
  rw [zRepHom, zRepHom, eqToHom_trans, eqToHom_refl]

/-- **Merging `a` to its run is the merge `a ⟶ b` followed by merging `b`** — at a merge
generator. -/
theorem zRunArrow_fwd {a b : Ch Zbp} (e : Cut.Refine a b) (he : Cut.mergeGen e) :
    zRunArrow a ≫ zRepHom (Sum.inl e : ZG a b)
      = Polygraph.fwdArrow Cut.poly Cut.mergeGen e ≫ zRunArrow b := by
  have hev : Cut.ev (cellCongr Quiver.Path rfl
        (congrArg Cut.vert (zRep_eq_of_gen (Sum.inl e : ZG a b))) (runCutWord a))
      = Cut.ev ((Cut.gen e.1 e.2).toPath.comp (runCutWord b)) := by
    rw [Cut.ev_cellCongr, Cut.ev_comp, Cut.ev_toPath, ev_runCutWord, ev_runCutWord]
    refine eq_of_W ((W Zbp).comp_mem _ _ (W_eqToHom _) (W_zRunMerge a))
      ((W Zbp).comp_mem _ _ (W_zRunMerge b)
        ((W Zbp).comp_mem _ _ ?_ (MorphismProperty.id_mem _ _)))
    exact merge_le_W Zbp _ he
  refine Eq.trans (Polygraph.quot_map_cellCongr ZP
    (congrArg (fun z : Ch Zbp => (⟨z⟩ : GenObj ZG)) (zRep_eq_of_gen (Sum.inl e : ZG a b)))
    (runInvWord a)).symm ?_
  refine Eq.trans (congrArg (fun t => (ZP).quot.map t)
    (Prefunctor.mapPath_cellCongr (Polygraph.fwdPre Cut.poly Cut.mergeGen) rfl
      (congrArg Cut.vert (zRep_eq_of_gen (Sum.inl e : ZG a b))) (runCutWord a)).symm) ?_
  refine Eq.trans (Polygraph.Hom.quot_map_congr (Polygraph.invIncl Cut.poly Cut.mergeGen)
    (Cut.quot_eq_of_ev_eq _ _ _ rfl hev)) ?_
  exact Eq.trans (congrArg (fun t => (ZP).quot.map t)
      (Prefunctor.mapPath_comp (Polygraph.fwdPre Cut.poly Cut.mergeGen) (Cut.gen e.1 e.2).toPath
        (runCutWord b)))
    (Polygraph.quot_map_comp ZP _ _)

/-- **…and at a formal inverse**, by cancelling the merge it inverts. -/
theorem zRunArrow_bwd {a b : Ch Zbp} (e : Cut.Refine b a) (he : Cut.mergeGen e) :
    zRunArrow a ≫ zRepHom (Sum.inr ⟨e, he⟩ : ZG a b)
      = Polygraph.bwdArrow Cut.poly Cut.mergeGen e he ≫ zRunArrow b := by
  have hfwd := zRunArrow_fwd e he
  calc zRunArrow a ≫ zRepHom (Sum.inr ⟨e, he⟩ : ZG a b)
      = (𝟙 (⟨⟨a⟩⟩ : (ZP).presented) ≫ zRunArrow a) ≫ zRepHom (Sum.inr ⟨e, he⟩ : ZG a b) := by
        rw [Category.id_comp]
    _ = ((Polygraph.bwdArrow Cut.poly Cut.mergeGen e he
            ≫ Polygraph.fwdArrow Cut.poly Cut.mergeGen e) ≫ zRunArrow a)
          ≫ zRepHom (Sum.inr ⟨e, he⟩ : ZG a b) := by
        rw [Polygraph.bwdArrow_fwdArrow]
    _ = Polygraph.bwdArrow Cut.poly Cut.mergeGen e he
          ≫ ((Polygraph.fwdArrow Cut.poly Cut.mergeGen e ≫ zRunArrow a)
            ≫ zRepHom (Sum.inr ⟨e, he⟩ : ZG a b)) := by
        simp only [Category.assoc]
    _ = Polygraph.bwdArrow Cut.poly Cut.mergeGen e he
          ≫ ((zRunArrow b ≫ zRepHom (Sum.inl e : ZG b a))
            ≫ zRepHom (Sum.inr ⟨e, he⟩ : ZG a b)) := by rw [← hfwd]
    _ = Polygraph.bwdArrow Cut.poly Cut.mergeGen e he ≫ zRunArrow b := by
        rw [Category.assoc, zRepHom_trans, Category.comp_id]

/-- **Merging to the run factors through any inverted generator.** -/
theorem zRunArrow_step {a b : Ch Zbp} (g : ZG a b) (h : Cut.merged g) :
    zRunArrow a ≫ zRepHom g
      = (ZP).quot.map (Polygraph.cell (P := ZP) g).toPath ≫ zRunArrow b := by
  rcases g with e | ⟨e, he⟩
  · exact zRunArrow_fwd e h
  · exact zRunArrow_bwd e he

/-! ## The contraction, and what it presents -/

/-- **The merges of the cut presentation contract onto the runs.** -/
noncomputable def zCutContraction : Contraction ZP Cut.merged where
  rep := zRep
  rep_idem := zRep_idem
  word := runInvWord
  word_all d := Quiver.Path.All.mapPath (Polygraph.fwdPre Cut.poly Cut.mergeGen)
    (fun _ he => he) (all_runCutWord d)
  invWord d := Polygraph.invWord Cut.poly Cut.mergeGen (runCutWord d) (all_runCutWord d)
  invWord_all d := Polygraph.all_invWord Cut.poly Cut.mergeGen (fun _ _ => trivial)
    (runCutWord d) (all_runCutWord d)
  word_invWord d := (Polygraph.quot_map_comp _ _ _).trans
    (Polygraph.quot_fwd_invWord Cut.poly Cut.mergeGen (runCutWord d) (all_runCutWord d))
  invWord_word d := (Polygraph.quot_map_comp _ _ _).trans
    (Polygraph.quot_invWord_fwd Cut.poly Cut.mergeGen (runCutWord d) (all_runCutWord d))
  rep_eq_of_S {_ _} g _ := zRep_eq_of_gen g
  word_comp_of_S g h :=
    (Polygraph.quot_map_cellCongr ZP _ _).trans
      ((zRunArrow_step g h).trans (Polygraph.quot_map_comp ZP _ _).symm)

/-- **The cut presentation of `Ch(Z)[W⁻¹]`, contracted onto the runs** — one 0-cell per run, and
one 1-cell per bead cut that braids. -/
noncomputable def zRunPresentation :
    Presents zCutContraction.poly (((W Zbp).op).Localization) :=
  zCutLocPresentation.contract zCutContraction

end ChainCat
