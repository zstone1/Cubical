import CubeChains.Salvetti.TopeLines
import CubeChains.Salvetti.ChainBraidFace
import CubeChains.Arrangements.SalElements

/-!
# Salvetti/TopeSal — the wall-crossing comparison `topeLines ≅ chFace ⋙ salFunctor`

The natural iso identifying, over each cube chain `b : Ch (□n)`, the tope refinements
`(⋁b.dims).toPsh ⟶ topePresheaf` with the topes above `chFace b`.  A tope `T` above the chain's
braid face restricts, per bead, to a within-bead tope; the two cross-block coordinate signs are
already pinned by `chFace b ⊑ T`, so `T ↦ b.map.hom ≫ T̂` (`betaMap`, the Yoneda direction) is a
bijection whose naturality *is* the wall-crossing `T ↦ chFace b₂ ⊙ T` (`map_comp_tope_eq`).
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain PrecubicalSet

namespace CubeChains

variable {n : ℕ}

/-! ## Part A — the core "cross-block invisibility" lemma -/

/-- `topeRestrict` distributes over the wall-crossing composition. -/
theorem topeRestrict_comp_distrib {m d : ℕ} (g : ▫m ⟶ ▫d) (X Y : SignVec (BraidGround d)) :
    topeRestrict g (X ⊙ Y) = topeRestrict g X ⊙ topeRestrict g Y := rfl

/-- A constant height has zero braid covector (every difference is zero). -/
theorem braidSign_const_zero {d : ℕ} (c : ℤ) : braidSign (fun _ : Fin d => c) = 0 := by
  funext e
  simp only [braidSign_apply, sub_self, sign_zero, Pi.zero_apply]

/-- **Bead `i`'s face is blind to the chain's braid face** — `chFace b` is `beadOf`-constant on
bead `i`'s coordinates, so it restricts to the zero covector there. -/
theorem topeRestrict_beadFace_chFace (b : Ch (□n)) (i : Fin b.dims.length) :
    topeRestrict (beadFace b.map.hom i) (chFace b).1 = 0 := by
  have h1 : (chFace b).1 = braidSign (fun q => ((beadOf b q : ℕ) : ℤ)) := rfl
  rw [h1, topeRestrict_braidSign]
  have hconst : (fun k => ((beadOf b (faceEmb (beadFace b.map.hom i) k) : ℕ) : ℤ))
      = (fun _ : Fin (b.dims.get i : ℕ) => ((i : ℕ) : ℤ)) := by
    funext k
    have : beadOf b (faceEmb (beadFace b.map.hom i) k) = i :=
      (mem_range_iff_beadOf b i (faceEmb (beadFace b.map.hom i) k)).mp ⟨k, rfl⟩
    rw [this]
  rw [hconst, braidSign_const_zero]

/-- `yonedaEquiv` and `cubeHomEquiv` are the same map, so their round trip cancels. -/
theorem yonedaEquiv_cube_symm {P : PrecubicalSet} (X : P.obj (op ▫n)) :
    yonedaEquiv ((cubeHomEquiv P n).symm X) = X :=
  (cubeHomEquiv P n).apply_symm_apply X

/-- Restricting `chFace b ⊙ X` to bead `i` drops the (blind) `chFace b` factor. -/
theorem topeRestrict_chFace_comp (b : Ch (□n)) (i : Fin b.dims.length)
    (X : SignVec (BraidGround n)) :
    topeRestrict (beadFace b.map.hom i) X
      = topeRestrict (beadFace b.map.hom i) ((chFace b).1 ⊙ X) := by
  rw [topeRestrict_comp_distrib, topeRestrict_beadFace_chFace, SignVec.comp_zero_left]

/-- Restricting a map into `topePresheaf` to bead `i` is `topeRestrict` of its classified tope. -/
theorem tope_bead_restrict (b : Ch (□n)) (ŝ : (□n).toPsh ⟶ topePresheaf) (i : Fin b.dims.length) :
    yonedaEquiv (ιᵂ b.dims i ≫ b.map.hom ≫ ŝ)
      = topeRestrictTope (beadFace b.map.hom i) (yonedaEquiv ŝ) := by
  rw [← Category.assoc, yonedaEquiv_comp]
  exact (map_yonedaEquiv ŝ (beadFace b.map.hom i)).symm

/-- **The wall-crossing on a single chain** (the naturality core).  Pulling a tope `T` of `□n` back
along `b` sees only its within-bead signs, so it agrees with pulling back `chFace b ⊙ T`. -/
theorem map_comp_tope_eq (b : Ch (□n)) (T : Tope n) :
    b.map.hom ≫ (cubeHomEquiv topePresheaf n).symm T
      = b.map.hom ≫ (cubeHomEquiv topePresheaf n).symm
          ⟨(chFace b).1 ⊙ T.1, COM.isTope_comp (chFace b).2 T.2⟩ := by
  refine serialWedge_hom_ext b.dims _ _ (fun i => ?_) (tope_cube0_eq _ _)
  apply yonedaEquiv.injective
  have e1 := tope_bead_restrict b ((cubeHomEquiv topePresheaf n).symm T) i
  have e2 := tope_bead_restrict b
    ((cubeHomEquiv topePresheaf n).symm ⟨(chFace b).1 ⊙ T.1, COM.isTope_comp (chFace b).2 T.2⟩) i
  rw [yonedaEquiv_cube_symm] at e1 e2
  have e3 : topeRestrictTope (beadFace b.map.hom i) T
      = topeRestrictTope (beadFace b.map.hom i)
          ⟨(chFace b).1 ⊙ T.1, COM.isTope_comp (chFace b).2 T.2⟩ :=
    Subtype.ext (topeRestrict_chFace_comp b i T.1)
  exact e1.trans (e3.trans e2.symm)

/-! ## Part B — the objectwise data -/

/-- The topes above a chain's braid face — the value of `chFace ⋙ salFunctor`. -/
abbrev SalObj (b : Ch (□n)) : Type :=
  {T : SignVec (BraidGround n) // (braidCOM n).IsTope T ∧ (chFace b).1 ⊑ T}

/-- The Yoneda direction `SalObj b → (topeLines).obj (op b)`: a tope above `chFace b`, transposed
and pulled back along the chain's descent. -/
def betaMap (b : Ch (□n)) (s : SalObj b) : (⋁b.dims).toPsh ⟶ topePresheaf :=
  b.map.hom ≫ (cubeHomEquiv topePresheaf n).symm ⟨s.1, s.2.1⟩

theorem betaMap_apply (b : Ch (□n)) (s : SalObj b) :
    betaMap b s = b.map.hom ≫ (cubeHomEquiv topePresheaf n).symm ⟨s.1, s.2.1⟩ := rfl

/-- Reading `betaMap b s` at bead `i` recovers `s` restricted to that bead. -/
theorem betaMap_bead (b : Ch (□n)) (s : SalObj b) (i : Fin b.dims.length) :
    yonedaEquiv (ιᵂ b.dims i ≫ betaMap b s)
      = topeRestrictTope (beadFace b.map.hom i) ⟨s.1, s.2.1⟩ := by
  have e := tope_bead_restrict b ((cubeHomEquiv topePresheaf n).symm ⟨s.1, s.2.1⟩) i
  rw [yonedaEquiv_cube_symm] at e
  exact e

/-- **`betaMap b` is injective** — within-bead pairs agree by `betaMap_bead`, cross-block pairs by
`chFace b ⊑ T` (their nonzero sign forces the value). -/
theorem betaMap_injective (b : Ch (□n)) : Function.Injective (betaMap b) := by
  intro s s' hss
  apply Subtype.ext
  funext e
  by_cases hbead : beadOf b e.1.1 = beadOf b e.1.2
  · -- within bead `i := beadOf b e.1.1`
    have hbeadeq :
        topeRestrictTope (beadFace b.map.hom (beadOf b e.1.1)) (⟨s.1, s.2.1⟩ : Tope n)
          = topeRestrictTope (beadFace b.map.hom (beadOf b e.1.1)) ⟨s'.1, s'.2.1⟩ := by
      rw [← betaMap_bead b s (beadOf b e.1.1), ← betaMap_bead b s' (beadOf b e.1.1), hss]
    have hrestr : topeRestrict (beadFace b.map.hom (beadOf b e.1.1)) s.1
        = topeRestrict (beadFace b.map.hom (beadOf b e.1.1)) s'.1 :=
      congrArg Subtype.val hbeadeq
    have hp : e.1.1 ∈ Set.range (faceEmb (beadFace b.map.hom (beadOf b e.1.1))) :=
      (mem_range_iff_beadOf b (beadOf b e.1.1) e.1.1).mpr rfl
    have hq : e.1.2 ∈ Set.range (faceEmb (beadFace b.map.hom (beadOf b e.1.1))) :=
      (mem_range_iff_beadOf b (beadOf b e.1.1) e.1.2).mpr hbead.symm
    obtain ⟨k, hk⟩ := hp
    obtain ⟨k', hk'⟩ := hq
    have hkk' : k < k' :=
      (faceEmb (beadFace b.map.hom (beadOf b e.1.1))).lt_iff_lt.mp (by rw [hk, hk']; exact e.2)
    have hbg : braidGroundMap (beadFace b.map.hom (beadOf b e.1.1))
        (⟨(k, k'), hkk'⟩ : BraidGround _) = e := by
      apply Subtype.ext
      change (faceEmb (beadFace b.map.hom (beadOf b e.1.1)) k,
            faceEmb (beadFace b.map.hom (beadOf b e.1.1)) k') = e.1
      rw [hk, hk']
    rw [← hbg]
    exact congrFun hrestr ⟨(k, k'), hkk'⟩
  · -- cross-block pair: `chFace b e ≠ 0`
    have hne : (chFace b).1 e ≠ 0 := by
      intro h0
      apply hbead
      have h := (braidSign_zero_iff (fun q => ((beadOf b q : ℕ) : ℤ)) e).mp h0
      exact Fin.val_injective (Nat.cast_injective (R := ℤ) h)
    rcases s.2.2 e with h1 | h1
    · exact absurd h1 hne
    rcases s'.2.2 e with h2 | h2
    · exact absurd h2 hne
    exact h1.symm.trans h2

/-! ### The pushforward run and the clean bijection `Run (⋁b.dims) ≃ SalObj b` -/

/-- The chain of `□n` obtained by pushing a run of `⋁b.dims` forward along the descent `b.map`. -/
def pushC (b : Ch (□n)) (r : Run (⋁b.dims)) : Ch (□n) := ⟨r.chain.dims, r.chain.map ≫ b.map⟩

/-- …as a run of `□n`. -/
def pushRun (b : Ch (□n)) (r : Run (⋁b.dims)) : Run (□n) := ⟨pushC b r, r.ones⟩

/-- The canonical refinement `pushC b r ⟶ b` — the run's own descent. -/
def pushHom (b : Ch (□n)) (r : Run (⋁b.dims)) : pushC b r ⟶ b := ⟨r.chain.map, rfl⟩

/-- Run → tope-above: the braid face of the pushed-forward run. -/
def phiFwd (b : Ch (□n)) (r : Run (⋁b.dims)) : SalObj b :=
  ⟨(chFace (pushC b r)).1, isTope_chFace_run (pushRun b r), chFace_faceLE (pushHom b r)⟩

/-- Cancelling the (mono) descent: two runs with the same pushforward are equal. -/
theorem pushC_inj_aux (b : Ch (□n)) {d d' : List ℕ+} (m : ⋁d ⟶ ⋁b.dims) (m' : ⋁d' ⟶ ⋁b.dims)
    (hm : (⟨d, m ≫ b.map⟩ : Ch (□n)) = ⟨d', m' ≫ b.map⟩) :
    (⟨d, m⟩ : Ch (⋁b.dims)) = ⟨d', m'⟩ := by
  obtain rfl : d = d' := congrArg ChainCat.Obj.dims hm
  haveI : Mono b.map.hom := descent_mono (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n) b
  injection hm with _ hmeq
  have hm2 : m.hom ≫ b.map.hom = m'.hom ≫ b.map.hom := by
    have h3 := congrArg BPSet.Hom.hom hmeq
    rwa [BPSet.comp_hom, BPSet.comp_hom] at h3
  rw [BPSet.hom_ext ((cancel_mono b.map.hom).mp hm2)]

theorem phiFwd_injective (b : Ch (□n)) : Function.Injective (phiFwd b) := by
  intro r r' hrr
  have hpush : pushC b r = pushC b r' :=
    chFaceEquiv.injective (Subtype.ext (congrArg (·.1) hrr))
  exact Run.ext (pushC_inj_aux b r.chain.map r'.chain.map hpush)

theorem phiFwd_surjective (b : Ch (□n)) : Function.Surjective (phiFwd b) := by
  intro s
  set pr := (runTopeEquiv n).symm ⟨s.1, s.2.1⟩ with hpr
  have hchain : (chFace pr.chain).1 = s.1 :=
    congrArg Subtype.val (chFaceEquiv.apply_symm_apply (⟨s.1, s.2.1.1⟩ : COM.Face (braidCOM n)))
  have hLE : (chFace b).1 ⊑ (chFace pr.chain).1 := by rw [hchain]; exact s.2.2
  refine ⟨⟨⟨pr.chain.dims, (reflectHom hLE).φ⟩, pr.ones⟩, ?_⟩
  apply Subtype.ext
  change (chFace (⟨pr.chain.dims, (reflectHom hLE).φ ≫ b.map⟩ : Ch (□n))).1 = s.1
  rw [show (⟨pr.chain.dims, (reflectHom hLE).φ ≫ b.map⟩ : Ch (□n)) = pr.chain from
        congrArg (ChainCat.Obj.mk pr.chain.dims) (reflectHom hLE).w]
  exact hchain

/-- **Runs of the wedge are the topes above the chain's braid face.** -/
noncomputable def phiEquiv (b : Ch (□n)) : Run (⋁b.dims) ≃ SalObj b :=
  Equiv.ofBijective (phiFwd b) ⟨phiFwd_injective b, phiFwd_surjective b⟩

/-- The soft half: tope refinements of `b` are runs of `⋁b.dims` (`runTopeIso` + `runPshEquiv`). -/
noncomputable def linesEquiv (b : Ch (□n)) :
    ((⋁b.dims).toPsh ⟶ topePresheaf) ≃ Run (⋁b.dims) :=
  (Iso.homCongr (Iso.refl (⋁b.dims).toPsh) runTopeIso.symm).trans (runPshEquiv b.dims)

/-- **`betaMap b` is bijective** — injective (above) and equinumerous with its source via the two
soft equivalences (`E`).  Conjugating by `E` turns injectivity into bijectivity on the finite
source `SalObj b`. -/
theorem betaMap_bijective (b : Ch (□n)) : Function.Bijective (betaMap b) := by
  haveI : Finite (BraidGround n) := Subtype.finite
  haveI : Finite (SalObj b) := Subtype.finite
  have E := (linesEquiv b).trans (phiEquiv b)
  refine (E.bijective.of_comp_iff' (betaMap b)).mp ?_
  exact Finite.injective_iff_bijective.mp (E.injective.comp (betaMap_injective b))

/-! ## Part C — the natural iso -/

/-- **Naturality of `betaMap`** — the wall-crossing square, restated on a chain morphism.  A
refinement `g : b₂ ⟶ b₁` sends `betaMap b₁ s` to `betaMap b₂` of its `chFace b₂`-composition. -/
theorem betaMap_natural {b₁ b₂ : Ch (□n)} (g : b₂ ⟶ b₁) (s : SalObj b₁) :
    betaMap b₂ ⟨(chFace b₂).1 ⊙ s.1, COM.isTope_comp (chFace b₂).2 s.2.1,
        SignVec.faceLE_comp_left _ _⟩
      = g.φ.hom ≫ betaMap b₁ s := by
  have hw : g.φ.hom ≫ b₁.map.hom = b₂.map.hom := by
    have h := congrArg BPSet.Hom.hom g.w
    rwa [BPSet.comp_hom] at h
  rw [betaMap_apply, betaMap_apply, ← Category.assoc, hw]
  exact (map_comp_tope_eq b₂ ⟨s.1, s.2.1⟩).symm

/-- **The wall-crossing comparison** `topeLines (□n) ≅ chFace ⋙ salFunctor`.  Objectwise the Yoneda
bijection `betaMap`; naturality is `betaMap_natural`. -/
noncomputable def topeSalIso (n : ℕ) :
    topeLines (□n) ≅ chFaceFunctor ⋙ COM.salFunctor (braidCOM n) :=
  (NatIso.ofComponents (F := chFaceFunctor ⋙ COM.salFunctor (braidCOM n)) (G := topeLines (□n))
    (fun X => (Equiv.ofBijective (betaMap X.unop) (betaMap_bijective X.unop)).toIso)
    (fun {X Y} f => by
      apply ConcreteCategory.hom_ext
      intro s
      exact betaMap_natural f.unop s)).symm

end CubeChains
