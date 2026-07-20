import CubeChains.Salvetti.RunOrderFace
import CubeChains.Chains.Flips
import CubeChains.Chains.Events

/-!
# Salvetti/WallCrossing — the bead-local half of the Salvetti wall-crossing law

`wallCrossing_of_sameBlock` asks that restricting a run along `f : a ⟶ b` preserve the relative
order of any two coordinates lying in one bead of `a`.  Naming a coordinate by the *event* that
flips it (`Chains/Events`) leaves one recursion: a run orders one bead's coordinates exactly as
that bead's own run does (`runFlipIdx_lt_iff_bead`).  Restriction is bead-local
(`beadRun_runRestrict`), so reading both sides bead-locally meets `RunOrderFace`'s single-face law.
-/

open CategoryTheory Opposite CubeChain StdCube BPSet SignType ChainCat

namespace CubeChains

variable {n : ℕ}

/-! ## Part 1 — the cube list a run traces out -/

/-- The cube list a run over `χ` traces out: one edge per bead of the run.  A run of *any*
bi-pointed set will do — it carries its own dimension sequence, so nothing forces a wedge here. -/
def runCubes {X : BPSet} (s : Run X) (χ : X.toPsh ⟶ (□n).toPsh) : CubeList n :=
  cubesOf s.dims (s.map.hom ≫ χ)

/-- **`runConcat` is `++` on cube lists** — the form the bead recursion meets, where the run is cut
at a `wedge2` rather than at a list junction.  `concatChainMap_inclL/R` are the whole content. -/
theorem runCubes_concat {X Y : BPSet} (s₁ : Run X) (s₂ : Run Y)
    (χ : (wedge2 X Y).toPsh ⟶ (□n).toPsh) :
    runCubes ((runConcat X Y).obj (s₁, s₂)) χ
      = runCubes s₁ (wedgeInl X Y ≫ χ) ++ runCubes s₂ (wedgeInr X Y ≫ χ) := by
  have hL : wedgeInclL s₁.dims s₂.dims ≫ (concatChainMap X Y s₁.chain s₂.chain).hom ≫ χ
      = s₁.map.hom ≫ wedgeInl X Y ≫ χ := by
    rw [← Category.assoc, concatChainMap_inclL X Y s₁.chain s₂.chain, Category.assoc]
  have hR : wedgeInclR s₁.dims s₂.dims ≫ (concatChainMap X Y s₁.chain s₂.chain).hom ≫ χ
      = s₂.map.hom ≫ wedgeInr X Y ≫ χ := by
    rw [← Category.assoc, concatChainMap_inclR X Y s₁.chain s₂.chain, Category.assoc]
  change cubesOf (s₁.dims ++ s₂.dims) ((concatChainMap X Y s₁.chain s₂.chain).hom ≫ χ) = _
  rw [cubesOf_append s₁.dims s₂.dims, hL, hR]
  rfl

/-- **A run of a cube flips exactly the coordinates in the face it is pushed along.** -/
theorem flips_runCubes_cube {e : ℕ} (u : Run (□e)) (γ : (□e).toPsh ⟶ (□n).toPsh) (p : Fin n) :
    Flips (runCubes u γ) p ↔ ∃ p', faceEmb (cubeFace γ) p' = p :=
  flips_cubesOf_cube u.map γ p

/-- **The height of a coordinate under a run of a cube**, read through the bead's face.  A run of
`□ᵉ` is an all-edges chain of `□ᵉ` outright, so no `⋁[e] ≅ □ᵉ` conjugation survives here. -/
theorem flipIdx_cubeRun (e : ℕ) (u : Run (□e)) (γ : (□e).toPsh ⟶ (□n).toPsh) (p' : Fin e) :
    (flipIdx (runCubes u γ) (faceEmb (cubeFace γ) p') : ℤ) = cubeRunHeight u p' := by
  have hcubes : runCubes u γ = pushCubes (cubeFace γ) (wedgeToRefineObj u.chain).cubes :=
    cubesOf_comp_face u.dims u.map.hom γ
  rw [hcubes, flipIdx_pushCubes]
  rfl

/-! ## Part 2 — the run one bead of a wedge carries

`runPresheaf` classifies runs of `⋁A` (`pshOfRun`), so bead `i`'s own run is that classifying map
restricted along `ιᵂ A i` — and the classification's two legs at a cons *are* the halves of the
Segal split. -/

/-- The run bead `i` of a serial wedge carries. -/
def beadRun (A : List ℕ+) (s : Run (⋁A)) (i : Fin A.length) : Run (□((A.get i : ℕ))) :=
  yonedaEquiv (ιᵂ A i ≫ pshOfRun A s)

theorem beadRun_zero (c : ℕ+) (rest : List ℕ+) (s : Run (⋁(c :: rest))) :
    beadRun (c :: rest) s 0 = (runSplit (consAltitude c rest) s).1 :=
  (congrArg yonedaEquiv (pshOfRun_inl c rest s)).trans (yonedaEquiv.apply_symm_apply _)

theorem beadRun_succ (c : ℕ+) (rest : List ℕ+) (s : Run (⋁(c :: rest))) (j : Fin rest.length) :
    beadRun (c :: rest) s j.succ = beadRun rest (runSplit (consAltitude c rest) s).2 j :=
  congrArg yonedaEquiv
    ((ι_succ_comp j (pshOfRun (c :: rest) s)).trans
      (congrArg (fun t => ιᵂ rest j ≫ t) (pshOfRun_inr c rest s)))

/-! ## Part 3 — a run reads one bead of the source

The single recursion.  Cutting `⋁(c :: rest)` at its head bead cuts the run's cube list there
(`runCubes_concat`), and a coordinate of bead `i` lands on the head side exactly when `i = 0` —
which is `flipIdx_faceEmb_beadFace`, the statement that `flipIdx` inverts `cubeEv`. -/

/-- **A run orders one bead's coordinates the way that bead's own run does.** -/
theorem runFlipIdx_lt_iff_bead : ∀ (A : List ℕ+) (s : Run (⋁A))
    (χ : (⋁A).toPsh ⟶ (□n).toPsh) (i : Fin A.length) (p q : Fin ((A.get i : ℕ))),
    (flipIdx (runCubes s χ) (faceEmb (beadFace χ i) p)
        < flipIdx (runCubes s χ) (faceEmb (beadFace χ i) q)
      ↔ cubeRunHeight (beadRun A s i) p < cubeRunHeight (beadRun A s i) q)
  | [], _, _, i, _, _ => i.elim0
  | c :: rest, s, χ, i, p, q => by
    set s₁ : Run (□(c : ℕ)) := (runSplit (consAltitude c rest) s).1 with hs₁
    set s₂ : Run (⋁rest) := (runSplit (consAltitude c rest) s).2 with hs₂
    have hs : runCubes s χ = runCubes s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ)
        ++ runCubes s₂ (wedgeInr (□(c : ℕ)) (⋁rest) ≫ χ) :=
      (congrArg (fun z : Run (⋁(c :: rest)) => runCubes z χ)
        (runConcat_runSplit (consAltitude c rest) s).symm).trans (runCubes_concat s₁ s₂ χ)
    refine Fin.cases (motive := fun i => ∀ p q : Fin (((c :: rest).get i : ℕ)),
        (flipIdx (runCubes s χ) (faceEmb (beadFace χ i) p)
            < flipIdx (runCubes s χ) (faceEmb (beadFace χ i) q)
          ↔ cubeRunHeight (beadRun (c :: rest) s i) p
            < cubeRunHeight (beadRun (c :: rest) s i) q)) ?_ (fun j => ?_) i p q
    · intro p q
      have hf : ∀ x : Fin (((c :: rest).get 0 : ℕ)),
          Flips (runCubes s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ)) (faceEmb (beadFace χ 0) x) :=
        fun x => (flips_runCubes_cube s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ) _).mpr ⟨x, rfl⟩
      have hL : ∀ x : Fin (((c :: rest).get 0 : ℕ)),
          (flipIdx (runCubes s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ))
              (faceEmb (beadFace χ 0) x) : ℤ) = cubeRunHeight s₁ x :=
        fun x => flipIdx_cubeRun (c : ℕ) s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ) x
      rw [hs, flipIdx_append_left (hf p), flipIdx_append_left (hf q), beadRun_zero, ← hs₁,
        ← Nat.cast_lt (α := ℤ), hL p, hL q]
      exact Iff.rfl
    · intro p q
      -- a later bead's coordinate is not flipped by the head bead: `flipIdx` would return `0`
      have hnot : ∀ x : Fin (((c :: rest).get j.succ : ℕ)),
          ¬ Flips (runCubes s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ))
            (faceEmb (beadFace χ j.succ) x) := by
        intro x hx
        obtain ⟨z, hz⟩ := (flips_runCubes_cube s₁ (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ) _).mp hx
        have h0 : flipIdx (cubesOf (c :: rest) χ)
            (faceEmb (cubeFace (wedgeInl (□(c : ℕ)) (⋁rest) ≫ χ)) z) = 0 :=
          flipIdx_faceEmb_beadFace χ 0 z
        have h1 := flipIdx_faceEmb_beadFace χ j.succ x
        rw [← hz, h0, Fin.val_succ] at h1
        omega
      rw [hs, flipIdx_append_right (hnot p), flipIdx_append_right (hnot q),
        Nat.add_lt_add_iff_right, beadRun_succ, ← hs₂, beadFace_succ]
      exact runFlipIdx_lt_iff_bead rest s₂ (wedgeInr (□(c : ℕ)) (⋁rest) ≫ χ) j p q

/-! ## Part 4 — restriction is bead-local

`runRestrict f` is precomposition with `f` under the classification, so bead `i` of the restricted
run is read off `ιᵂ A i ≫ f`, which `blockFace_spec` factors through bead `blockIdx f i`. -/

/-- **Bead `i` of a restricted run** is bead `blockIdx f i` of the original, restricted along
`blockFace f i`. -/
theorem beadRun_runRestrict {A B : List ℕ+} (f : ⋁A ⟶ ⋁B) (r : Run (⋁B)) (i : Fin A.length) :
    beadRun A (runRestrict f r) i
      = runRestrictFace (yoneda.map (blockFace f.hom i)) (beadRun B r (blockIdx f.hom i)) := by
  have hspec : ιᵂ A i ≫ f.hom ≫ pshOfRun B r
      = yoneda.map (blockFace f.hom i) ≫ ιᵂ B (blockIdx f.hom i) ≫ pshOfRun B r :=
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ pshOfRun B r) (blockFace_spec f.hom i))).trans (Category.assoc _ _ _)
  have h0 : runYoneda (beadRun B r (blockIdx f.hom i))
      = ιᵂ B (blockIdx f.hom i) ≫ pshOfRun B r := yonedaEquiv.symm_apply_apply _
  rw [runRestrictFace_eq, h0, beadRun, runRestrict, pshOfRun_runOfPsh]
  exact congrArg yonedaEquiv hspec

/-! ## Part 5 — the wall-crossing law -/

/-- A sign of a difference is determined by the two strict orders. -/
theorem sign_sub_eq_of_lt_iff {x y z w : ℤ} (h1 : x < y ↔ z < w) (h2 : y < x ↔ w < z) :
    sign (x - y) = sign (z - w) := by
  rcases lt_trichotomy x y with h | h | h
  · rw [sign_neg (by omega), sign_neg (by have := h1.mp h; omega)]
  · have hzw : ¬ z < w := fun hc => absurd (h1.mpr hc) (by omega)
    have hwz : ¬ w < z := fun hc => absurd (h2.mpr hc) (by omega)
    rw [show x - y = 0 by omega, show z - w = 0 by omega]
  · rw [sign_pos (by omega), sign_pos (by have := h2.mp h; omega)]

/-- The covector height of a chain, as a `flipIdx`. -/
theorem chCovectorHeight_eq_flipIdx (a : Ch (□n)) (p : Fin n) :
    chCovectorHeight a p = (flipIdx (cubesOf a.dims a.map.hom) p : ℤ) := rfl

/-- The height of a coordinate under a run, as a `flipIdx`. -/
theorem runHeight_eq_flipIdx (a : Ch (□n)) (s : Run (⋁a.dims)) (p : Fin n) :
    runHeight a s p = (flipIdx (runCubes s a.map.hom) p : ℤ) := rfl

/-- The covector height of a chain of `□ⁿ` names the bead of the event that flips a coordinate. -/
theorem chCovectorHeight_cubeEv (a : Ch (□n)) (e : beadEvent a.dims) :
    chCovectorHeight a (cubeEv a.map e) = ((e.1 : ℕ) : ℤ) :=
  (chCovectorHeight_eq_flipIdx a _).trans
    (congrArg (fun k : ℕ => (k : ℤ)) (flipIdx_cubeEv a.map e))

/-- **Restriction preserves the order of the run inside one bead of `a`.**  Both sides are read
bead-locally by `runFlipIdx_lt_iff_bead`; `beadRun_runRestrict` identifies the two beads, and what
is left is the single-face law. -/
theorem runHeight_lt_iff_of_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims))
    (p q : Fin n) (heq : chCovectorHeight a p = chCovectorHeight a q) :
    (runHeight a (runRestrict f.φ r) p < runHeight a (runRestrict f.φ r) q
      ↔ runHeight b r p < runHeight b r q) := by
  obtain ⟨⟨i, p'⟩, rfl⟩ := (cubeEv_bijective a.map).surjective p
  obtain ⟨⟨i', q'⟩, rfl⟩ := (cubeEv_bijective a.map).surjective q
  obtain rfl : i = i' := by
    rw [chCovectorHeight_cubeEv a ⟨i, p'⟩, chCovectorHeight_cubeEv a ⟨i', q'⟩] at heq
    exact Fin.ext (by exact_mod_cast heq)
  -- the same event, named in `b`: its bead is `blockIdx f.φ i`, its coordinate travels along
  -- `blockFace f.φ i`
  have hcomp : ∀ x : Fin ((a.dims.get i : ℕ)),
      cubeEv a.map ⟨i, x⟩
        = faceEmb (beadFace b.map.hom (blockIdx f.φ.hom i)) (faceEmb (blockFace f.φ.hom i) x) := by
    intro x
    rw [show a.map = f.φ ≫ b.map from f.w.symm]
    exact cubeEv_comp f.φ b.map ⟨i, x⟩
  rw [runHeight_eq_flipIdx, runHeight_eq_flipIdx, runHeight_eq_flipIdx, runHeight_eq_flipIdx,
    Nat.cast_lt, Nat.cast_lt]
  refine (runFlipIdx_lt_iff_bead a.dims (runRestrict f.φ r) a.map.hom i p' q').trans ?_
  rw [hcomp p', hcomp q']
  refine Iff.trans ?_
    (runFlipIdx_lt_iff_bead b.dims r b.map.hom (blockIdx f.φ.hom i)
      (faceEmb (blockFace f.φ.hom i) p') (faceEmb (blockFace f.φ.hom i) q')).symm
  rw [beadRun_runRestrict f.φ r i, cubeRunHeight_runRestrictFace_lt_iff,
    show cubeFace (yoneda.map (blockFace f.φ.hom i)) = blockFace f.φ.hom i from
      yonedaEquiv_yoneda_map _]

/-- **The bead-local half of the Salvetti wall-crossing law** — the hypothesis of
`wallCrossing_of_sameBlock`, discharged. -/
theorem wallCrossing_sameBlock {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims))
    (e : BraidGround n) (heq : chCovectorHeight a e.1.1 = chCovectorHeight a e.1.2) :
    sign (runHeight a (runRestrict f.φ r) e.1.1 - runHeight a (runRestrict f.φ r) e.1.2)
      = sign (runHeight b r e.1.1 - runHeight b r e.1.2) :=
  sign_sub_eq_of_lt_iff (runHeight_lt_iff_of_sameBlock f r e.1.1 e.1.2 heq)
    (runHeight_lt_iff_of_sameBlock f r e.1.2 e.1.1 heq.symm)

/-- **The Salvetti wall-crossing law.**  Restricting a run along `f : a ⟶ b` composes `a`'s
covector into the run's tope. -/
theorem wallCrossing {a b : Ch (□n)} (f : a ⟶ b) (r : Run (⋁b.dims)) :
    braidSign (runHeight a (runRestrict f.φ r))
      = braidSign (chCovectorHeight a) ⊙ braidSign (runHeight b r) :=
  wallCrossing_of_sameBlock f r (fun e he => wallCrossing_sameBlock f r e he)

/-! ## Part 6 — the Salvetti comparison of presheaves

`runTopeEquiv` is objectwise a bijection; `wallCrossing` is exactly its naturality square, since
`salFunctor`'s restriction map *is* the wall-crossing composition `X' ⊙ ·`. -/

/-- **Runs are the Salvetti presheaf of the braid arrangement.** -/
def salLinesIso (n : ℕ) :
    Lines (□n) ≅ (chFaceEquiv n).functor ⋙ COM.salFunctor (braidCOM n) :=
  NatIso.ofComponents (fun a => Equiv.toIso (runTopeEquiv a.unop)) (by
    intro a b f
    ext r
    exact Subtype.ext (wallCrossing f.unop r))

end CubeChains
