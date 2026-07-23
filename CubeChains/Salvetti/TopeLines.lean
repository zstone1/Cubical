import CubeChains.Salvetti.Topes
import CubeChains.Salvetti.Conc

/-!
# Salvetti/TopeLines — runs of a cube *are* topes of the braid arrangement

Step 1 of the comparison `Int(Lines K) ≃ Sal`: the run presheaf and the tope presheaf are the same
presheaf on `Box`.  Objectwise `runTopeEquiv` sends a run to the braid face `chFace` of its ordered
partition (a tope because that partition is a *no-tie* injective height); naturality is
`beadOf_restrict_lt`, the single-cube restriction-preserves-order fact.  Whiskering the resulting
`runTopeIso` under `pshExtFunctor` identifies `topeLines K` with `Lines K`.
-/

open CategoryTheory Opposite BPSet CubeChain ChainCat

namespace CubeChains

/-! ### The point `□0` -/

/-- Every tope of the empty ground set is the same (`BraidGround 0` is empty). -/
theorem tope_cube0_eq (S T : Tope 0) : S = T := Subtype.ext (funext fun e => e.1.1.elim0)

/-! ### The objectwise bijection `Run (□n) ≃ Tope n` -/

/-- **`beadOf` is a bijection exactly when the partition is all-singletons** — its `n` coordinates
land in `dims.length` beads surjectively, so bijectivity pins the bead count to `n`. -/
theorem beadOf_bijective_iff_length_eq {n : ℕ} (c : Ch (□n)) :
    Function.Bijective (beadOf c) ↔ c.dims.length = n := by
  rw [Fintype.bijective_iff_surjective_and_card, Fintype.card_fin, Fintype.card_fin]
  exact ⟨fun h => h.2.symm, fun h => ⟨beadOf_surjective c, h.symm⟩⟩

/-- **A run's braid face is a tope** — its ordered partition `beadOf` is a *bijection* on a cube
(all beads positive-dimensional, total dimension `n`), so the realising height is injective. -/
theorem isTope_chFace_run {n : ℕ} (r : Run (□n)) : (braidCOM n).IsTope (chFace r.chain).1 := by
  refine (braidCOM_isTope_iff_injective _).mpr ⟨fun q => ((beadOf r.chain q : ℕ) : ℤ), ?_, rfl⟩
  have hlen : r.chain.dims.length = n := by
    have h1 : dimSum r.chain.dims = r.chain.dims.length :=
      dimSum_eq_length_of_ones (l := r.chain.dims) r.ones
    have h2 : dimSum r.chain.dims = n := wedgeDimSum_eq r.chain.map
    omega
  have hbij : Function.Bijective (beadOf r.chain) :=
    (beadOf_bijective_iff_length_eq r.chain).mpr hlen
  exact fun a b hab => hbij.injective (Fin.val_injective (Nat.cast_injective (R := ℤ) hab))

/-- `dimSum` is bounded below by the length: every bead has positive dimension. -/
theorem length_le_dimSum (l : List ℕ+) : l.length ≤ dimSum l := by
  rw [dimSum_sum]
  simpa only [List.length_map] using
    List.length_le_sum_of_one_le (l.map (fun d : ℕ+ => (d : ℕ)))
      (fun i hi => by obtain ⟨d, _, rfl⟩ := List.mem_map.mp hi; exact d.pos)

/-- **All beads are edges when the total dimension equals the bead count** — the converse of
`dimSum_eq_length_of_ones`, forcing every `dᵢ = 1`. -/
theorem all_one_of_dimSum_eq_length : ∀ {l : List ℕ+}, dimSum l = l.length → ∀ d ∈ l, d = 1
  | [], _ => by intro d hd; simp at hd
  | a :: rest, h => by
      have hcons : dimSum (a :: rest) = (a : ℕ) + dimSum rest := by
        simp only [dimSum_sum, List.map_cons, List.sum_cons]
      have hrest := length_le_dimSum rest
      have ha : 0 < (a : ℕ) := a.pos
      rw [hcons, List.length_cons] at h
      have ha1 : (a : ℕ) = 1 := by omega
      have hdr : dimSum rest = rest.length := by omega
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hmem
      · exact PNat.coe_injective ha1
      · exact all_one_of_dimSum_eq_length hdr d hmem

/-- **The chain reconstructed from a tope is a run** — a tope is a no-tie covector, so its
partition `beadOf` is injective; injective + surjective forces `c.dims.length = n`, and against
`dimSum c.dims = n` every bead is an edge. -/
theorem isRun_chFaceEquiv_symm {n : ℕ} (T : Tope n) :
    IsRun (□n) (chFaceEquiv.symm ⟨T.1, T.2.1⟩) := by
  set c := chFaceEquiv.symm ⟨T.1, T.2.1⟩ with hc
  have hface : chFaceEquiv c = ⟨T.1, T.2.1⟩ := chFaceEquiv.apply_symm_apply _
  have htope : (braidCOM n).IsTope (chFace c).1 := by
    have hval : (chFace c).1 = T.1 := congrArg Subtype.val hface
    rw [hval]; exact T.2
  have htope2 : ∀ e, (chFace c).1 e ≠ 0 := ((braidCOM_isTope_iff _).mp htope).2
  have hbeadinj : Function.Injective (beadOf c) := by
    intro i j hij
    by_contra hne
    have hcast : ((beadOf c i : ℕ) : ℤ) = ((beadOf c j : ℕ) : ℤ) := by rw [hij]
    rcases lt_or_gt_of_ne hne with h | h
    · exact htope2 ⟨(i, j), h⟩
        ((braidSign_zero_iff (fun q => ((beadOf c q : ℕ) : ℤ)) ⟨(i, j), h⟩).mpr hcast)
    · exact htope2 ⟨(j, i), h⟩
        ((braidSign_zero_iff (fun q => ((beadOf c q : ℕ) : ℤ)) ⟨(j, i), h⟩).mpr hcast.symm)
  have hlen : c.dims.length = n :=
    (beadOf_bijective_iff_length_eq c).mp ⟨hbeadinj, beadOf_surjective c⟩
  have hdimSum : dimSum c.dims = n := wedgeDimSum_eq c.map
  exact all_one_of_dimSum_eq_length (by rw [hdimSum, hlen])

/-- **A run of `□n` is a tope of `braidCOM n`** — the braid face of its ordered partition. -/
def runTopeEquiv (n : ℕ) : Run (□n) ≃ Tope n where
  toFun r := ⟨(chFace r.chain).1, isTope_chFace_run r⟩
  invFun T := ⟨chFaceEquiv.symm ⟨T.1, T.2.1⟩, isRun_chFaceEquiv_symm T⟩
  left_inv r := Run.ext (by
    change chFaceEquiv.symm ⟨(chFace r.chain).1, (isTope_chFace_run r).1⟩ = r.chain
    rw [show (⟨(chFace r.chain).1, (isTope_chFace_run r).1⟩ : COM.Face (braidCOM n))
          = chFace r.chain from Subtype.ext rfl]
    exact chFaceEquiv.symm_apply_apply r.chain)
  right_inv T := Subtype.ext (by
    change (chFace (chFaceEquiv.symm ⟨T.1, T.2.1⟩)).1 = T.1
    exact congrArg Subtype.val (chFaceEquiv.apply_symm_apply ⟨T.1, T.2.1⟩))

/-! ### Naturality: face restriction preserves the run order -/

open SignType in
/-- The sign of a difference of naturals is fixed by the strict order in both directions. -/
private theorem sign_natCast_sub_eq {a₁ a₂ b₁ b₂ : ℕ}
    (hlt : a₁ < a₂ ↔ b₁ < b₂) (hgt : a₂ < a₁ ↔ b₂ < b₁) :
    sign ((a₁ : ℤ) - (a₂ : ℤ)) = sign ((b₁ : ℤ) - (b₂ : ℤ)) := by
  rcases lt_trichotomy a₁ a₂ with h | h | h
  · rw [sign_neg (show (a₁ : ℤ) - (a₂ : ℤ) < 0 by omega),
        sign_neg (show (b₁ : ℤ) - (b₂ : ℤ) < 0 by have := hlt.mp h; omega)]
  · have hb : b₁ = b₂ := by
      by_contra hbne
      rcases lt_or_gt_of_ne hbne with hb | hb
      · exact absurd (hlt.mpr hb) (by omega)
      · exact absurd (hgt.mpr hb) (by omega)
    rw [h, hb, sub_self, sub_self]
  · rw [sign_pos (show (0 : ℤ) < (a₁ : ℤ) - (a₂ : ℤ) by omega),
        sign_pos (show (0 : ℤ) < (b₁ : ℤ) - (b₂ : ℤ) by have := hgt.mp h; omega)]

/-- **`chFace` commutes with restriction** — restricting the tope of a run along a face gives the
tope of the restricted run, `beadOf_restrict_lt` matching the two orders coordinatewise. -/
theorem chFace_topeRestrict {d e : ℕ} (r : Run (□d)) (g : ▫e ⟶ ▫d) :
    (chFace ((runPresheaf.map g.op r).chain)).1 = topeRestrict g (chFace r.chain).1 := by
  change braidSign (fun k => ((beadOf ((runPresheaf.map g.op r).chain) k : ℕ) : ℤ))
      = braidSign (fun k => ((beadOf r.chain (faceEmb g k) : ℕ) : ℤ))
  funext epair
  have hlt := beadOf_restrict_lt r g epair.1.1 epair.1.2
  have hgt := beadOf_restrict_lt r g epair.1.2 epair.1.1
  simp only [Fin.lt_def] at hlt hgt
  simp only [braidSign_apply]
  exact sign_natCast_sub_eq hlt hgt

/-- **Runs and topes are the same presheaf on `Box`.** -/
def runTopeIso : runPresheaf ≅ topePresheaf :=
  NatIso.ofComponents (fun X => (runTopeEquiv X.unop.dim).toIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro r
    exact Subtype.ext (chFace_topeRestrict r f.unop))

/-! ### The tope refinement presheaf, identified with `Lines` -/

/-- **The tope presheaf.**  `topeLines K a = (⋁a.dims).toPsh ⟶ topePresheaf`, the tope analogue of
`Lines K` — the contravariant lift `pshExtFunctor topePresheaf` along `linesWedge`. -/
def topeLines (K : BPSet) : (Ch K)ᵒᵖ ⥤ Type := (linesWedge K).op ⋙ pshExtFunctor topePresheaf

/-- **`topeLines K ≅ Lines K`** — `runTopeIso` whiskered under the lift `pshExtFunctor`. -/
def topeLinesIsoLines (K : BPSet) : topeLines K ≅ Lines K :=
  Functor.isoWhiskerLeft (linesWedge K).op (pshExtFunctorFunctor.mapIso runTopeIso).symm

end CubeChains
