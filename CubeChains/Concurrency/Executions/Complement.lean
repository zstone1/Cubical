import CubeChains.Concurrency.Executions.RunPerm
import CubeChains.Concurrency.Grading.CodimTwo
import CubeChains.Concurrency.Merge.CubeCrossing

/-!
# Concurrency/Executions/Complement — the complementary run, and its length

A run of `⋁d` **is** a map into the classifier, `(⋁d).toPsh ⟶ runPresheaf` (`runPshEquiv`), and
`revRunPsh` is a natural involution of it.  The **complement** is post-composition with that:

    ⋁d ──run──▸ runPresheaf ──revRunPsh──▸ runPresheaf

Naturality is the whole theory.  It meets the Segal splitting leg by leg (`runSplit_compl`), so a
run and its complement split the shape's capacity (`permLen_cross_add_compl`) — the complement is
the longest element of the shape's parabolic, and the bound, the attainment and the uniqueness are
its three corollaries.
-/

open CategoryTheory CategoryTheory.MonoidalCategory Opposite BPSet ChainCat CubeChain

namespace CubeChains

/-- **Reversal is a natural endomorphism of `runPresheaf`** — `Run.rev_restrict`. -/
def revRunPsh : runPresheaf ⟶ runPresheaf where
  app _ := TypeCat.ofHom Run.rev
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro r
    exact (Run.rev_restrict f.unop r).symm

/-- …and an involution. -/
@[simp] theorem revRunPsh_comp_self : revRunPsh ≫ revRunPsh = 𝟙 runPresheaf := by
  refine NatTrans.ext (funext fun _ => ?_)
  apply ConcreteCategory.hom_ext
  intro r
  exact Run.rev_rev r

/-! ## The complement of a run of a wedge

A run of `⋁d` is a map to the classifier (`runPshEquiv`), so reversing every bead at once is
post-composing it with `revRunPsh`. -/

/-- **The complement of a run of a wedge**: reversed inside each bead.  On a bead cut into `k`
pieces it is the longest element of `Sₖ`, so it carries the merge to the greatest crossing. -/
noncomputable def Run.compl {d : List ℕ+} (r : Run (⋁d)) : Run (⋁d) :=
  runPshEquiv d ((runPshEquiv d).symm r ≫ revRunPsh)

/-- The complement's classifier, by definition of `Run.compl`. -/
theorem runPshEquiv_symm_compl {d : List ℕ+} (r : Run (⋁d)) :
    (runPshEquiv d).symm r.compl = (runPshEquiv d).symm r ≫ revRunPsh :=
  (runPshEquiv d).symm_apply_apply _

/-- **The complement is an involution** — `revRunPsh` is. -/
@[simp] theorem Run.compl_compl {d : List ℕ+} (r : Run (⋁d)) : r.compl.compl = r := by
  rw [Run.compl, runPshEquiv_symm_compl, Category.assoc, revRunPsh_comp_self, Category.comp_id,
    Equiv.apply_symm_apply]

/-- **The complement acts bead by bead** — `beadCell_comp`, since it is a post-composition. -/
theorem runProj_compl {d : List ℕ+} (r : Run (⋁d)) (i : Fin d.length) :
    runProj r.compl i = Run.rev (runProj r i) := by
  rw [runProj, runProj, Run.compl, Equiv.symm_apply_apply, CubeChain.beadCell_comp]
  rfl

/-- **The complement splits at a junction** — post-composition meets the Segal decomposition on
each leg: the head through `runProj`, the tail through the classifier's right leg. -/
theorem runSplit_compl (c : ℕ+) (rest : List ℕ+) (r : Run (⋁(c :: rest))) :
    runSplit (consAltitude c rest) r.compl
      = ((runSplit (consAltitude c rest) r).1.rev, (runSplit (consAltitude c rest) r).2.compl) :=
  Prod.ext
    (((runProj_zero c rest r.compl).symm.trans (runProj_compl r 0)).trans
      (congrArg Run.rev (runProj_zero c rest r)))
    ((runPshEquiv rest).symm.injective
      ((((runPshEquiv_symm_inr c rest r.compl).symm.trans
              (congrArg (fun t => wedgeInr (□(c : ℕ)) (⋁rest) ≫ t)
                (runPshEquiv_symm_compl r))).trans
            ((Category.assoc (wedgeInr (□(c : ℕ)) (⋁rest))
                  ((runPshEquiv (c :: rest)).symm r) revRunPsh).symm.trans
              (congrArg (fun t => t ≫ revRunPsh) (runPshEquiv_symm_inr c rest r)))).trans
        (runPshEquiv_symm_compl (runSplit (consAltitude c rest) r).2).symm))

/-! ## What a run crosses

The shape a run refines a wedge by is a chain of `Zbp`, so a run has a crossing permutation; it is
monoidal over the junctions, and the classifier's reversal shifts it by the reversal in each bead.
-/

/-- **The permutation of `⋁d`'s events a run performs.** -/
noncomputable def Run.cross {d : List ℕ+} (r : Run (⋁d)) : Equiv.Perm (Fin (dimSum d)) :=
  crossPerm (a := zObj r.dims) (serialWedge_dimSum_eq r.map) (zHom r.map)

/-- **A run is pinned by what it crosses** — a run carries no data but its wedge map, and
`crossPerm` pins that. -/
theorem Run.cross_injective {d : List ℕ+} : Function.Injective (Run.cross (d := d)) := by
  rintro ⟨⟨rd, rm⟩, rp⟩ ⟨⟨sd, sm⟩, sp⟩ h
  obtain rfl : rd = sd :=
    ones_eq_of_dimSum_eq rp sp
      ((serialWedge_dimSum_eq rm).trans (serialWedge_dimSum_eq sm).symm)
  exact Run.ext (congrArg (fun φ => (⟨rd, φ⟩ : Ch (⋁d)))
    (congrArg ChainCat.Hom.φ (hom_ext_of_crossPerm h)))

/-- **A chain of `□n` crosses at the base what it crosses in the cube** — `serialWedge1` *is* the
coarsest chain's classifying map, so the base refinement is `toCubeTop` in another spelling. -/
theorem cross_eq_crossPerm_zHom {n : ℕ+} (A : Ch (□(n : ℕ))) (h : dimSum A.dims = (n : ℕ)) :
    crossPerm (a := zObj A.dims) h (zHom (e := [n]) (A.map ≫ (serialWedge1 n).inv)) = cross A := by
  obtain ⟨_ | k, hn⟩ := n
  · exact absurd hn (by omega)
  · exact crossPerm_eq_of_φ h rfl

/-- **The crossing of a wedge concatenation is the block sum** — `crossPerm_chConcat` read on
`Ch Zbp`, where a wedge map *is* a chain map (`zHom`).  The strand counts are named, so the
equation is between permutations of `Fin (m + n)` with no `Fin` transport. -/
theorem crossPerm_zHom_concat {e₁ e₂ dl dr : List ℕ+} (φ₁ : ⋁e₁ ⟶ ⋁dl) (φ₂ : ⋁e₂ ⟶ ⋁dr)
    {m n : ℕ} (h₁ : dimSum e₁ = m) (h₂ : dimSum e₂ = n) (h : dimSum (e₁ ++ e₂) = m + n) :
    crossPerm h (zHom (concatHomφ (zHom φ₁) (zHom φ₂)))
      = permSum m n (crossPerm h₁ (zHom φ₁), crossPerm h₂ (zHom φ₂)) := by
  subst h₁
  subst h₂
  refine Eq.trans ?_ (crossPerm_chConcat (ab := (zObj e₁, zObj e₂))
    (ab' := (zObj dl, zObj dr)) (zHom φ₁, zHom φ₂))
  exact crossPerm_eq_of_φ h rfl

/-- **`Run.cross` is monoidal over a junction.**  The two halves of the concatenation's classifying
map are the head bead read in its own one-bead wedge (the monoidal triangle, `⋁[]` being the unit)
and the tail read by its own classifying map. -/
theorem Run.cross_concat (c : ℕ+) (rest : List ℕ+) (ρ : Run (□(c : ℕ))) (s : Run (⋁rest)) :
    Run.cross (d := c :: rest) ((runConcat (□(c : ℕ)) (⋁rest)).obj (ρ, s))
      = permSum (c : ℕ) (dimSum rest) (ChainCat.cross ρ.chain, s.cross) := by
  have hB : dimSum s.dims = dimSum rest := serialWedge_dimSum_eq s.map
  have h : dimSum (ρ.dims ++ s.dims) = (c : ℕ) + dimSum rest := by
    rw [dimSum_append, dimSum_dims_cube, hB]
  have htri : (serialWedge1 c).hom ⊗ₘ 𝟙 (⋁rest) = serialWedgeAppendHom [c] rest :=
    (MonoidalCategory.tensorHom_id (serialWedge1 c).hom (⋁rest)).trans
      (MonoidalCategory.triangle (□(c : ℕ)) (⋁rest)).symm
  have hcomp : ((ρ.map ≫ (serialWedge1 c).inv) ⊗ₘ s.map)
      ≫ ((serialWedge1 c).hom ⊗ₘ 𝟙 (⋁rest)) = ρ.map ⊗ₘ s.map := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Category.comp_id]
  have hmap : concatHomφ (zHom (e := [c]) (ρ.map ≫ (serialWedge1 c).inv))
      (zHom (e := rest) s.map) = concatChainMap (□(c : ℕ)) (⋁rest) ρ.chain s.chain :=
    (congrArg (fun t => (serialWedgeAppend ρ.dims s.dims).inv
        ≫ (((ρ.map ≫ (serialWedge1 c).inv) ⊗ₘ s.map) ≫ t)) htri.symm).trans
      (congrArg (fun t => (serialWedgeAppend ρ.dims s.dims).inv ≫ t) hcomp)
  refine Eq.trans (crossPerm_eq_of_φ (db := [c] ++ rest) h
    (g' := zHom (concatHomφ (zHom (e := [c]) (ρ.map ≫ (serialWedge1 c).inv))
      (zHom (e := rest) s.map))) hmap.symm) ?_
  exact (crossPerm_zHom_concat _ _ (dimSum_dims_cube ρ.chain) hB h).trans
    (congrArg (fun σ => permSum (c : ℕ) (dimSum rest) (σ, s.cross))
      (cross_eq_crossPerm_zHom ρ.chain (dimSum_dims_cube ρ.chain)))

/-- **Reversing a bead's run multiplies its word by the reversal.** -/
theorem cross_rev {n : ℕ} (ρ : Run (□n)) : cross ρ.rev.chain = cross ρ.chain * Fin.revPerm := by
  obtain ⟨w, rfl⟩ : ∃ w, ρ = wordRun w :=
    ⟨runWordEquiv n ρ, ((runWordEquiv n).symm_apply_apply ρ).symm⟩
  rw [rev_wordRun, cross_wordRun, cross_wordRun]

/-! ## The complement is the longest run

The capacity is the pairs of events a shape makes concurrent, so a run and its complement split it:
inside a bead that is the reversal splitting `permLen Fin.revPerm`, and across a junction the
crossing counts add because the blocks never interact. -/

/-- **A run and its complement split the shape's capacity** — the parabolic length formula.  The
bound on every run, the attainment at the complement and its uniqueness are all read off this. -/
theorem permLen_cross_add_compl : ∀ (d : List ℕ+) (r : Run (⋁d)),
    permLen r.cross + permLen r.compl.cross = crossCap d
  | [], r => by
      rw [show permLen r.cross = 0 from Nat.le_zero.mp (permLen_le_choose _),
        show permLen r.compl.cross = 0 from Nat.le_zero.mp (permLen_le_choose _), crossCap_nil]
  | c :: rest, r => by
      rcases hp : runSplit (consAltitude c rest) r with ⟨ρ, s⟩
      have hsplit : r = (runConcat (□(c : ℕ)) (⋁rest)).obj (ρ, s) := by
        rw [← hp]; exact (runConcat_runSplit (consAltitude c rest) r).symm
      have hcompl : r.compl = (runConcat (□(c : ℕ)) (⋁rest)).obj (ρ.rev, s.compl) := by
        rw [← runConcat_runSplit (consAltitude c rest) r.compl, runSplit_compl c rest r, hp]
      have h1 : permLen r.cross = permLen (ChainCat.cross ρ.chain) + permLen s.cross :=
        ((congrArg (fun t : Run (⋁(c :: rest)) => permLen t.cross) hsplit).trans
          (congrArg permLen (Run.cross_concat c rest ρ s))).trans (permLen_permSum _ _)
      have h2 : permLen r.compl.cross
          = permLen (ChainCat.cross ρ.rev.chain) + permLen s.compl.cross :=
        ((congrArg (fun t : Run (⋁(c :: rest)) => permLen t.cross) hcompl).trans
          (congrArg permLen (Run.cross_concat c rest ρ.rev s.compl))).trans (permLen_permSum _ _)
      have hcube := permLen_mul_revPerm_add (ChainCat.cross ρ.chain)
      rw [permLen_revPerm, ← cross_rev ρ] at hcube
      have hIH := permLen_cross_add_compl rest s
      rw [h1, h2, crossCap_cons]
      omega

/-- **The capacity bounds every run over a shape** — a crossing is a set of pairs, and a run only
inverts the pairs one of the shape's beads holds. -/
theorem permLen_cross_le_crossCap {d : List ℕ+} (r : Run (⋁d)) : permLen r.cross ≤ crossCap d :=
  Nat.le.intro (permLen_cross_add_compl d r)

/-- **A run as long as the capacity is the complement of the one crossing nothing** — its own
complement crosses nothing, and a run is pinned by what it crosses. -/
theorem eq_compl_of_permLen {d : List ℕ+} {r b : Run (⋁d)} (hb : b.cross = 1)
    (hr : permLen r.cross = crossCap d) : r = b.compl := by
  have h := permLen_cross_add_compl d r
  rw [hr] at h
  exact (Run.compl_compl r).symm.trans
    (congrArg Run.compl
      (Run.cross_injective ((eq_one_of_permLen_eq_zero _ (by omega)).trans hb.symm)))

/-- **The complement fixes exactly the runs of degree zero** — a bead it fixes is an edge, since
`Fin.revPerm` moves every order on two or more axes (`Run.rev_ne`). -/
theorem Run.compl_ne {d : List ℕ+} (r : Run (⋁d)) (hd : BPSet.degree d ≠ 0) : r.compl ≠ r := by
  intro h
  refine hd ((BPSet.degree_eq_zero_iff d).mpr fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  by_contra hne
  have hval : 2 ≤ ((d.get i : ℕ)) := by
    rcases Nat.lt_or_ge ((d.get i : ℕ)) 2 with hlt | hge
    · exact absurd (show d.get i = 1 by
        exact_mod_cast Nat.le_antisymm (Nat.lt_succ_iff.mp hlt) (d.get i).2) hne
    · exact hge
  exact Run.rev_ne (runProj r i) hval
    ((runProj_compl r i).symm.trans (congrArg (fun s => runProj s i) h))

/-- **…and at degree zero it fixes every run** — the capacity is nothing, so a run and its
complement both cross nothing.  With `Run.compl_ne` this is the "exactly" its docstring claims. -/
theorem Run.compl_eq_self {d : List ℕ+} (r : Run (⋁d)) (hd : BPSet.degree d = 0) : r.compl = r := by
  have h := permLen_cross_add_compl d r
  rw [crossCap_eq_zero_of_degree hd] at h
  exact Run.cross_injective ((eq_one_of_permLen_eq_zero _ (by omega)).trans
    (eq_one_of_permLen_eq_zero _ (by omega)).symm)

end CubeChains
