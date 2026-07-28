import CubeChains.Salvetti.RunWord

/-!
# Salvetti/ExecData — an execution of `□n` is a chain plus a linearization of it

`execEquiv : Ch⋆ (□n) ≃ ExecData n` presents an execution as its chain `C` together with the run
word `w` linearizing it, subject to one condition: `C`'s ordered partition must be coarser than
`w`'s (`chFace C ⊑ chFace (wordChain w)`) — which is the Salvetti condition `X ⊑ T` on a cell of
`braidCOM n`, since `chFaceEquiv` reads faces as chains and `wordChain` reads topes as words.

Both halves are explicit.  Completeness (`ext_runWord`) is thinness of `Ch (□n)`: the run's map is
a *morphism* onto the chain, so the chain it linearizes determines it.  The construction (`ofWord`)
is `reflectHom` between the two `blockChain`s, so it computes.
-/

open CategoryTheory CubeChain BPSet Opposite

namespace CubeChains

open ChStar

variable {n L : ℕ}

/-! ## A run is pinned by the chain it linearizes

The run's classifying map `r.map` is itself a *morphism* `totalChain C r ⟶ C` in `Ch (□n)`, and
that category is thin — so nothing else can linearize the same chain. -/

/-- The chain of `□n` a run of `⋁C.dims` linearizes. -/
def totalChain (C : Ch (□n)) (r : Run (⋁C.dims)) : Ch (□n) := ⟨r.dims, r.map ≫ C.map⟩

/-- Two wedge maps that agree after `C.map` agree — `Ch (□n)` is thin. -/
theorem map_ext_over {C : Ch (□n)} {d : List ℕ+} {m m' : ⋁d ⟶ ⋁C.dims}
    (h : m ≫ C.map = m' ≫ C.map) : m = m' :=
  congrArg ChainCat.Hom.φ
    ((chainCat_hom_subsingleton (cube_nonSelfLinked n) (BPSet.cube_admitsAltitude n)
      (⟨d, m ≫ C.map⟩ : Ch (□n)) C).elim ⟨m, rfl⟩ ⟨m', h.symm⟩)

/-- **A run is determined by the chain it linearizes.** -/
theorem run_eq_of_totalChain {C : Ch (□n)} (r s : Run (⋁C.dims))
    (h : totalChain C r = totalChain C s) : r = s := by
  obtain ⟨hd, hm⟩ := ChainCat.Obj.eq_mk_of_eq h
  refine Run.ext (ChainCat.Obj.mk_eq_mk hd (map_ext_over ?_))
  rw [Category.assoc]
  exact hm

namespace ChStar

/-- The run word determines the chain the run linearizes. -/
theorem runChain_eq_of_runWord {x y : Ch⋆ (□n)} (hw : runWord x = runWord y) :
    runChain x = runChain y :=
  eq_of_beadOf fun q => by rw [← runWord_symm_val, ← runWord_symm_val, hw]

/-- **Executions are pinned by their chain and their run word.**  This is what makes an enumeration
of run words *complete*. -/
theorem ext_runWord {x y : Ch⋆ (□n)} (hc : x.chain = y.chain) (hw : runWord x = runWord y) :
    x = y := by
  obtain ⟨cx, ax⟩ := x
  obtain ⟨cy, ay⟩ := y
  obtain rfl : cx = cy := Opposite.unop_injective hc
  refine congrArg (Sigma.mk cx) ((runPshEquiv cx.unop.dims).injective ?_)
  exact run_eq_of_totalChain _ _ (runChain_eq_of_runWord hw)

/-- An execution refines its own linearization. -/
def runRefine (x : Ch⋆ (□n)) : runChain x ⟶ x.chain := ⟨x.run.map, rfl⟩

/-- The chain of an execution is coarser than its run. -/
theorem chFace_runChain_le (x : Ch⋆ (□n)) :
    (chFace x.chain).1 ⊑ (chFace (runChain x)).1 :=
  chFace_faceLE (runRefine x)

end ChStar

/-! ## Building an execution from a word -/

/-- **The all-edges chain performing the directions in the order `w`** — one bead per step. -/
def wordChain (w : Equiv.Perm (Fin n)) : Ch (□n) := blockChain ⇑w.symm w.symm.surjective

theorem beadOf_wordChain (w : Equiv.Perm (Fin n)) (q : Fin n) :
    (beadOf (wordChain w) q : ℕ) = (w.symm q : ℕ) := beadOf_blockChain _ _ q

theorem length_wordChain (w : Equiv.Perm (Fin n)) : (wordChain w).dims.length = n :=
  length_blockChain _ _

theorem ones_wordChain (w : Equiv.Perm (Fin n)) : ∀ d ∈ (wordChain w).dims, d = 1 :=
  ones_of_dimSum_eq_length
    ((wedgeDimSum_eq (wordChain w).map).trans (length_wordChain w).symm)

/-- The compatibility a word must satisfy to linearize the blocks of `β`: `β`'s strict order is
`w`'s wherever `β` separates. -/
def WordCompat (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L) : Prop :=
  ∀ i j, β i ≠ β j → (β i < β j ↔ w.symm i < w.symm j)

theorem faceLE_of_wordCompat {w : Equiv.Perm (Fin n)} {β : Fin n → Fin L}
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    (chFace (blockChain β hβ)).1 ⊑ (chFace (wordChain w)).1 := by
  refine chFace_faceLE_iff.mpr fun i j hne => ?_
  rw [beadOf_blockChain, beadOf_blockChain] at hne
  rw [beadOf_blockChain, beadOf_blockChain, beadOf_wordChain, beadOf_wordChain]
  exact hc i j (fun he => hne (congrArg Fin.val he))

theorem wordCompat_of_faceLE {w : Equiv.Perm (Fin n)} {β : Fin n → Fin L}
    (hβ : Function.Surjective β)
    (h : (chFace (blockChain β hβ)).1 ⊑ (chFace (wordChain w)).1) : WordCompat w β := by
  intro i j hne
  have hval := chFace_faceLE_iff.mp h i j (by
    rw [beadOf_blockChain, beadOf_blockChain]; exact fun he => hne (Fin.val_injective he))
  rw [beadOf_blockChain, beadOf_blockChain, beadOf_wordChain, beadOf_wordChain] at hval
  exact hval

/-- The refinement of `blockChain β` by the run `w` performs. -/
def wordRefine {w : Equiv.Perm (Fin n)} {β : Fin n → Fin L} (hβ : Function.Surjective β)
    (hc : WordCompat w β) : wordChain w ⟶ blockChain β hβ :=
  reflectHom (faceLE_of_wordCompat hβ hc)

/-- **The execution performing the directions in the order `w`, with beads the blocks of `β`.** -/
def ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (hc : WordCompat w β) : Ch⋆ (□n) :=
  ⟨op (blockChain β hβ),
    (runPshEquiv (blockChain β hβ).dims).symm
      ⟨⟨(wordChain w).dims, (wordRefine hβ hc).φ⟩, ones_wordChain w⟩⟩

@[simp] theorem chain_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L)
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    (ofWord w β hβ hc).chain = blockChain β hβ := rfl

theorem run_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L) (hβ : Function.Surjective β)
    (hc : WordCompat w β) :
    (ofWord w β hβ hc).run = ⟨⟨(wordChain w).dims, (wordRefine hβ hc).φ⟩, ones_wordChain w⟩ :=
  (runPshEquiv (blockChain β hβ).dims).apply_symm_apply _

theorem runChain_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L)
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    runChain (ofWord w β hβ hc) = wordChain w :=
  (congrArg (totalChain (blockChain β hβ)) (run_ofWord w β hβ hc)).trans
    (congrArg (ChainCat.Obj.mk (wordChain w).dims) (wordRefine hβ hc).w)

@[simp] theorem runWord_ofWord (w : Equiv.Perm (Fin n)) (β : Fin n → Fin L)
    (hβ : Function.Surjective β) (hc : WordCompat w β) :
    runWord (ofWord w β hβ hc) = w :=
  runWord_of_runChain_ofBlockMap _ w (runChain_ofWord w β hβ hc)

/-! ## Completeness: every execution is `ofWord` of its own data -/

namespace ChStar

/-- The chain a run linearizes is the word chain of its run word. -/
theorem runChain_eq_wordChain (x : Ch⋆ (□n)) : runChain x = wordChain (runWord x) :=
  eq_of_beadOf fun q => (runWord_symm_val x q).symm.trans (beadOf_wordChain _ q).symm

theorem wordCompat_runWord (x : Ch⋆ (□n)) : WordCompat (runWord x) (beadOf x.chain) := by
  refine wordCompat_of_faceLE (beadOf_surjective x.chain) ?_
  rw [blockChain_beadOf, ← runChain_eq_wordChain]
  exact chFace_runChain_le x

/-- **Every execution is built from its own chain and run word.** -/
theorem eq_ofWord (x : Ch⋆ (□n)) :
    ofWord (runWord x) (beadOf x.chain) (beadOf_surjective x.chain) (wordCompat_runWord x) = x :=
  ext_runWord (by rw [chain_ofWord, blockChain_beadOf]) (by rw [runWord_ofWord])

end ChStar

/-! ## The object equivalence -/

/-- **The data of an execution of `□n`**: a chain together with a run word linearizing it. -/
def ExecData (n : ℕ) : Type :=
  {p : Ch (□n) × Equiv.Perm (Fin n) // (chFace p.1).1 ⊑ (chFace (wordChain p.2)).1}

/-- The chain and run word of an execution. -/
def execData (x : Ch⋆ (□n)) : ExecData n :=
  ⟨(x.chain, runWord x), by
    rw [← ChStar.runChain_eq_wordChain]; exact ChStar.chFace_runChain_le x⟩

/-- The execution a chain-plus-word names. -/
def ofExecData (p : ExecData n) : Ch⋆ (□n) :=
  ofWord p.1.2 (beadOf p.1.1) (beadOf_surjective p.1.1)
    (wordCompat_of_faceLE (beadOf_surjective p.1.1) (by rw [blockChain_beadOf]; exact p.2))

@[simp] theorem chain_ofExecData (p : ExecData n) : (ofExecData p).chain = p.1.1 := by
  refine Eq.trans ?_ (blockChain_beadOf p.1.1)
  exact chain_ofWord p.1.2 (beadOf p.1.1) (beadOf_surjective p.1.1) _

@[simp] theorem runWord_ofExecData (p : ExecData n) : runWord (ofExecData p) = p.1.2 :=
  runWord_ofWord p.1.2 (beadOf p.1.1) (beadOf_surjective p.1.1) _

theorem execData_ofExecData (p : ExecData n) : execData (ofExecData p) = p := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact chain_ofExecData p
  · exact runWord_ofExecData p

/-- **An execution of `□n` is a chain plus a linearization of it.** -/
def execEquiv : Ch⋆ (□n) ≃ ExecData n where
  toFun := execData
  invFun := ofExecData
  left_inv := ChStar.eq_ofWord
  right_inv := execData_ofExecData

end CubeChains
