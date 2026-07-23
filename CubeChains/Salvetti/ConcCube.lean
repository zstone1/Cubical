import CubeChains.Salvetti.ConcPure

/-!
# Salvetti/ConcCube — `Conc (□ⁿ)` is full onto the pure braids

Every execution of `□ⁿ` has `n` events, so `Conc (□n)` lands in the fibre `Braid n` of the braid
category, and it *is* the ungraded `cubeConc n` there (`concCubeIso`, whose components are the
strand-count identifications `Nev x = n`).  Transporting `ConcPure`'s two halves across it:

    the loops of executions at `x`  ↠  PureBraid n           (`conc_full_pureBraid`)
    the loops of executions at `x`  ↪  PureBraid n           (`conc_loop_mem_pureBraid`)

so the image of `Aut(x)` under `Conc (□n)` is exactly the pure braid group (`conc_loop_iff`).
Faithfulness — that the map is *injective* — is Salvetti's asphericity theorem and is not proved
here.
-/

open CategoryTheory Opposite BPSet ChainCat CubeChain Equiv FreeGroupoid

namespace CubeChains

variable {n : ℕ}

/-! ## Transport across the strand count -/

theorem braidTransport_symm_transport {m k : ℕ} (h : m = k) (b : Braid m) :
    braidTransport h.symm (braidTransport h b) = b := by subst h; rfl

theorem braidTransport_injective {m k : ℕ} (h : m = k) : Function.Injective (braidTransport h) := by
  subst h; exact fun _ _ hb => hb

theorem braidHom_injective {m : ℕ} {a b : Braid m} (h : braidHom a = braidHom b) : a = b := by
  injection h

/-! ## `Conc (□ⁿ)` is the ungraded functor -/

/-- The naturality square of the strand-count identification: `permOf_tope`, conjugated by
`eqToHom_comp_braidHom`. -/
private theorem concCube_naturality {x y : Ch⋆ (□n)} (f : x ⟶ y) :
    (ConcPos (□n)).map f ≫ eqToHom (congrArg strands (Nev_cube y))
      = eqToHom (congrArg strands (Nev_cube x)) ≫ braidHom (ofPerm (tope y * (tope x)⁻¹)) := by
  rw [← permOf_tope f, ← braidTransport_ofPerm (Nev_cube x) (permOf f),
    eqToHom_comp_braidHom (Nev_cube x), braidTransport_symm_transport]
  change (braidHom (ofPerm (permOf f)) ≫ eqToHom (congrArg strands (Nev_eq f)))
      ≫ eqToHom (congrArg strands (Nev_cube y)) = _
  rw [Category.assoc, eqToHom_trans]

/-- **`Conc (□n)` regraded.**  Its components are the strand-count identifications. -/
noncomputable def concCubeIso (n : ℕ) : Conc (□n) ≅ cubeConc n ⋙ braidIncl n :=
  FreeGroupoid.liftNatIso _ _ (NatIso.ofComponents
    (fun x => eqToIso (congrArg strands (Nev_cube x)))
    (fun {x y} f => by
      simpa only [Functor.comp_map, Conc, cubeConc, FreeGroupoid.lift_map_homMk, cubeConcPos,
        eqToIso.hom] using concCube_naturality f))

@[simp] theorem concCubeIso_hom_app (x : Ch⋆ (□n)) :
    (concCubeIso n).hom.app (mk x) = eqToHom (congrArg strands (Nev_cube x)) := by
  rw [concCubeIso, FreeGroupoid.liftNatIso_hom_app]
  rfl

/-- **The braid of a loop of executions**, read in `Braid n` through the strand count. -/
theorem conc_map_loop {x : Ch⋆ (□n)} (g : mk x ⟶ mk x) :
    (Conc (□n)).map g = braidHom (braidTransport (Nev_cube x).symm (concBraid g)) := by
  have hnat0 := (concCubeIso n).hom.naturality g
  rw [concCubeIso_hom_app] at hnat0
  have hnat : (Conc (□n)).map g ≫ eqToHom (congrArg strands (Nev_cube x))
      = eqToHom (congrArg strands (Nev_cube x)) ≫ braidHom (concBraid g) := hnat0
  rw [eqToHom_comp_braidHom (Nev_cube x)] at hnat
  exact (cancel_mono (eqToHom (congrArg strands (Nev_cube x)))).mp hnat

/-! ## The theorem -/

/-- **Fullness onto the pure braids.**  Every pure braid is realised by a loop of executions of the
`n`-cube, at any execution. -/
theorem conc_full_pureBraid (x : Ch⋆ (□n)) {b : Braid n} (hb : b ∈ PureBraid n) :
    ∃ g : mk x ⟶ mk x, (Conc (□n)).map g = braidHom (braidTransport (Nev_cube x).symm b) := by
  obtain ⟨g, hg⟩ := pureBraid_le_concImage x hb
  exact ⟨g, by rw [conc_map_loop, hg]⟩

/-- **Purity.**  Conversely, a loop of executions realises only pure braids. -/
theorem conc_loop_mem_pureBraid {x : Ch⋆ (□n)} (g : mk x ⟶ mk x) :
    ∃ b ∈ PureBraid n, (Conc (□n)).map g = braidHom (braidTransport (Nev_cube x).symm b) :=
  ⟨concBraid g, concBraid_loop_perm g, conc_map_loop g⟩

/-- **The image of `Aut(x)` under `Conc (□ⁿ)` is exactly the pure braid group.** -/
theorem conc_loop_iff (x : Ch⋆ (□n)) (b : Braid n) :
    (∃ g : mk x ⟶ mk x, (Conc (□n)).map g = braidHom (braidTransport (Nev_cube x).symm b))
      ↔ b ∈ PureBraid n := by
  refine ⟨fun ⟨g, hg⟩ => ?_, conc_full_pureBraid x⟩
  rw [conc_map_loop] at hg
  obtain rfl : b = concBraid g :=
    (braidTransport_injective _ (braidHom_injective hg)).symm
  exact concBraid_loop_perm g

end CubeChains
