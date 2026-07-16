import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.Group

/-!
# Foundations/ShortFive — the short five lemma for groups (non-abelian)

`Grp` is not abelian, so mathlib's abelian four/five lemma does not apply, and its `MulExact`
ladder lemma (`mulExact_iff_of_surjective_of_bijective_of_injective`) secretly requires
`CommMonoid`.  But the **short five lemma** — in a ladder of two short exact sequences of groups,
outer verticals iso forces the middle vertical iso — holds for arbitrary groups.

Here it is, as an elementary diagram chase, exactness in the `ker = range` form.

```
    A  --ι-->  B  --π-->  C          (top)    ker π = range ι,  π surjective
    |f         |g         |h
    A' --ι'--> B' --π'--> C'         (bottom) ker π' = range ι', ι' injective
```
-/

namespace ShortFive

open Function MonoidHom

variable {A B C A' B' C' : Type*}
  [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
  {ι : A →* B} {π : B →* C} {ι' : A' →* B'} {π' : B' →* C'}
  {f : A →* A'} {g : B →* B'} {h : C →* C'}

/-- **Injectivity of the middle map.**  Needs the top row exact at `B`, `ι'` and `h` injective, and
`f` injective. -/
theorem injective_middle
    (commL : ∀ a, g (ι a) = ι' (f a)) (commR : ∀ b, π' (g b) = h (π b))
    (hTop : π.ker = ι.range) (hf : Injective f) (hι' : Injective ι') (hh : Injective h) :
    Injective g := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hπb : π b = 1 := hh (by rw [← commR, hb, map_one, map_one])
  obtain ⟨a, rfl⟩ := mem_range.mp (hTop ▸ mem_ker.mpr hπb)
  have hfa : f a = 1 := hι' (by rw [← commL, hb, map_one])
  have ha1 : a = 1 := hf (show f a = f 1 by rw [hfa, map_one])
  rw [ha1, map_one]

/-- **Surjectivity of the middle map.**  Needs the bottom row exact at `B'`, `π` and `h`
surjective, and `f` surjective. -/
theorem surjective_middle
    (commL : ∀ a, g (ι a) = ι' (f a)) (commR : ∀ b, π' (g b) = h (π b))
    (hBot : π'.ker = ι'.range) (hf : Surjective f) (hπ : Surjective π) (hh : Surjective h) :
    Surjective g := by
  intro b'
  obtain ⟨c, hc⟩ := hh (π' b')
  obtain ⟨b, rfl⟩ := hπ c
  have hpg : π' (g b) = π' b' := by rw [commR, hc]
  obtain ⟨a', ha'⟩ := mem_range.mp (hBot ▸ mem_ker.mpr
    (show π' (g b * b'⁻¹) = 1 by rw [map_mul, map_inv, hpg, mul_inv_cancel]))
  obtain ⟨a, rfl⟩ := hf a'
  exact ⟨(ι a)⁻¹ * b, by rw [map_mul, map_inv, commL, ha']; group⟩

/-- **The short five lemma.**  Outer verticals iso ⟹ middle vertical iso. -/
theorem bijective_middle
    (commL : ∀ a, g (ι a) = ι' (f a)) (commR : ∀ b, π' (g b) = h (π b))
    (hTop : π.ker = ι.range) (hBot : π'.ker = ι'.range)
    (hπ : Surjective π) (hι' : Injective ι')
    (hf : Bijective f) (hh : Bijective h) : Bijective g :=
  ⟨injective_middle commL commR hTop hf.1 hι' hh.1,
   surjective_middle commL commR hBot hf.2 hπ hh.2⟩

end ShortFive
