import Mathlib

/-! ## Group Exponentiation via ZMod -/

section GpowInfra

variable {G : Type} [Group G] {q : ℕ} [NeZero q]

/-- Exponentiate a group element by a `ZMod q` value, using integer zpow. -/
def gpow (g : G) (z : ZMod q) : G := g ^ (z.val : ℤ)

omit [NeZero q] in
private lemma zpow_val_mod (g : G) (hord : orderOf g = q) (n : ℕ) :
    g ^ ((n % q : ℕ) : ℤ) = g ^ (n : ℤ) := by
  rw [zpow_natCast, zpow_natCast,
    show n % q = n % orderOf g from by rw [hord], pow_mod_orderOf]

lemma gpow_add (g : G) (hord : orderOf g = q) (a b : ZMod q) :
    gpow g (a + b) = gpow g a * gpow g b := by
  simp only [gpow, ZMod.val_add]
  rw [zpow_val_mod g hord, zpow_natCast, zpow_natCast, zpow_natCast, pow_add]

omit [NeZero q] in
lemma gpow_zero (g : G) : gpow g (0 : ZMod q) = 1 := by
  simp [gpow, ZMod.val_zero]

lemma gpow_neg (g : G) (hord : orderOf g = q) (a : ZMod q) :
    gpow g (-a) = (gpow g a)⁻¹ := by
  apply mul_left_cancel (a := gpow g a)
  rw [← gpow_add g hord, add_neg_cancel, gpow_zero, mul_inv_cancel]

lemma gpow_sub (g : G) (hord : orderOf g = q) (a b : ZMod q) :
    gpow g (a - b) = gpow g a * (gpow g b)⁻¹ := by
  rw [sub_eq_add_neg, gpow_add g hord, gpow_neg g hord]

omit [NeZero q] in
lemma gpow_mul (g : G) (hord : orderOf g = q) (a b : ZMod q) :
    gpow g (a * b) = (gpow g a) ^ (b.val : ℤ) := by
  simp only [gpow, ZMod.val_mul]
  rw [zpow_val_mod g hord, zpow_natCast, zpow_natCast, zpow_natCast, pow_mul]

lemma gpow_injective (g : G) (hord : orderOf g = q) [Fact q.Prime] :
    Function.Injective (gpow g : ZMod q → G) := by
  intro a b hab
  simp only [gpow] at hab
  have hmod := (zpow_eq_zpow_iff_modEq (G := G)).mp hab
  rw [Int.ModEq, hord] at hmod
  have hav : (a.val : ℤ) % q = a.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast ZMod.val_lt a)
  have hbv : (b.val : ℤ) % q = b.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast ZMod.val_lt b)
  have : a.val = b.val := by exact_mod_cast hav.symm.trans (hmod.trans hbv)
  exact (ZMod.val_injective q) this

lemma gpow_surjective [Fintype G] (g : G) (hord : orderOf g = q) [Fact q.Prime]
    (hcard : Fintype.card G = q) :
    Function.Surjective (gpow g : ZMod q → G) :=
  (gpow_injective g hord).surjective_of_finite
    (Fintype.equivOfCardEq (show Fintype.card (ZMod q) = Fintype.card G by
      rw [ZMod.card, hcard]))

lemma gpow_bijective [Fintype G] (g : G) (hord : orderOf g = q) [Fact q.Prime]
    (hcard : Fintype.card G = q) :
    Function.Bijective (gpow g : ZMod q → G) :=
  ⟨gpow_injective g hord, gpow_surjective g hord hcard⟩

noncomputable def gpow_equiv [Fintype G] (g : G) (hord : orderOf g = q) [Fact q.Prime]
    (hcard : Fintype.card G = q) : ZMod q ≃ G :=
  Equiv.ofBijective (gpow g) (gpow_bijective g hord hcard)

end GpowInfra
