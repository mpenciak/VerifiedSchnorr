import VerifiedSchnorr.Gpow
import VerifiedSchnorr.Util
import VerifiedSchnorr.SigmaProtocol

noncomputable section

/-! ## Chaum-Pedersen Protocol -/

section ChaumPedersen

variable {G : Type} [CommGroup G] [Fintype G]
variable {q : ℕ} [Fact q.Prime]
variable (g u : G) (hordg : orderOf g = q) (hordu : orderOf u = q) (hcard : Fintype.card G = q)
include hordg hordu hcard

private instance : NeZero q := ⟨Nat.Prime.ne_zero (Fact.out)⟩

/-- The Chaum-Pedersen protocol for proving equality of discrete logarithms:
    given (g, u, h, v), prove knowledge of x such that h = g^x and v = u^x. -/
def ChaumPedersenProtocol : SigmaProtocol where
  stmtType := G × G
  witType := ZMod q
  commitType := G × G
  challType := ZMod q
  respType := ZMod q
  relation stmt x := stmt.1 = gpow g x ∧ stmt.2 = gpow u x
  verify stmt commit e z :=
    gpow g z = commit.1 * stmt.1 ^ (e.val : ℤ) ∧
    gpow u z = commit.2 * stmt.2 ^ (e.val : ℤ)

omit [Fintype G] hcard in
/-- Completeness: an honest prover with witness x can always convince the verifier. -/
theorem chaum_pedersen_complete (x e r : ZMod q) :
    let h := gpow g x
    let v := gpow u x
    let a := gpow g r
    let b := gpow u r
    let z := r + e * x
    (ChaumPedersenProtocol g u).verify (h, v) (a, b) e z := by
  constructor
  · show gpow g (r + e * x) = gpow g r * (gpow g x) ^ (e.val : ℤ)
    rw [gpow_add g hordg, show e * x = x * e from mul_comm e x, gpow_mul g hordg]
  · show gpow u (r + e * x) = gpow u r * (gpow u x) ^ (e.val : ℤ)
    rw [gpow_add u hordu, show e * x = x * e from mul_comm e x, gpow_mul u hordu]

/-- Special soundness: from two accepting transcripts with the same commitment
    but different challenges, we can extract the witness x. -/
theorem chaum_pedersen_special_soundness
    (stmt : G × G) (commit : G × G) (e₁ e₂ z₁ z₂ : ZMod q) (hne : e₁ ≠ e₂)
    (hv₁ : (ChaumPedersenProtocol g u).verify stmt commit e₁ z₁)
    (hv₂ : (ChaumPedersenProtocol g u).verify stmt commit e₂ z₂) :
    (ChaumPedersenProtocol g u).relation stmt ((z₁ - z₂) * (e₁ - e₂)⁻¹) := by
  simp only [ChaumPedersenProtocol] at *
  rcases hv₁ with ⟨hv1g, hv1u⟩
  rcases hv₂ with ⟨hv2g, hv2u⟩
  
  -- Extraction for the first base g
  have hg1 : g ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at hordg
    have := (Fact.out : q.Prime).two_le; omega
  have hnat : Nat.card G = q := Nat.card_eq_fintype_card.trans hcard
  obtain ⟨k1, hk1⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card hnat hg1 : stmt.1 ∈ Subgroup.zpowers g)
  set w1 : ZMod q := (k1 : ZMod q)
  have hw1 : stmt.1 = gpow g w1 := by
    simp only [gpow, w1]
    rw [show ((k1 : ZMod q).val : ℤ) = k1 % (q : ℤ) from ZMod.val_intCast k1,
      show (q : ℤ) = (orderOf g : ℤ) from by exact_mod_cast hordg.symm,
      zpow_mod_orderOf, hk1]
  
  have hweq1 : gpow g (z₁ - z₂) = gpow g (w1 * (e₁ - e₂)) := by
    rw [gpow_sub g hordg, hv1g, hv2g, hw1, ← gpow_mul g hordg, ← gpow_mul g hordg,
      show w1 * (e₁ - e₂) = w1 * e₁ - w1 * e₂ from by ring, gpow_sub g hordg]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _
  
  have hinj1 := gpow_injective g hordg hweq1
  have hw1_val : w1 = (z₁ - z₂) * (e₁ - e₂)⁻¹ := by
    rw [hinj1, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), mul_one]

  -- Extraction for the second base u
  have hu1 : u ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at hordu
    have := (Fact.out : q.Prime).two_le; omega
  obtain ⟨k2, hk2⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card hnat hu1 : stmt.2 ∈ Subgroup.zpowers u)
  set w2 : ZMod q := (k2 : ZMod q)
  have hw2 : stmt.2 = gpow u w2 := by
    simp only [gpow, w2]
    rw [show ((k2 : ZMod q).val : ℤ) = k2 % (q : ℤ) from ZMod.val_intCast k2,
      show (q : ℤ) = (orderOf u : ℤ) from by exact_mod_cast hordu.symm,
      zpow_mod_orderOf, hk2]
  
  have hweq2 : gpow u (z₁ - z₂) = gpow u (w2 * (e₁ - e₂)) := by
    rw [gpow_sub u hordu, hv1u, hv2u, hw2, ← gpow_mul u hordu, ← gpow_mul u hordu,
      show w2 * (e₁ - e₂) = w2 * e₁ - w2 * e₂ from by ring, gpow_sub u hordu]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _
  
  have hinj2 := gpow_injective u hordu hweq2
  have hw2_val : w2 = (z₁ - z₂) * (e₁ - e₂)⁻¹ := by
    rw [hinj2, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), mul_one]

  -- Final result: both witnesses are the same extracted value
  constructor
  · rw [hw1, hw1_val]
  · rw [hw2, hw2_val]

omit [Fintype G] hcard in
/-- Honest-Verifier Zero-Knowledge: real transcripts and simulated transcripts 
    are identically distributed. -/
theorem chaum_pedersen_hvzk (stmt : G × G) (x e : ZMod q) (hx : (ChaumPedersenProtocol g u).relation stmt x) :
    let realTranscript := do
      let r ← PMF.uniformOfFintype (ZMod q)
      return (gpow g r, gpow u r, r + e * x)
    let simulator := do
      let z ← PMF.uniformOfFintype (ZMod q)
      return (gpow g z * (stmt.1 ^ (e.val : ℤ))⁻¹, gpow u z * (stmt.2 ^ (e.val : ℤ))⁻¹, z)
    realTranscript = simulator := by
  simp only [ChaumPedersenProtocol] at *
  -- Rewrite uniform in simulator via the bijection z ↦ z + e * x
  conv_rhs =>
    rw [show PMF.uniformOfFintype (ZMod q) =
      PMF.map (· + e * x) (PMF.uniformOfFintype (ZMod q))
      from (add_const_map_uniform (e * x)).symm]
  change PMF.bind _ _ = PMF.bind _ _
  rw [PMF.bind_map]
  congr 1; ext r; simp only [Function.comp]; congr 1
  -- Use hx : stmt.1 = g^x and stmt.2 = u^x
  rcases hx with ⟨hx1, hx2⟩
  simp only [hx1, hx2, gpow_add g hordg, gpow_add u hordu, show e * x = x * e from mul_comm e x, 
    gpow_mul g hordg, gpow_mul u hordu, mul_assoc, mul_inv_cancel, mul_one]

end ChaumPedersen
