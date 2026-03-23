import VerifiedSchnorr.Gpow
import VerifiedSchnorr.Util
import VerifiedSchnorr.SigmaProtocol

noncomputable section

/-! ## Schnorr Identification Protocol -/

section Schnorr

variable {G : Type} [CommGroup G] [Fintype G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G) (hord : orderOf g = q) (hcard : Fintype.card G = q)
include hord hcard

private instance : NeZero q := ⟨Nat.Prime.ne_zero (Fact.out)⟩

/-- The Schnorr identification protocol as a sigma protocol. -/
def SchnorrProtocol : SigmaProtocol where
  stmtType := G
  witType := ZMod q
  commitType := G
  challType := ZMod q
  respType := ZMod q
  relation h x := h = gpow g x
  verify h a e z := gpow g z = a * h ^ (e.val : ℤ)

omit [Fintype G] hcard in
/-- Completeness: honest prover always convinces honest verifier. -/
theorem schnorr_complete (x e r : ZMod q) :
    let h := gpow g x
    let a := gpow g r
    let z := r + e * x
    (SchnorrProtocol g).verify h a e z := by
  show gpow g (r + e * x) = gpow g r * (gpow g x) ^ (e.val : ℤ)
  rw [gpow_add g hord, show e * x = x * e from mul_comm e x, gpow_mul g hord]

/-- Special soundness: from two accepting transcripts with the same commitment
    but different challenges, we can extract the witness. -/
theorem schnorr_special_soundness
    (h a : G) (e₁ e₂ z₁ z₂ : ZMod q) (hne : e₁ ≠ e₂)
    (hv₁ : (SchnorrProtocol g).verify h a e₁ z₁)
    (hv₂ : (SchnorrProtocol g).verify h a e₂ z₂) :
    (SchnorrProtocol g).relation h ((z₁ - z₂) * (e₁ - e₂)⁻¹) := by
  simp only [SchnorrProtocol] at *
  -- g generates G since orderOf g = q = card G (prime)
  have hg1 : g ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at hord
    have := (Fact.out : q.Prime).two_le; omega
  have hnat : Nat.card G = q := Nat.card_eq_fintype_card.trans hcard
  -- h is a power of g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card hnat hg1 : h ∈ Subgroup.zpowers g)
  set w : ZMod q := (k : ZMod q)
  have hw : h = gpow g w := by
    simp only [gpow, w]
    rw [show ((k : ZMod q).val : ℤ) = k % (q : ℤ) from ZMod.val_intCast k,
      show (q : ℤ) = (orderOf g : ℤ) from by exact_mod_cast hord.symm,
      zpow_mod_orderOf, hk]
  -- Rewrite verification equations using gpow
  have hv₁' : gpow g z₁ = a * gpow g (w * e₁) := by
    rw [hv₁, hw, ← gpow_mul g hord]
  have hv₂' : gpow g z₂ = a * gpow g (w * e₂) := by
    rw [hv₂, hw, ← gpow_mul g hord]
  -- Derive z₁ - z₂ = w * (e₁ - e₂) via gpow_injective
  have hweq : gpow g (z₁ - z₂) = gpow g (w * (e₁ - e₂)) := by
    rw [gpow_sub g hord, hv₁', hv₂',
      show w * (e₁ - e₂) = w * e₁ - w * e₂ from by ring, gpow_sub g hord]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _
  have hinj := gpow_injective g hord hweq
  -- Extract w = (z₁ - z₂) * (e₁ - e₂)⁻¹
  suffices w = (z₁ - z₂) * (e₁ - e₂)⁻¹ by rw [hw, this]
  rw [hinj, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hne), mul_one]

/-- Real transcript: prover with witness x, given challenge e, samples r uniformly. -/
noncomputable def schnorrRealTranscript (x e : ZMod q) : PMF (G × ZMod q) := do
  let r ← PMF.uniformOfFintype (ZMod q)
  return (gpow g r, r + e * x)

/-- Simulator: without witness, given statement h and challenge e, samples z uniformly. -/
noncomputable def schnorrSimulator (h : G) (e : ZMod q) : PMF (G × ZMod q) := do
  let z ← PMF.uniformOfFintype (ZMod q)
  return (gpow g z * (h ^ (e.val : ℤ))⁻¹, z)

omit [Fintype G] hcard in
/-- HVZK: real transcripts and simulated transcripts have the same distribution. -/
theorem schnorr_hvzk (x e : ZMod q) :
    schnorrRealTranscript g x e = schnorrSimulator g (gpow g x) e := by
  simp only [schnorrRealTranscript, schnorrSimulator]
  -- Rewrite uniform in RHS via the bijection z ↦ z + e * x
  conv_rhs =>
    rw [show PMF.uniformOfFintype (ZMod q) =
      PMF.map (· + e * x) (PMF.uniformOfFintype (ZMod q))
      from (add_const_map_uniform (e * x)).symm]
  change PMF.bind _ _ = PMF.bind _ _
  rw [PMF.bind_map]
  -- Now both sides: bind uniform (fun r => pure (..., r + e * x))
  congr 1; ext r; simp only [Function.comp]; congr 1
  -- gpow g (r + e * x) * (gpow g x ^ (e.val : ℤ))⁻¹ = gpow g r
  rw [gpow_add g hord, show e * x = x * e from mul_comm e x, gpow_mul g hord,
    mul_assoc, mul_inv_cancel, mul_one]

end Schnorr
