import VerifiedSchnorr.Gpow
import VerifiedSchnorr.Util
import VerifiedSchnorr.Commitment

noncomputable section

/-! ## Pedersen Commitment Scheme -/

section Pedersen

variable {G : Type} [CommGroup G] [Fintype G]
variable {q : ℕ} [Fact q.Prime]
variable (g : G) (hord : orderOf g = q) (hcard : Fintype.card G = q)
include hord hcard

private instance : NeZero q := ⟨Nat.Prime.ne_zero (Fact.out)⟩

/-- The Pedersen commitment scheme: commit(m, r) = g^m * h^r. -/
def PedersenCommitment (h : G) : CommitmentScheme where
  messageType := ZMod q
  randomType := ZMod q
  commitType := G
  commit m r := gpow g m * gpow h r

/-! ### Perfectly Hiding -/

private instance pedersen_finite (h : G) : Finite (PedersenCommitment (q := q) g h).commitType :=
  inferInstanceAs (Finite G)

private instance pedersen_nonempty (h : G) :
    Nonempty (PedersenCommitment (q := q) g h).commitType :=
  inferInstanceAs (Nonempty G)

/-- The commitment distribution for any message is uniform over G. -/
private lemma pedersen_commit_uniform (h : G) (hordh : orderOf h = q) (m : ZMod q) :
    CommitDistribution (PedersenCommitment (q := q) g h) m =
    PMF.uniformOfFinite G := by
  unfold CommitDistribution PedersenCommitment
  dsimp only
  simp only [bind_pure_comp, PMF.monad_map_eq_map]
  -- The map r ↦ gpow g m * gpow h r is a bijection ZMod q → G
  have : (fun r : ZMod q => gpow g m * gpow h r) =
      (fun x => gpow g m * x) ∘ (gpow (q := q) h) := rfl
  rw [this, ← PMF.map_comp]
  have heq : (gpow (q := q) h : ZMod q → G) = (gpow_equiv h hordh hcard : ZMod q → G) := rfl
  rw [heq, PMF.map_comp]
  exact PMF.uniformOfFinite_map_equiv
    ((gpow_equiv h hordh hcard).trans (Equiv.mulLeft (gpow g m)))

/-- The Pedersen commitment scheme is perfectly hiding when h is a generator. -/
theorem pedersen_perfectlyHiding (h : G) (hordh : orderOf h = q) :
    PerfectlyHiding (PedersenCommitment (q := q) g h) := by
  intro m₀ m₁ c
  simp only [pedersen_commit_uniform g hord hcard h hordh]

/-! ### Computational Binding (DLP Extraction) -/

/-- A DLP solution: x such that g^x = h. -/
def isDLPSolution (h : G) (x : ZMod q) : Prop := gpow g x = h

/-- If an adversary can open a Pedersen commitment in two different ways,
    we can extract a discrete logarithm of h with respect to g. -/
theorem pedersen_binding_extract
    (h : G) (m₁ m₂ r₁ r₂ : ZMod q)
    (hm : m₁ ≠ m₂)
    (hopen : (PedersenCommitment (q := q) g h).commit m₁ r₁ =
             (PedersenCommitment (q := q) g h).commit m₂ r₂) :
    isDLPSolution g h ((m₁ - m₂) * (r₂ - r₁)⁻¹) := by
  simp only [PedersenCommitment, isDLPSolution] at *
  -- hopen : gpow g m₁ * gpow h r₁ = gpow g m₂ * gpow h r₂
  -- Step 1: h is a power of g
  have hg1 : g ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at hord
    have := (Fact.out : q.Prime).two_le; omega
  have hnat : Nat.card G = q := Nat.card_eq_fintype_card.trans hcard
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card hnat hg1 : h ∈ Subgroup.zpowers g)
  set w : ZMod q := (k : ZMod q)
  have hw : h = gpow g w := by
    simp only [gpow, w]
    rw [show ((k : ZMod q).val : ℤ) = k % (q : ℤ) from ZMod.val_intCast k,
      show (q : ℤ) = (orderOf g : ℤ) from by exact_mod_cast hord.symm,
      zpow_mod_orderOf, hk]
  -- Step 2: rewrite hopen using gpow
  have hopen' : gpow g (m₁ + w * r₁) = gpow g (m₂ + w * r₂) := by
    rw [gpow_add g hord, gpow_add g hord, gpow_mul g hord, gpow_mul g hord, ← hw]
    exact hopen
  have hinj := gpow_injective g hord hopen'
  -- hinj : m₁ + w * r₁ = m₂ + w * r₂
  -- Step 3: derive w = (m₁ - m₂) * (r₂ - r₁)⁻¹
  have hweq : m₁ - m₂ = w * (r₂ - r₁) := by linear_combination hinj
  suffices w = (m₁ - m₂) * (r₂ - r₁)⁻¹ by rw [← this, ← hw]
  -- r₁ ≠ r₂ (otherwise m₁ = m₂, contradicting hm)
  have hr : r₂ ≠ r₁ := by
    intro heqr; rw [heqr] at hinj
    exact hm (add_right_cancel hinj)
  rw [hweq, mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hr), mul_one]

end Pedersen
