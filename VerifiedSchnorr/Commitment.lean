import VerifiedSchnorr.Util

noncomputable section

local instance {α : Type _} [Finite α] : Fintype α := Fintype.ofFinite α

/-! ## Commitment Schemes -/

/-- A commitment scheme with message, randomness, and commitment types. -/
structure CommitmentScheme where
  messageType : Type
  randomType : Type
  commitType : Type
  [hr : Finite randomType]
  [hrne : Nonempty randomType]
  commit : messageType → randomType → commitType

attribute [instance] CommitmentScheme.hr CommitmentScheme.hrne

/-- The commitment distribution: commit to message `m` with uniform randomness. -/
noncomputable def CommitDistribution (C : CommitmentScheme) [Finite C.commitType]
    [Nonempty C.commitType] (m : C.messageType) : PMF C.commitType := do
  let r ← PMF.uniformOfFinite C.randomType
  return C.commit m r

/-- A commitment scheme is perfectly hiding if the commitment distribution
    is independent of the message. -/
def PerfectlyHiding (C : CommitmentScheme) [Finite C.commitType] [Nonempty C.commitType] :=
  ∀ (m₀ m₁ : C.messageType), ∀ (c : C.commitType),
    CommitDistribution C m₀ c = CommitDistribution C m₁ c

/-- XOR commitment: commit(m, r) = m ⊕ r. This is essentially OTP. -/
def XORCommitment (w : ℕ) : CommitmentScheme := {
  messageType := BitVec w
  randomType := BitVec w
  commitType := BitVec w
  commit := BitVec.xor
}

instance {w : ℕ} : Finite (XORCommitment w |>.commitType) := by
  unfold XORCommitment; infer_instance

instance {w : ℕ} : Nonempty (XORCommitment w |>.commitType) := by
  unfold XORCommitment; infer_instance

private lemma BitVec.xor_map_uniform {w : ℕ} (m : BitVec w) :
    PMF.map (fun a => m ^^^ a) (PMF.uniformOfFintype (BitVec w))
      = PMF.uniformOfFintype (BitVec w) := by
  ext x
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  simp_rw [show ∀ a, (x = m ^^^ a) = (a = m ^^^ x) from fun a => propext
    ⟨fun h => by rw [h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor],
     fun h => by rw [h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]⟩]
  rw [tsum_ite_eq]

theorem XORCommitment_PerfectlyHiding {w : ℕ} :
    PerfectlyHiding (XORCommitment w) := by
  intro m₀ m₁ c
  show CommitDistribution (XORCommitment w) m₀ c = CommitDistribution (XORCommitment w) m₁ c
  unfold CommitDistribution XORCommitment
  dsimp only
  simp only [BitVec.xor_eq, bind_pure_comp, PMF.monad_map_eq_map, PMF.uniformOfFinite,
    BitVec.xor_map_uniform]
