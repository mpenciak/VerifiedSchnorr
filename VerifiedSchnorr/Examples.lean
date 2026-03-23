import Mathlib

noncomputable section

-- abbrev 𝔽 (p : ℕ) [Fact p.Prime] (n : ℕ) := GaloisField p n

local instance {α : Type _} [Finite α] : Fintype α := Fintype.ofFinite α

def PMF.uniformOfFinite (α : Type _) [Nonempty α] [Finite α] : PMF α := PMF.uniformOfFintype α

instance {w} : Finite (BitVec w) := .intro (by
  refine ⟨BitVec.toFin, BitVec.ofFin, ?_, ?_⟩
  · intro; rfl
  · intro; rfl)

structure ShannonCipher where
  keyType : Type
  messageType : Type
  cipherType : Type
  encrypt : keyType → messageType → cipherType
  decrypt : keyType → cipherType → messageType
  decrypt_encrypt {k : keyType} {m : messageType} : decrypt k (encrypt k m) = m

def BitVecOTP (w : ℕ) : ShannonCipher := {
  keyType := BitVec w,
  messageType := BitVec w,
  cipherType := BitVec w,
  encrypt := BitVec.xor
  decrypt := BitVec.xor
  decrypt_encrypt := by
    intros
    rw [BitVec.xor_eq, BitVec.xor_eq, ←BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
}

instance {w : ℕ} : Finite (BitVecOTP w |>.keyType) := by
  unfold BitVecOTP
  infer_instance

instance {w : ℕ} : Nonempty (BitVecOTP w |>.keyType) := by
  unfold BitVecOTP
  infer_instance

instance {w : ℕ} : Finite (BitVecOTP w |>.cipherType) := by
  unfold BitVecOTP
  infer_instance

instance {w : ℕ} : Nonempty (BitVecOTP w |>.cipherType) := by
  unfold BitVecOTP
  infer_instance

def PerfectSecurityGame (E : ShannonCipher) [Finite E.keyType] [Nonempty E.keyType] (m : E.messageType) :
    PMF E.cipherType := do
  let k ← PMF.uniformOfFinite E.keyType
  return E.encrypt k m

def PerfectSecurity (E : ShannonCipher) [Finite E.keyType] [Nonempty E.keyType] :=
  ∀(m₀ m₁ : E.messageType), ∀(c : E.cipherType),
  let p₀ := PerfectSecurityGame E m₀
  let p₁ := PerfectSecurityGame E m₁
  p₀ c = p₁ c

lemma BitVecOTP_PerfectSecurityGame_uniform {w : ℕ} :
    ∀(m : BitVec w),
      PerfectSecurityGame (BitVecOTP w) m = PMF.uniformOfFinite (BitVecOTP w |>.cipherType) := by
  intros m
  unfold PerfectSecurityGame
  unfold BitVecOTP
  simp only [BitVec.xor_eq, bind_pure_comp]
  ext x
  unfold PMF.uniformOfFinite
  have : ∀(a : BitVec w), x = a ^^^ m ↔ a = x ^^^ m := by
    intros a
    constructor <;> intro ha <;> rw [ha, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  simp [PMF.monad_map_eq_map, this]

theorem BitVecOTP_PerfectSecurity {w : ℕ} : PerfectSecurity (BitVecOTP w) := by
  unfold PerfectSecurity
  simp only [BitVecOTP_PerfectSecurityGame_uniform, implies_true]

structure ComputationalCipher where
  keyType : Type
  messageType : Type
  cipherType : Type
  [hk : Finite keyType]
  [hkne : Nonempty keyType]
  [hm : Finite messageType]
  [hc : Finite cipherType]
  [hcne : Nonempty cipherType]
  encrypt : keyType → messageType → cipherType
  decrypt : keyType → cipherType → messageType
  decrypt_encrypt {k : keyType} {m : messageType} : decrypt k (encrypt k m) = m

attribute [instance] ComputationalCipher.hk ComputationalCipher.hkne
  ComputationalCipher.hm ComputationalCipher.hc ComputationalCipher.hcne

/-- A Shannon cipher with finite types is a computational cipher. -/
def ShannonCipher.toComputationalCipher (E : ShannonCipher)
    [Finite E.keyType] [Nonempty E.keyType]
    [Finite E.messageType]
    [Finite E.cipherType] [Nonempty E.cipherType] : ComputationalCipher := {
  keyType := E.keyType
  messageType := E.messageType
  cipherType := E.cipherType
  encrypt := E.encrypt
  decrypt := E.decrypt
  decrypt_encrypt := E.decrypt_encrypt
}

instance {w : ℕ} : Finite (BitVecOTP w |>.messageType) := by
  unfold BitVecOTP; infer_instance

instance {w : ℕ} : Nonempty (BitVecOTP w |>.messageType) := by
  unfold BitVecOTP; infer_instance

def BitVecComputationalCipher (w : ℕ) : ComputationalCipher :=
  (BitVecOTP w).toComputationalCipher

/-! ## IND-EAV Security -/

/-- The IND-EAV game: encrypt message `m` under a uniformly random key. -/
noncomputable def INDEAVGame (E : ComputationalCipher) (m : E.messageType) : PMF E.cipherType := do
  let k ← PMF.uniformOfFinite E.keyType
  return E.encrypt k m

/-- IND-EAV security: the ciphertext distribution is independent of the message. -/
def INDEAVSecure (E : ComputationalCipher) :=
  ∀ (m₀ m₁ : E.messageType), ∀ (c : E.cipherType),
    INDEAVGame E m₀ c = INDEAVGame E m₁ c

/-- Perfect security (as defined for Shannon ciphers) implies IND-EAV security
    when viewed as a computational cipher. -/
theorem PerfectSecurity_implies_INDEAVSecure (E : ShannonCipher)
    [Finite E.keyType] [Nonempty E.keyType]
    [Finite E.messageType]
    [Finite E.cipherType] [Nonempty E.cipherType]
    (hperf : PerfectSecurity E) :
    INDEAVSecure (E.toComputationalCipher) := by
  intro m₀ m₁ c
  exact hperf m₀ m₁ c

theorem BitVecOTP_INDEAVSecure {w : ℕ} : INDEAVSecure (BitVecComputationalCipher w) := by
  unfold BitVecComputationalCipher
  exact PerfectSecurity_implies_INDEAVSecure _ BitVecOTP_PerfectSecurity

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
