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

end section

structure ComputationalCipher where
  keyType : Type
  messageType : Type
  cipherType : Type
  [hk : Finite keyType]
  [hm : Finite messageType]
  [hc : Finite cipherType]
  encrypt : keyType → messageType → cipherType
  decrypt : keyType → cipherType → messageType
  decrypt_encrypt {k : keyType} {m : messageType} : decrypt k (encrypt k m) = m
