import Mathlib

noncomputable section

local instance {α : Type _} [Finite α] : Fintype α := Fintype.ofFinite α

def PMF.uniformOfFinite (α : Type _) [Nonempty α] [Finite α] : PMF α := PMF.uniformOfFintype α

instance {w} : Finite (BitVec w) := .intro (by
  refine ⟨BitVec.toFin, BitVec.ofFin, ?_, ?_⟩
  · intro; rfl
  · intro; rfl)

/-! ## Uniform Distribution Helpers -/

lemma PMF.uniformOfFintype_map_equiv {α β : Type} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFintype α) = PMF.uniformOfFintype β := by
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  classical
  rw [tsum_congr fun a => if_congr
    (show b = e a ↔ a = e.symm b from
      ⟨fun h => by rw [← e.symm_apply_apply a, h], fun h => by rw [h, e.apply_symm_apply]⟩)
    rfl rfl, tsum_ite_eq, Fintype.card_congr e]

lemma PMF.uniformOfFinite_map_equiv {α β : Type} [Finite α] [Finite β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    PMF.map e (PMF.uniformOfFinite α) = PMF.uniformOfFinite β :=
  PMF.uniformOfFintype_map_equiv e

lemma add_const_map_uniform {α : Type} [AddGroup α] [Fintype α] (c : α) :
    PMF.map (· + c) (PMF.uniformOfFintype α) = PMF.uniformOfFintype α := by
  ext x
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  classical
  rw [tsum_congr fun a => if_congr
    (show x = a + c ↔ a = x - c from
      ⟨fun h => by rw [h, add_sub_cancel_right], fun h => by rw [h, sub_add_cancel]⟩)
    rfl rfl, tsum_ite_eq]
