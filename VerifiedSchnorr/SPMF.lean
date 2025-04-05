import Mathlib

noncomputable section

open NNReal ENNReal MeasureTheory

def SPMF.{u} (α : Type u) : Type u :=
  { f : α → ℝ≥0∞ // ∃ h < 1, HasSum f h }

namespace SPMF

instance instFunLike : FunLike (SPMF α) α ℝ≥0∞ where
  coe p a := p.val a
  coe_injective' _ _ h := Subtype.eq h

@[ext]
protected theorem ext {p q : SPMF α} (h : ∀ x, p x = q x) : p = q :=
  DFunLike.ext p q h

-- theorem hasSum_coe_one (p : SPMF α) : HasSum p 1 :=
--   p.2

-- @[simp]
-- theorem tsum_coe (p : SPMF α) : ∑' a, p a = 1 :=
--   p.hasSum_coe_one.tsum_eq

theorem tsum_coe_ne_top (p : SPMF α) : ∑' a, p a ≠ ∞ := sorry
  -- p.tsum_coe.symm ▸ ENNReal.one_ne_top

theorem tsum_coe_indicator_ne_top (p : SPMF α) (s : Set α) : ∑' a, s.indicator p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl) ENNReal.summable
      ENNReal.summable)
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

-- @[simp]
-- theorem coe_ne_zero (p : SPMF α) : ⇑p ≠ 0 := fun hp =>
--   zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)

/-- The support of a `PMF` is the set where it is nonzero. -/
def support (p : SPMF α) : Set α :=
  Function.support p

@[simp]
theorem mem_support_iff (p : SPMF α) (a : α) : a ∈ p.support ↔ p a ≠ 0 := Iff.rfl

-- @[simp]
-- theorem support_nonempty (p : SPMF α) : p.support.Nonempty :=
--   Function.support_nonempty_iff.2 p.coe_ne_zero

@[simp]
theorem support_countable (p : SPMF α) : p.support.Countable := sorry
  -- Summable.countable_support_ennreal (tsum_coe_ne_top p)

theorem apply_eq_zero_iff (p : SPMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff, Classical.not_not]

theorem apply_pos_iff (p : SPMF α) (a : α) : 0 < p a ↔ a ∈ p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

theorem apply_eq_one_iff (p : SPMF α) (a : α) : p a = 1 ↔ p.support = {a} := by sorry
  -- refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
  --   fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one <| ha.symm.trans h,
  --   fun h => _root_.trans (symm <| tsum_eq_single a
  --     fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  -- suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  -- classical
  -- have : 0 < ∑' b, ite (b = a) 0 (p b) := lt_of_le_of_ne' zero_le'
  --   ((tsum_ne_zero_iff ENNReal.summable).2
  --     ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm <| (p.mem_support_iff a').2 ha'⟩⟩)
  -- calc
  --   1 = 1 + 0 := (add_zero 1).symm
  --   _ < p a + ∑' b, ite (b = a) 0 (p b) :=
  --     (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
  --   _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
  --   _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
  --     congr
  --     exact symm (tsum_eq_single a fun b hb => if_neg hb)
  --   _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
  --   _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero, le_rfl]

theorem coe_le_one (p : SPMF α) (a : α) : p a ≤ 1 := by sorry
  -- classical
  -- refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  -- split_ifs with h <;> simp only [h, zero_le', le_rfl]

theorem apply_ne_top (p : SPMF α) (a : α) : p a ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

theorem apply_lt_top (p : SPMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

