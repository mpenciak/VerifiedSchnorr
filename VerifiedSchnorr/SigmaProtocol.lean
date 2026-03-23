import Mathlib

/-! ## Sigma Protocols -/

/-- A sigma protocol (3-move interactive proof). -/
structure SigmaProtocol where
  stmtType : Type
  witType : Type
  commitType : Type
  challType : Type
  respType : Type
  [hch : Fintype challType]
  [hchne : Nonempty challType]
  relation : stmtType → witType → Prop
  verify : stmtType → commitType → challType → respType → Prop

attribute [instance] SigmaProtocol.hch SigmaProtocol.hchne
