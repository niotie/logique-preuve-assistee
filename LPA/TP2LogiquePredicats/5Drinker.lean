import LPA.TP1LogiqueProp
import LPA.TP2LogiquePredicats.«4QuantifierNegation»

namespace LPA

variable {α : Type}     -- un type d'éléments
variable {dans_le_bar boit : α → Prop}

theorem buveur (h : ∃ x, dans_le_bar x):
    ∃ x, (dans_le_bar x ∧ boit x → ∀ y, dans_le_bar y → boit y) := by
  sorry
