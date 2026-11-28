/-! Equations 677 and 255 of the Equational Theories Project, for a binary operation `⋆`. -/

section
variable {α : Type} (op : α → α → α)
local infixl:70 " ⋆ " => op

def Eq677 : Prop := ∀ x y, x = y ⋆ (x ⋆ ((y ⋆ x) ⋆ y))
def Eq255 : Prop := ∀ x, x = ((x ⋆ x) ⋆ x) ⋆ x
end
