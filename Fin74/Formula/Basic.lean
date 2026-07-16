module

public import Foundation.Vorspiel.Set.Basic

@[expose]
public section

variable {α : Type*}

/-- Formulas over primitives `⊥`, `🡒`, `◇` (following [Fin74]), with `□` a derived
connective. Fewer modal primitives keep structural induction (e.g. for `subst`, or the
"modal decomposition" lemma used in the pigeonhole argument of [Fin74]) to a single
modal case. -/
inductive Formula (α : Type*)
| atom : α → Formula α
| bot  : Formula α
| imp  : Formula α → Formula α → Formula α
| dia  : Formula α → Formula α
deriving DecidableEq

namespace Formula

variable {A B : Formula α}

prefix:100 "#" => atom
notation:max "⊥" => bot
infixr:64 " 🡒 " => imp
prefix:95 "◇" => dia

@[match_pattern]
abbrev neg (A : Formula α) : Formula α := A 🡒 ⊥
prefix:90 "∼" => neg

@[match_pattern]
abbrev or (A B : Formula α) : Formula α := ∼A 🡒 B
infixl:68 " ⋎ " => or

@[match_pattern]
abbrev and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
infixl:72 " ⋏ " => and

@[match_pattern]
abbrev iff (A B : Formula α) : Formula α := (A 🡒 B) ⋏ (B 🡒 A)
infix:58 " 🡘 " => iff

@[match_pattern]
abbrev top : Formula α := ∼⊥
notation:max "⊤" => top

@[match_pattern]
abbrev box (A : Formula α) : Formula α := ∼◇(∼A)
prefix:95 "□" => box

end Formula

end
