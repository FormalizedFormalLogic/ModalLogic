module

public import ModalLogicArchive.Propositional.Entailment.Corsi.VF

@[expose] public section

namespace LO.Propositional

namespace Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

protected class WF (𝓢 : S) extends
  -- Axioms
  Entailment.HasAxiomAndElim 𝓢,
  Entailment.HasAxiomOrInst 𝓢,
  Entailment.HasDistributeAndOr 𝓢,
  Entailment.HasImpId 𝓢,
  Entailment.HasAxiomVerum 𝓢,
  Entailment.HasAxiomEFQ 𝓢,
  -- Rule
  Entailment.ModusPonens 𝓢,
  Entailment.AFortiori 𝓢,
  Entailment.AndIntroRule 𝓢,
  Entailment.RuleC 𝓢,
  Entailment.RuleD 𝓢,
  Entailment.RuleI 𝓢,
  Entailment.RuleE 𝓢

-- TODO: unify old
namespace Corsi

end Corsi



end Entailment


end LO.Propositional

end
