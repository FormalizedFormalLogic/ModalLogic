module

public import ModalLogicArchive.Modal.Entailment.Basic

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

protected class K4Hen (𝓢 : S) extends Entailment.K4 𝓢, HasAxiomHen 𝓢

namespace K4Hen

variable [Entailment.K4Hen 𝓢]

instance : HenkinRule 𝓢 where
  henkin h := (K_left h) ⨀ (axiomHen ⨀ nec h);

end K4Hen

end Entailment

end LO.Modal

end
