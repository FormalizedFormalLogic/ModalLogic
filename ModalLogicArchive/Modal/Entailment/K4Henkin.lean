module

public import ModalLogicArchive.Modal.Entailment.Basic

@[expose] public section

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

namespace Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

protected class K4Henkin (𝓢 : S) extends Entailment.K4 𝓢, HenkinRule 𝓢

namespace K4Henkin

variable [Entailment.K4Henkin 𝓢]

instance : LoebRule 𝓢 where
  loeb h := h ⨀ (henkin $ E_intro (axiomK' $ nec h) axiomFour);

end K4Henkin

end Entailment

end LO.Modal

end
