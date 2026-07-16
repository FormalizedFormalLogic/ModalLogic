module

public import ModalLogicArchive.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.K5 𝓢]

end LO.Modal.Entailment
end
