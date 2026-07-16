module
public import ModalLogicArchive.Propositional.Entailment.Corsi.Basic
public import ModalLogicArchive.Propositional.Entailment.Corsi.F
public import ModalLogicArchive.Propositional.Entailment.Corsi.WF
public import ModalLogicArchive.Propositional.Entailment.Corsi.VF

@[expose] public section

namespace LO.Propositional.Entailment

variable {S F : Type*} [DecidableEq F] [LogicalConnective F] [Entailment S F] {𝓢 : S}

instance [Entailment.WF 𝓢] : Entailment.VF 𝓢 where

instance [Entailment.WF 𝓢] [HasAxiomC 𝓢] [HasAxiomD 𝓢] [HasAxiomI 𝓢] : Entailment.F 𝓢 where

end LO.Propositional.Entailment

end
