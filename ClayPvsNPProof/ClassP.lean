import ClayPvsNP
import ClayPvsNPProof.ATK.LigacaoPNP

/-!
# A classe `P` fixada é a classe `classeP` do ATK

O kernel ATK (`ATK/LigacaoPNP.lean`, portado em `ClayPvsNPProof.ATK.LigacaoPNP`) define
`EmP L := ∃ χ, (∀ w, w ∈ L ↔ χ w = true) ∧ Nonempty (TM2ComputableInPolyTime cod encodeBool χ)`
com `cod = id` e `encodeBool b = [b]`. É o `ClayPvsNP.InP` fixado com as duas conjunções trocadas;
os dados de máquina são definicionalmente os mesmos.

É uma equivalência de definições. Não decide P vs NP.
-/

namespace ClayPvsNPProof

open Turing Computability ClayPvsNPProof.ATK.LigacaoPNP

/-- O predicado de tempo polinomial fixado é o do ATK (`cod = id`, `encodeBool b = [b]`). -/
theorem polyTimeComputable_iff (f : ClayPvsNP.Word → Bool) :
    ClayPvsNP.PolyTimeComputable f ↔ Nonempty (TM2ComputableInPolyTime cod encodeBool f) :=
  Iff.rfl

/-- `L ∈ P` (fixado) se e somente se `L ∈ P` (ATK). -/
theorem inP_iff_emP (L : ClayPvsNP.Language) : ClayPvsNP.InP L ↔ EmP L := by
  unfold ClayPvsNP.InP EmP
  exact exists_congr fun χ => by rw [polyTimeComputable_iff, and_comm]

/-- **A classe `P` fixada é igual à classe `classeP` do ATK.** -/
theorem P_eq_classeP : ClayPvsNP.P = classeP := by
  ext L
  exact inP_iff_emP L

end ClayPvsNPProof
