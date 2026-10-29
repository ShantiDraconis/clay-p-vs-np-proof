import ClayPvsNPProof.ClassP
import ClayPvsNPProof.Transcoders

/-!
# A classe `NP` fixada é a classe `classeNP` do ATK, e `P ⊆ NP` no modelo fixado

As duas definições de NP diferem só na codificação de pares: o enunciado fixado usa
`ClayPvsNP.pair w c = (w.flatMap fun b => [true, b]) ++ false :: c` e o ATK usa
`par w c = (w.flatMap fun b => [b, b]) ++ [false, true] ++ c`. Os transcodificadores de
`ClayPvsNPProof.Transcoders` (máquinas `FinTM2` de tempo linear) convertem uma na outra, e P é
fechada por reduções de Karp computadas por `FinTM2` (`ATK.ModeloPNP.P_fechada_red`, que usa a
composição de máquinas `ATK.ComposicaoTM2.comp`). Daí:

* `NP_eq_classeNP : ClayPvsNP.NP = classeNP`;
* `P_subset_NP : ClayPvsNP.P ⊆ ClayPvsNP.NP` (porte de `ATK.ModeloPNP.P_sub_NP`).

São teoremas sobre as definições. Não decidem P vs NP.
-/

namespace ClayPvsNPProof

open Turing Computability ClayPvsNPProof.ATK.LigacaoPNP ClayPvsNPProof.ATK.ModeloPNP
  ClayPvsNPProof.Transcoders

/-- Um verificador na codificação fixada vira um verificador na codificação do ATK. -/
theorem verificador_ATK {V : ClayPvsNP.Language} (hV : V ∈ classeP) :
    {x | tP x ∈ V} ∈ classeP :=
  P_fechada_red ⟨tP, fun _ => Iff.rfl, ⟨tPComputable⟩⟩ hV

/-- Um verificador na codificação do ATK vira um verificador na codificação fixada. -/
theorem verificador_fixado {V : Linguagem} (hV : V ∈ classeP) :
    {x | tA x ∈ V} ∈ classeP :=
  P_fechada_red ⟨tA, fun _ => Iff.rfl, ⟨tAComputable⟩⟩ hV

/-- `L ∈ NP` (fixado) se e somente se `L ∈ NP` (ATK). -/
theorem inNP_iff_emNP (L : ClayPvsNP.Language) : ClayPvsNP.InNP L ↔ EmNP L := by
  constructor
  · rintro ⟨V, q, hV, hL⟩
    have hV' : V ∈ classeP := (inP_iff_emP V).mp hV
    refine ⟨{x | tP x ∈ V}, verificador_ATK hV', q, fun w => ?_⟩
    rw [hL w]
    simp only [Set.mem_ofPred_eq, tP_par]
  · rintro ⟨V, hV, q, hL⟩
    refine ⟨{x | tA x ∈ V}, q, (inP_iff_emP _).mpr (verificador_fixado hV), fun w => ?_⟩
    rw [hL w]
    simp only [Set.mem_ofPred_eq, tA_pair]

/-- **A classe `NP` fixada é a classe `classeNP` do ATK.** -/
theorem NP_eq_classeNP : ClayPvsNP.NP = classeNP := by
  ext L
  exact inNP_iff_emNP L

/-- **`P ⊆ NP` no modelo fixado** (o verificador decodifica o primeiro componente do par e roda o
decisor; certificado vazio). -/
theorem P_subset_NP : ClayPvsNP.P ⊆ ClayPvsNP.NP := by
  rw [P_eq_classeP, NP_eq_classeNP]
  exact P_sub_NP

/-- `P_eq_NP` é exatamente o enunciado `classeP = classeNP` do ATK. -/
theorem P_eq_NP_iff_classes : ClayPvsNP.P_eq_NP ↔ classeP = classeNP := by
  unfold ClayPvsNP.P_eq_NP
  rw [P_eq_classeP, NP_eq_classeNP]

/-- `¬ P_eq_NP` é exatamente o enunciado `PneNP` do ATK. -/
theorem not_P_eq_NP_iff_PneNP : ¬ ClayPvsNP.P_eq_NP ↔ PneNP :=
  not_congr P_eq_NP_iff_classes

/-- `P_eq_NP ↔ NP ⊆ P` (a outra inclusão é teorema). -/
theorem P_eq_NP_iff_NP_subset_P : ClayPvsNP.P_eq_NP ↔ ClayPvsNP.NP ⊆ ClayPvsNP.P :=
  ⟨fun h => h ▸ le_rfl, fun h => Set.Subset.antisymm P_subset_NP h⟩

end ClayPvsNPProof
