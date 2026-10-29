import ClayPvsNPProof.ClassNP
import ClayPvsNPProof.ATK.CookLevinNP
import ClayPvsNPProof.Main

/-!
# SAT no modelo fixado: Cook–Levin e a lacuna `Gap`

`SAT` é a linguagem binária das fórmulas CNF satisfatíveis, com a codificação do ATK
(`ATK.ModeloPNP.codCNF`: quatro símbolos de dois bits, `0 ↦ 00`, `1 ↦ 01`, fim de literal
`↦ 10`, fim de cláusula `↦ 11`; um literal é a polaridade seguida dos bits do índice em
`Nat.bits` e do fim de literal). É um `ClayPvsNP.Language`, ou seja, uma linguagem sobre o
mesmo alfabeto `{0,1}` do enunciado fixado.

Teoremas (todos sobre as classes FIXADAS `ClayPvsNP.P`, `ClayPvsNP.NP`):

* `SAT_mem_NP : SAT ∈ ClayPvsNP.NP` (porte de `ATK.SATemNP.sat_em_NP`);
* `SAT_NP_hard : ∀ L ∈ ClayPvsNP.NP, KarpRed L SAT` (Cook 1971 / Levin 1973; porte de
  `ATK.CookLevinNP.red_SAT`, compilador verificado de laços para `FinTM2`);
* `P_closed_KarpRed`: `ClayPvsNP.P` é fechada por reduções de Karp;
* `P_eq_NP_iff_SAT_mem_P : ClayPvsNP.P_eq_NP ↔ SAT ∈ ClayPvsNP.P`
  (porte de `ATK.ZeroClasses.Pontes.p_eq_np_iff_sat`);
* `Gap : Prop := SAT ∉ ClayPvsNP.P` e `not_P_eq_NP_iff_Gap : ¬ ClayPvsNP.P_eq_NP ↔ Gap`.

`Gap` é o problema em aberto, reescrito: nada aqui o prova nem o refuta. `OPEN_MATH = true`.
-/

namespace ClayPvsNPProof

open Turing Computability ClayPvsNPProof.ATK.LigacaoPNP ClayPvsNPProof.ATK.ModeloPNP

/-- **SAT** como linguagem binária: as codificações `codCNF φ` das fórmulas CNF `φ`
satisfatíveis (é, por definição, `ATK.ModeloPNP.SAT`). -/
def SAT : ClayPvsNP.Language :=
  {x | ∃ φ : CNF, codCNF φ = x ∧ Satisfativel φ}

theorem SAT_eq_ATK : SAT = ClayPvsNPProof.ATK.ModeloPNP.SAT := rfl

/-- Sanidade: a fórmula vazia (palavra vazia) está em SAT. -/
theorem nil_mem_SAT : ([] : ClayPvsNP.Word) ∈ SAT :=
  ⟨[], rfl, ⟨fun _ => false, by simp [Satisfaz]⟩⟩

/-- Sanidade: a fórmula `x₀` (palavra `01 10 11`: polaridade positiva, índice `0` sem bits, fim de
literal, fim de cláusula) está em SAT. -/
theorem x0_mem_SAT : [false, true, true, false, true, true] ∈ SAT :=
  ⟨[[(0, true)]], by decide, ⟨fun _ => true, by simp [Satisfaz]⟩⟩

/-- Sanidade: a palavra `11` (a fórmula com uma cláusula vazia) não está em SAT. -/
theorem true_true_not_mem_SAT : ([true, true] : ClayPvsNP.Word) ∉ SAT := by
  rintro ⟨φ, hφ, τ, hτ⟩
  rcases φ with _ | ⟨C, φ⟩
  · simp [codCNF] at hφ
  · rcases C with _ | ⟨ℓ, C⟩
    · obtain ⟨ℓ, hℓ, -⟩ := hτ [] (by simp)
      simp at hℓ
    · simp [codCNF, codClausula, codLiteral, simb] at hφ

/-- Redução de Karp no modelo fixado: uma função `Word → Word` computada por uma `FinTM2` em
tempo polinomial (entrada e saída na fita como a própria palavra). -/
def KarpRed (A B : ClayPvsNP.Language) : Prop :=
  ∃ f : ClayPvsNP.Word → ClayPvsNP.Word, (∀ w, w ∈ A ↔ f w ∈ B) ∧
    Nonempty (TM2ComputableInPolyTime (id : ClayPvsNP.Word → List Bool) id f)

theorem karpRed_iff_Red (A B : ClayPvsNP.Language) : KarpRed A B ↔ Red A B := Iff.rfl

/-- `ClayPvsNP.P` é fechada por reduções de Karp. -/
theorem P_closed_KarpRed {A B : ClayPvsNP.Language} (h : KarpRed A B) (hB : B ∈ ClayPvsNP.P) :
    A ∈ ClayPvsNP.P := by
  rw [P_eq_classeP] at hB ⊢
  exact P_fechada_red h hB

/-- **SAT ∈ NP** no modelo fixado. -/
theorem SAT_mem_NP : SAT ∈ ClayPvsNP.NP := by
  rw [NP_eq_classeNP]
  exact ClayPvsNPProof.ATK.SATemNP.sat_em_NP

/-- **Cook–Levin** no modelo fixado: toda linguagem de `ClayPvsNP.NP` se reduz a SAT. -/
theorem SAT_NP_hard : ∀ L ∈ ClayPvsNP.NP, KarpRed L SAT := by
  intro L hL
  rw [NP_eq_classeNP] at hL
  exact ClayPvsNPProof.ATK.CookLevinNP.red_SAT hL

/-- **`P = NP ⟺ SAT ∈ P`** no modelo fixado. -/
theorem P_eq_NP_iff_SAT_mem_P : ClayPvsNP.P_eq_NP ↔ SAT ∈ ClayPvsNP.P := by
  constructor
  · intro h
    unfold ClayPvsNP.P_eq_NP at h
    rw [h]
    exact SAT_mem_NP
  · intro h
    refine Set.Subset.antisymm P_subset_NP fun L hL => ?_
    exact P_closed_KarpRed (SAT_NP_hard L hL) h

/-- **A lacuna**: SAT não está em `ClayPvsNP.P`. É o problema em aberto (equivalente a
`¬ ClayPvsNP.P_eq_NP` por `not_P_eq_NP_iff_Gap`); não é provada aqui. -/
def Gap : Prop := SAT ∉ ClayPvsNP.P

/-- **`P ≠ NP ⟺ Gap`.** -/
theorem not_P_eq_NP_iff_Gap : ¬ ClayPvsNP.P_eq_NP ↔ Gap :=
  not_congr P_eq_NP_iff_SAT_mem_P

/-- O alvo `Target = ClayPvsNP.P_eq_NP` vale se e somente se a lacuna falha. -/
theorem Target_iff_not_Gap : Target ↔ ¬ Gap := by
  unfold Gap
  rw [not_not]
  exact P_eq_NP_iff_SAT_mem_P

end ClayPvsNPProof
