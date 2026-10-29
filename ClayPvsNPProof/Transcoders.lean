import ClayPvsNP
import ClayPvsNPProof.ATK.ModeloPNP

/-!
# Transcodificadores de pares: codificação fixada ↔ codificação do ATK

O enunciado fixado (`ClayPvsNP.pair`) codifica `⟨w, c⟩` como
`(w.flatMap fun b => [true, b]) ++ false :: c`; o kernel ATK (`ATK.LigacaoPNP.par`) codifica como
`(w.flatMap fun b => [b, b]) ++ [false, true] ++ c`. Este arquivo constrói duas máquinas
`Turing.FinTM2`, com prova de correção e de tempo **linear** (`2 n + 4` passos):

* `tA` (fixada → ATK): `tA (ClayPvsNP.pair w c) = par w c` (`tA_pair`), computada por `tAComputable`;
* `tP` (ATK → fixada): `tP (par w c) = ClayPvsNP.pair w c` (`tP_par`), computada por `tPComputable`.

As duas usam duas pilhas sobre `Bool` (`false` = entrada/saída, `true` = auxiliar) e três rótulos
(`0` = traduz, `1` = copia o resto, `2` = devolve a auxiliar para a saída), no estilo do
decodificador do ATK `ATK.ModeloPNP.decTM`, cujos auxiliares de configuração (`cfgD`, `pil`,
`upd_false`, `upd_true`, `passoSaida`) são reutilizados.

Código novo (não está no kernel ATK): é o transcodificador de pares que faltava para a codificação
fixada. Não decide nada sobre P vs NP.
-/

namespace ClayPvsNPProof.Transcoders

open Turing Computability StateTransition Function
open ClayPvsNPProof.ATK.ModeloPNP ClayPvsNPProof.ATK.LigacaoPNP
open Turing.TM2.Stmt

/-! ## Uma máquina genérica de três rótulos -/

/-- Rótulo 1: copia o resto da entrada para a pilha auxiliar. -/
def passoCopia : StD :=
  pop false (fun _ o => (o, none))
    (branch (fun s => s.1.isSome)
      (push true (fun s => s.1.getD false) (load (fun _ => (none, none)) (goto fun _ => 1)))
      (load (fun _ => (none, none)) (goto fun _ => 2)))

/-- O programa: passo de tradução no rótulo `0`, depois cópia (`1`) e saída (`2`). -/
def prog (p0 : StD) : Fin 3 → StD
  | 0 => p0
  | 1 => passoCopia
  | 2 => passoSaida

/-- A máquina com passo de tradução `p0`. -/
abbrev tm (p0 : StD) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := σD
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog p0

abbrev stepT (p0 : StD) := Turing.TM2.step (prog p0)

theorem one {p0 : StD} {c c' : CfgD} (h : stepT p0 c = some c') :
    flip bind (stepT p0) (some c) = some c' := h

theorem copia_cons (p0 : StD) (a : Bool) (r A : List Bool) :
    stepT p0 (cfgD 1 (a :: r) A) = some (cfgD 1 r (a :: A)) := by
  simp [cfgD, stepT, prog, passoCopia, Turing.TM2.stepAux, pil_false, upd_false, pil_true,
    upd_true]

theorem copia_nil (p0 : StD) (A : List Bool) : stepT p0 (cfgD 1 [] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepT, prog, passoCopia, Turing.TM2.stepAux, pil_false, upd_false]

theorem saida_cons' (p0 : StD) (B : List Bool) (a : Bool) (A : List Bool) :
    stepT p0 (cfgD 2 B (a :: A)) = some (cfgD 2 (a :: B) A) := by
  simp [cfgD, stepT, prog, passoSaida, Turing.TM2.stepAux, pil_true, upd_true, pil_false,
    upd_false]

theorem saida_nil' (p0 : StD) (B : List Bool) :
    stepT p0 (cfgD 2 B []) = some ⟨none, (none, none), pil B []⟩ := by
  simp [cfgD, stepT, prog, passoSaida, Turing.TM2.stepAux, pil_true, upd_true]

theorem run_copia (p0 : StD) : ∀ (r A : List Bool),
    (flip bind (stepT p0))^[r.length + 1] (some (cfgD 1 r A)) = some (cfgD 2 [] (r.reverse ++ A))
  | [], A => by rw [List.length_nil, zero_add, iterate_one]; exact copia_nil p0 A
  | a :: r, A => by
    rw [List.length_cons, iterate_succ_apply, one (copia_cons p0 a r A), run_copia p0 r (a :: A)]
    simp

theorem run_saida' (p0 : StD) : ∀ (A B : List Bool),
    (flip bind (stepT p0))^[A.length + 1] (some (cfgD 2 B A)) =
      some ⟨none, (none, none), pil (A.reverse ++ B) []⟩
  | [], B => by rw [List.length_nil, zero_add, iterate_one]; exact saida_nil' p0 B
  | a :: A, B => by
    rw [List.length_cons, iterate_succ_apply, one (saida_cons' p0 B a A), run_saida' p0 A (a :: B)]
    simp

theorem initList_tm (p0 : StD) (x : List Bool) : initList (tm p0) x = cfgD 0 x [] := by
  simp only [initList, cfgD, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem haltList_tm (p0 : StD) (y : List Bool) :
    haltList (tm p0) y = (⟨none, (none, none), pil y []⟩ : CfgD) := by
  simp only [haltList, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

/-- **Computabilidade em tempo linear (genérica)**: se a fase de tradução leva `x` ao rótulo `2`
com `(g x).reverse` na pilha auxiliar em `k x ≤ |x| + 2` passos, e `|g x| ≤ |x| + 1`, então `g` é
computada por `tm p0` em tempo `2 n + 4`. -/
noncomputable def computavel (p0 : StD) (g : List Bool → List Bool) (k : List Bool → ℕ)
    (hrun : ∀ x, (flip bind (stepT p0))^[k x] (some (cfgD 0 x [])) =
      some (cfgD 2 [] ((g x).reverse ++ [])))
    (hk : ∀ x, k x ≤ x.length + 2) (hg : ∀ x, (g x).length ≤ x.length + 1) :
    TM2ComputableInPolyTime cod cod g where
  tm := tm p0
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * Polynomial.X + 4
  outputsFun x := by
    have hrun' := hrun x
    have hsai := run_saida' p0 ((g x).reverse ++ []) []
    simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hsai hrun'
    have hin : List.map (Equiv.refl Bool).invFun (cod x) = x := by simp [cod]
    have hout : List.map (Equiv.refl Bool).invFun (cod (g x)) = g x := by simp [cod]
    refine ⟨⟨((g x).length + 1) + k x, ?_⟩, ?_⟩
    · rw [hin, hout, initList_tm, Option.map_some, haltList_tm]
      show (flip bind (stepT p0))^[((g x).length + 1) + k x] (some (cfgD 0 x [])) = _
      rw [iterate_add_apply, hrun', hsai]
      rfl
    · have h1 := hk x
      have h2 := hg x
      change (g x).length + 1 + k x ≤ Polynomial.eval x.length (2 * Polynomial.X + 4)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat]
      omega

/-! ## Par fixado → par do ATK -/

/-- Passo de tradução de `tA`: `1 b ↦ b b`; `0 ↦ 0 1` e copia o resto. -/
def passoA : StD :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (branch (fun s => s.1.getD false)
        (pop false (fun s o => (s.1, o))
          (branch (fun s => s.2.isSome)
            (push true (fun s => s.2.getD false) (push true (fun s => s.2.getD false)
              (load (fun _ => (none, none)) (goto fun _ => 0))))
            (load (fun _ => (none, none)) (goto fun _ => 2))))
        (push true (fun _ => false) (push true (fun _ => true)
          (load (fun _ => (none, none)) (goto fun _ => 1)))))
      (load (fun _ => (none, none)) (goto fun _ => 2)))

/-- Par fixado → par do ATK (total em todas as palavras). -/
def tA : List Bool → List Bool
  | true :: b :: r => b :: b :: tA r
  | [true] => []
  | false :: r => false :: true :: r
  | [] => []

/-- Passos da fase de tradução de `tA`. -/
def kA : List Bool → ℕ
  | true :: _ :: r => kA r + 1
  | [true] => 1
  | false :: r => r.length + 2
  | [] => 1

theorem tA_pair (w c : List Bool) : tA (ClayPvsNP.pair w c) = par w c := by
  induction w with
  | nil => simp [ClayPvsNP.pair, par, tA]
  | cons b w ih =>
    rw [ClayPvsNP.pair_cons, tA, ih]
    simp [par]

theorem kA_le : ∀ x : List Bool, kA x ≤ x.length + 2
  | true :: b :: r => by simp only [kA, List.length_cons]; have := kA_le r; omega
  | [true] => by simp [kA]
  | false :: r => by simp [kA]
  | [] => by simp [kA]

theorem tA_length : ∀ x : List Bool, (tA x).length ≤ x.length + 1
  | true :: b :: r => by simp only [tA, List.length_cons]; have := tA_length r; omega
  | [true] => by simp [tA]
  | false :: r => by simp [tA]
  | [] => by simp [tA]

theorem stepA_tt (b : Bool) (r A : List Bool) :
    stepT passoA (cfgD 0 (true :: b :: r) A) = some (cfgD 0 r (b :: b :: A)) := by
  simp [cfgD, stepT, prog, passoA, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem stepA_t (A : List Bool) : stepT passoA (cfgD 0 [true] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepT, prog, passoA, Turing.TM2.stepAux, pil_false, upd_false]

theorem stepA_f (r A : List Bool) :
    stepT passoA (cfgD 0 (false :: r) A) = some (cfgD 1 r (true :: false :: A)) := by
  simp [cfgD, stepT, prog, passoA, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem stepA_nil (A : List Bool) : stepT passoA (cfgD 0 [] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepT, prog, passoA, Turing.TM2.stepAux, pil_false, upd_false]

theorem runA : ∀ (x A : List Bool),
    (flip bind (stepT passoA))^[kA x] (some (cfgD 0 x A)) = some (cfgD 2 [] ((tA x).reverse ++ A))
  | true :: b :: r, A => by
    simp only [kA]
    rw [iterate_succ_apply, one (stepA_tt b r A), runA r (b :: b :: A)]
    simp [tA]
  | [true], A => by
    simp only [kA, iterate_one, tA, List.reverse_nil, List.nil_append]
    exact stepA_t A
  | false :: r, A => by
    simp only [kA]
    rw [show r.length + 2 = r.length + 1 + 1 from rfl, iterate_succ_apply,
      one (stepA_f r A), run_copia passoA r]
    simp [tA]
  | [], A => by
    simp only [kA, iterate_one, tA, List.reverse_nil, List.nil_append]
    exact stepA_nil A

/-- **Par fixado → par do ATK em tempo linear.** -/
noncomputable def tAComputable : TM2ComputableInPolyTime cod cod tA :=
  computavel passoA tA kA (fun x => runA x []) kA_le tA_length

/-! ## Par do ATK → par fixado -/

/-- Passo de tradução de `tP`: `a a ↦ 1 a`; `a b` com `a ≠ b` `↦ 0` e copia o resto. -/
def passoP : StD :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (pop false (fun s o => (s.1, o))
        (branch (fun s => s.2.isSome)
          (branch (fun s => decide (s.1 = s.2))
            (push true (fun _ => true) (push true (fun s => s.1.getD false)
              (load (fun _ => (none, none)) (goto fun _ => 0))))
            (push true (fun _ => false) (load (fun _ => (none, none)) (goto fun _ => 1))))
          (load (fun _ => (none, none)) (goto fun _ => 2))))
      (load (fun _ => (none, none)) (goto fun _ => 2)))

/-- Par do ATK → par fixado (total em todas as palavras). -/
def tP : List Bool → List Bool
  | a :: b :: r => if a = b then true :: a :: tP r else false :: r
  | _ => []

/-- Passos da fase de tradução de `tP`. -/
def kP : List Bool → ℕ
  | a :: b :: r => if a = b then kP r + 1 else r.length + 2
  | _ => 1

theorem tP_par (w c : List Bool) : tP (par w c) = ClayPvsNP.pair w c := by
  induction w with
  | nil => simp [ClayPvsNP.pair, par, tP]
  | cons b w ih =>
    have h : par (b :: w) c = b :: b :: par w c := by simp [par]
    simp only [h, tP, ↓reduceIte, ih, ClayPvsNP.pair_cons]

theorem kP_le : ∀ x : List Bool, kP x ≤ x.length + 2
  | a :: b :: r => by
    simp only [kP, List.length_cons]
    split_ifs
    · have := kP_le r; omega
    · omega
  | [_] => by simp [kP]
  | [] => by simp [kP]

theorem tP_length : ∀ x : List Bool, (tP x).length ≤ x.length + 1
  | a :: b :: r => by
    simp only [tP, List.length_cons]
    split_ifs
    · simp only [List.length_cons]; have := tP_length r; omega
    · simp
  | [_] => by simp [tP]
  | [] => by simp [tP]

theorem stepP_eq (a : Bool) (r A : List Bool) :
    stepT passoP (cfgD 0 (a :: a :: r) A) = some (cfgD 0 r (a :: true :: A)) := by
  simp [cfgD, stepT, prog, passoP, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem stepP_ne (a b : Bool) (r A : List Bool) (h : a ≠ b) :
    stepT passoP (cfgD 0 (a :: b :: r) A) = some (cfgD 1 r (false :: A)) := by
  simp [cfgD, stepT, prog, passoP, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true, h]

theorem stepP_one (a : Bool) (A : List Bool) : stepT passoP (cfgD 0 [a] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepT, prog, passoP, Turing.TM2.stepAux, pil_false, upd_false]

theorem stepP_nil (A : List Bool) : stepT passoP (cfgD 0 [] A) = some (cfgD 2 [] A) := by
  simp [cfgD, stepT, prog, passoP, Turing.TM2.stepAux, pil_false, upd_false]

theorem runP : ∀ (x A : List Bool),
    (flip bind (stepT passoP))^[kP x] (some (cfgD 0 x A)) = some (cfgD 2 [] ((tP x).reverse ++ A))
  | a :: b :: r, A => by
    by_cases h : a = b
    · subst h
      simp only [kP, ite_true]
      rw [iterate_succ_apply, one (stepP_eq a r A), runP r (a :: true :: A)]
      simp [tP]
    · simp only [kP, h, ite_false]
      rw [show r.length + 2 = r.length + 1 + 1 from rfl, iterate_succ_apply,
        one (stepP_ne a b r A h), run_copia passoP r]
      simp [tP, h]
  | [a], A => by
    simp only [kP, iterate_one, tP, List.reverse_nil, List.nil_append]
    exact stepP_one a A
  | [], A => by
    simp only [kP, iterate_one, tP, List.reverse_nil, List.nil_append]
    exact stepP_nil A

/-- **Par do ATK → par fixado em tempo linear.** -/
noncomputable def tPComputable : TM2ComputableInPolyTime cod cod tP :=
  computavel passoP tP kP (fun x => runP x []) kP_le tP_length

end ClayPvsNPProof.Transcoders
