-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/CookLevinReducao.lean
-- (sha256 do original: 92eba3a30e9ca688…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.CookLevinTableau

/-!
# ATK — Ponte B4, marco M2c: a redução de Cook–Levin como função pura

Para `L ∈ classeNP` (dados extraídos em `DadosNP`: verificador `χ` computado por uma `FinTM2` em
tempo polinomial, cota `q` dos certificados):

* `tabTM`: o tableau (marco M2b) da máquina, com rótulos e estados enumerados, e valores de
  célula limitados aos símbolos que podem aparecer (`simbolosTM`, finito). Isso é necessário
  porque a `FinTM2` da Mathlib só exige alfabeto finito na pilha de entrada. `bomTM` dá as
  hipóteses de boa formação;
* `nome`: cada variável vira um número cujos bits são uma cadeia estruturada (blocos unários e
  uma marca final), `nome_inj`. Uma máquina imprime esses nomes sem aritmética binária;
* `codCNF_mem_SAT`: `codCNF φ ∈ SAT ⟺ φ` satisfatível;
* `reducao D T H w = codCNF (renomeia (tableau de w))`;
* **`reducao_iff`**: `w ∈ L ⟺ reducao D T H w ∈ SAT`, para qualquer tempo `T` que cubra o tempo
  da máquina nas entradas `par w c` com `|c| ≤ q(|w|)` e qualquer altura `H` suficiente.

Observação honesta: classicamente, toda linguagem se reduz a SAT por *alguma* função (não
computável). O conteúdo daqui é a função explícita e local do tableau. Que ela seja computável
por uma `FinTM2` em tempo polinomial é o marco M2d (`ClayPvsNPProof.ATK.CookLevinNP`), que fecha
`CookLevin modeloPNP SAT`.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.CookLevinReducao

open Turing ClayPvsNPProof.ATK.LigacaoPNP ClayPvsNPProof.ATK.ModeloPNP ClayPvsNPProof.ATK.SATemNP ClayPvsNPProof.ATK.CookLevinBase ClayPvsNPProof.ATK.CookLevinTableau

/-! ## SAT sobre codificações -/

/-- `codCNF φ ∈ SAT` exatamente quando `φ` é satisfatível. -/
theorem codCNF_mem_SAT (φ : CNF) : codCNF φ ∈ SAT ↔ Satisfativel φ := by
  constructor
  · intro h
    obtain ⟨c, -, hc⟩ := (sat_iff (codCNF φ)).mp h
    rw [acc_cnf, List.all_eq_true] at hc
    refine ⟨fun n => decide (val c n.bits = some true), fun C hC => ?_⟩
    obtain ⟨ℓ, hℓ, hb⟩ := List.any_eq_true.mp (hc C hC)
    refine ⟨ℓ, hℓ, ?_⟩
    simp only [bom, decide_eq_true_eq] at hb
    show decide (val c ℓ.1.bits = some true) = ℓ.2
    rw [hb, dec_some]
  · intro h
    exact ⟨φ, rfl, h⟩

/-! ## Nomes das variáveis: cadeias de bits estruturadas -/

/-- `n` em unário, terminado por `false`. -/
def unario (n : ℕ) : List Bool := List.replicate n true ++ [false]

theorem unario_append_inj : ∀ {a b : ℕ} {r s : List Bool}, unario a ++ r = unario b ++ s → a = b ∧ r = s
  | 0, 0, r, s, h => by simpa [unario] using h
  | 0, b + 1, r, s, h => by simp [unario, List.replicate_succ] at h
  | a + 1, 0, r, s, h => by simp [unario, List.replicate_succ] at h
  | a + 1, b + 1, r, s, h => by
    simp only [unario, List.replicate_succ, List.cons_append, List.append_assoc,
      List.cons.injEq, true_and] at h
    have := unario_append_inj (a := a) (b := b) (r := r) (s := s) (by simpa [unario] using h)
    exact ⟨by omega, this.2⟩

variable {K : Type} [Fintype K]

/-- Índice de cada pilha. -/
noncomputable def κ (k : K) : ℕ := (Fintype.equivFin K k : ℕ)

theorem κ_inj : Function.Injective (κ (K := K)) := by
  intro a b h
  exact (Fintype.equivFin K).injective (Fin.ext h)

/-- A cadeia de bits que nomeia cada variável (canônica: termina em `true`). -/
noncomputable def cadeia : Var K → List Bool
  | .x t k i j => [true, true] ++ unario t ++ unario (κ k) ++ unario i ++ unario j ++ [true]
  | .y t j => [true, false] ++ unario t ++ unario j ++ [true]
  | .z t j => [false, true] ++ unario t ++ unario j ++ [true]

theorem cadeia_canonica (v : Var K) : Canonica (cadeia v) := by
  right
  obtain ⟨l, hl⟩ : ∃ l, cadeia v = l ++ [true] := by cases v <;> exact ⟨_, rfl⟩
  rw [hl]
  simp

theorem cadeia_inj : Function.Injective (cadeia (K := K)) := by
  intro v w h
  cases v with
  | x t k i j =>
    cases w with
    | x t' k' i' j' =>
      simp only [cadeia, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
        true_and] at h
      obtain ⟨h1, h⟩ := unario_append_inj h
      obtain ⟨h2, h⟩ := unario_append_inj h
      obtain ⟨h3, h⟩ := unario_append_inj h
      obtain ⟨h4, -⟩ := unario_append_inj h
      rw [h1, κ_inj h2, h3, h4]
    | y => simp [cadeia] at h
    | z => simp [cadeia] at h
  | y t j =>
    cases w with
    | x => simp [cadeia] at h
    | y t' j' =>
      simp only [cadeia, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
        true_and] at h
      obtain ⟨h1, h⟩ := unario_append_inj h
      obtain ⟨h2, -⟩ := unario_append_inj h
      rw [h1, h2]
    | z => simp [cadeia] at h
  | z t j =>
    cases w with
    | x => simp [cadeia] at h
    | y => simp [cadeia] at h
    | z t' j' =>
      simp only [cadeia, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
        true_and] at h
      obtain ⟨h1, h⟩ := unario_append_inj h
      obtain ⟨h2, -⟩ := unario_append_inj h
      rw [h1, h2]

/-- O nome (número natural) de cada variável: os bits de `nome v` são `cadeia v`. -/
noncomputable def nome (v : Var K) : ℕ := deBits (cadeia v)

theorem bits_nome (v : Var K) : (nome v).bits = cadeia v := bits_deBits (cadeia_canonica v)

theorem nome_inj : Function.Injective (nome (K := K)) := by
  intro v w h
  apply cadeia_inj
  rw [← bits_nome, ← bits_nome, h]

/-- Renomear as variáveis do tableau para números naturais. -/
noncomputable def renomeia (φ : List (Cla K)) : CNF := φ.map (List.map fun ℓ => (nome ℓ.1, ℓ.2))

theorem satisfativel_renomeia (φ : List (Cla K)) :
    Satisfativel (renomeia φ) ↔ ∃ τ, Sat τ φ := by
  classical
  constructor
  · rintro ⟨τ', h⟩
    refine ⟨fun v => τ' (nome v), fun C hC => ?_⟩
    obtain ⟨ℓ, hℓ, hτ⟩ := h _ (List.mem_map.mpr ⟨C, hC, rfl⟩)
    obtain ⟨ℓ', hℓ', rfl⟩ := List.mem_map.mp hℓ
    exact ⟨ℓ', hℓ', hτ⟩
  · rintro ⟨τ, h⟩
    refine ⟨fun n => if hn : ∃ v, nome v = n then τ (Classical.choose hn) else false, ?_⟩
    intro C hC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
    obtain ⟨ℓ, hℓ, hτ⟩ := h C' hC'
    refine ⟨(nome ℓ.1, ℓ.2), List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩, ?_⟩
    have hex : ∃ v, nome v = nome ℓ.1 := ⟨ℓ.1, rfl⟩
    simp only [hex, dite_true]
    rw [nome_inj (Classical.choose_spec hex)]
    exact hτ


/-! ## O tableau de uma `FinTM2` -/

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

section maquina

variable (tm : FinTM2) (eIn : tm.Γ tm.k₀ ≃ Bool) (eOut : tm.Γ tm.k₁ ≃ Bool)

/-- Os símbolos que podem aparecer nas pilhas: os empurrados pelo programa, os da entrada e os
da saída. -/
def simbolosTM : Set (Σ k, tm.Γ k) :=
  (⋃ l, simbolos (tm.m l)) ∪ Set.range (fun b : Bool => (⟨tm.k₀, eIn.symm b⟩ : Σ k, tm.Γ k)) ∪
    Set.range (fun b : Bool => (⟨tm.k₁, eOut.symm b⟩ : Σ k, tm.Γ k))

theorem simbolosTM_finite : (simbolosTM tm eIn eOut).Finite :=
  ((Set.finite_iUnion fun l => simbolos_finite (tm.m l)).union (Set.finite_range _)).union
    (Set.finite_range _)

theorem fibra_finite (k : tm.K) : {a : tm.Γ k | (⟨k, a⟩ : Σ k, tm.Γ k) ∈ simbolosTM tm eIn eOut}.Finite :=
  (simbolosTM_finite tm eIn eOut).preimage (fun _ _ _ _ h => sigma_mk_injective h)

/-- O tableau da máquina. -/
noncomputable abbrev tabTM : Tab tm.K tm.Γ tm.Λ tm.σ where
  M := tm.m
  k₀ := tm.k₀
  k₁ := tm.k₁
  l₀ := tm.main
  v₀ := tm.initialState
  labs := (Finset.univ : Finset (Option tm.Λ)).toList
  sts := (Finset.univ : Finset tm.σ).toList
  vals := fun k => none :: ((fibra_finite tm eIn eOut k).toFinset.toList.map some)
  d := Finset.univ.sup fun l => prof (tm.m l)

/-- Cota de crescimento por passo. -/
noncomputable def empTM : ℕ := Finset.univ.sup fun l => emp (tm.m l)

theorem mem_vals {k : tm.K} {a : tm.Γ k} (h : (⟨k, a⟩ : Σ k, tm.Γ k) ∈ simbolosTM tm eIn eOut) :
    some a ∈ (tabTM tm eIn eOut).vals k := by
  simp only [List.mem_cons, reduceCtorEq, false_or, List.mem_map, Option.some.injEq,
    exists_eq_right, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact h

theorem bomTM (pre cands : List (tm.Γ tm.k₀)) (Q T H : ℕ) (acc : tm.Γ tm.k₁)
    (hpre : ∀ a ∈ pre, ∃ b, a = eIn.symm b) (hcands : ∀ a ∈ cands, ∃ b, a = eIn.symm b)
    (hacc : ∃ b, acc = eOut.symm b)
    (hH : pre.length + Q + empTM tm * T + (tabTM tm eIn eOut).d < H) :
    (tabTM tm eIn eOut).Bom pre cands Q T H (empTM tm) acc where
  labs_nodup := Finset.nodup_toList _
  labs_all := fun l => by simp
  sts_nodup := Finset.nodup_toList _
  sts_all := fun v => by simp
  vals_nodup := fun k => by
    refine List.nodup_cons.mpr ⟨by simp, (Finset.nodup_toList _).map (Option.some_injective _)⟩
  none_mem := fun k => by simp
  pre_mem := fun a ha => by
    obtain ⟨b, rfl⟩ := hpre a ha
    exact mem_vals tm eIn eOut (Or.inl (Or.inr ⟨b, rfl⟩))
  cands_mem := fun a ha => by
    obtain ⟨b, rfl⟩ := hcands a ha
    exact mem_vals tm eIn eOut (Or.inl (Or.inr ⟨b, rfl⟩))
  acc_mem := by
    obtain ⟨b, rfl⟩ := hacc
    exact mem_vals tm eIn eOut (Or.inr ⟨b, rfl⟩)
  push_mem := fun l k a h => mem_vals tm eIn eOut (Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨l, h⟩)))
  prof_le := fun l => Finset.le_sup (f := fun l => prof (tm.m l)) (Finset.mem_univ l)
  emp_le := fun l => Finset.le_sup (f := fun l => emp (tm.m l)) (Finset.mem_univ l)
  altura := hH

/-- A configuração inicial do tableau é a `initList` da máquina. -/
theorem init_tabTM (x : List (tm.Γ tm.k₀)) : (tabTM tm eIn eOut).init x = initList tm x := by
  simp only [Tab.init, initList, tabTM]
  congr 1
  funext k
  by_cases hk : k = tm.k₀
  · subst hk; simp
  · simp [hk]

end maquina


/-! ## A redução para uma linguagem de NP -/

/-- Os dados de uma linguagem de NP, extraídos da definição: verificador `χ` computado por uma
`FinTM2` em tempo polinomial e cota polinomial `q` dos certificados. -/
structure DadosNP (L : Linguagem) where
  χ : Palavra → Bool
  M : TM2ComputableInPolyTime cod Computability.encodeBool χ
  q : Polynomial ℕ
  hq : ∀ w, w ∈ L ↔ ∃ c : Palavra, c.length ≤ q.eval w.length ∧ χ (par w c) = true

/-- Toda linguagem de NP tem esses dados (escolha). -/
noncomputable def dadosNP {L : Linguagem} (hL : L ∈ classeNP) : DadosNP L :=
  have hL' : EmNP L := hL
  have hV := Classical.choose_spec hL'
  have hχ := Classical.choose_spec hV.1
  { χ := Classical.choose hV.1
    M := hχ.2.some
    q := Classical.choose hV.2
    hq := fun w => by
      rw [Classical.choose_spec hV.2 w]
      simp only [hχ.1] }

section reducao

variable {L : Linguagem} (D : DadosNP L)

/-- Prefixo fixo da entrada da máquina: `w` duplicado e o separador. -/
def preD (w : Palavra) : List (D.M.tm.Γ D.M.tm.k₀) :=
  (w.flatMap (fun b => [b, b]) ++ [false, true]).map D.M.inputAlphabet.invFun

/-- Valores possíveis das células de certificado. -/
def candsD : List (D.M.tm.Γ D.M.tm.k₀) :=
  [D.M.inputAlphabet.invFun false, D.M.inputAlphabet.invFun true]

/-- Símbolo de aceitação no topo da pilha de saída. -/
def accD : D.M.tm.Γ D.M.tm.k₁ := D.M.outputAlphabet.invFun true

/-- O tableau da redução para a palavra `w`, com tempo `T |w|` e altura `H |w|`. -/
noncomputable def formulaD (T H : ℕ → ℕ) (w : Palavra) : List (Cla D.M.tm.K) :=
  (tabTM D.M.tm D.M.inputAlphabet D.M.outputAlphabet).formula (preD D w) (candsD D)
    (D.q.eval w.length) (T w.length) (H w.length) (accD D)

/-- **A redução de Cook–Levin** (como função pura): a CNF do tableau, com variáveis renomeadas
para números cujos bits são cadeias estruturadas, codificada em binário. -/
noncomputable def reducao (T H : ℕ → ℕ) (w : Palavra) : Palavra :=
  codCNF (renomeia (formulaD D T H w))

theorem length_preD (w : Palavra) : (preD D w).length = 2 * w.length + 2 := by
  simp only [preD, List.length_map, List.length_append, List.length_flatMap, List.length_cons,
    List.length_nil]
  induction w with
  | nil => simp
  | cons b w ih => simp [List.sum_cons] at ih ⊢; omega

theorem entrada_par (w c : Palavra) :
    List.map D.M.inputAlphabet.invFun (cod (par w c)) =
      preD D w ++ c.map D.M.inputAlphabet.invFun := by
  simp [cod, par, preD, List.map_append]

theorem length_par (w c : Palavra) : (par w c).length = 2 * w.length + 2 + c.length := by
  simp only [par, List.length_append, List.length_cons, List.length_nil]
  have : (w.flatMap fun b => [b, b]).length = 2 * w.length := by
    induction w with
    | nil => simp
    | cons b w ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
        List.length_nil] at ih ⊢; omega
  omega

theorem haltList_k₁ (tm : FinTM2) (l : List (tm.Γ tm.k₁)) : (haltList tm l).stk tm.k₁ = l := by
  simp [haltList]

/-- A execução acolchoada do tableau sobre `par w c` termina na parada com `χ (par w c)`. -/
theorem run_par (T : ℕ → ℕ) (hT : ∀ n, D.M.time.eval (2 * n + 2 + D.q.eval n) ≤ T n)
    (w c : Palavra) (hc : c.length ≤ D.q.eval w.length) :
    (tabTM D.M.tm D.M.inputAlphabet D.M.outputAlphabet).run
        (preD D w ++ c.map D.M.inputAlphabet.invFun) (T w.length) =
      haltList D.M.tm [D.M.outputAlphabet.invFun (D.χ (par w c))] := by
  have hout := D.M.outputsFun (par w c)
  rw [entrada_par] at hout
  have hle : hout.steps ≤ T w.length := by
    refine hout.steps_le_m.trans ((eval_mono _ ?_).trans (hT w.length))
    show (par w c).length ≤ _
    rw [length_par]
    omega
  simp only [Tab.run, init_tabTM]
  have he := hout.evals_in_steps
  simp only [Option.map_some] at he
  exact acolchoada_de_evals _ _ _ rfl hout.steps (T w.length) hle he

/-- **A redução é correta**: `w ∈ L ⟺ reducao w ∈ SAT`, para qualquer tempo `T` que cubra o
tempo da máquina e altura `H` suficiente. -/
theorem reducao_iff (T H : ℕ → ℕ) (hT : ∀ n, D.M.time.eval (2 * n + 2 + D.q.eval n) ≤ T n)
    (hH : ∀ n, 2 * n + 2 + D.q.eval n + empTM D.M.tm * T n +
      (tabTM D.M.tm D.M.inputAlphabet D.M.outputAlphabet).d < H n) (w : Palavra) :
    w ∈ L ↔ reducao D T H w ∈ SAT := by
  have hb := bomTM D.M.tm D.M.inputAlphabet D.M.outputAlphabet (preD D w) (candsD D)
    (D.q.eval w.length) (T w.length) (H w.length) (accD D)
    (fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
      exact ⟨x, by simp⟩)
    (fun a ha => by
      simp only [candsD, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact ⟨false, by simp⟩
      · exact ⟨true, by simp⟩)
    ⟨true, by simp [accD]⟩ (by rw [length_preD]; exact hH w.length)
  rw [reducao, codCNF_mem_SAT, satisfativel_renomeia, formulaD, Tab.tableau_iff _ hb, D.hq]
  constructor
  · rintro ⟨c, hc, hχ⟩
    refine ⟨c.map D.M.inputAlphabet.invFun, (List.length_map ..).trans_le hc, fun a ha => ?_, ?_, ?_⟩
    · obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      cases b
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    · rw [run_par D T hT w c hc]; rfl
    · rw [run_par D T hT w c hc, haltList_k₁, hχ]; rfl
  · rintro ⟨c, hc, hcc, -, hacc⟩
    refine ⟨c.map D.M.inputAlphabet, (List.length_map ..).trans_le hc, ?_⟩
    have hcm : (c.map D.M.inputAlphabet).map D.M.inputAlphabet.invFun = c := by
      simp [List.map_map]
    have := run_par D T hT w (c.map D.M.inputAlphabet) ((List.length_map ..).trans_le hc)
    rw [hcm] at this
    rw [this, haltList_k₁] at hacc
    simp only [List.getElem?_cons_zero, Option.some.injEq, accD] at hacc
    exact D.M.outputAlphabet.symm.injective hacc

end reducao

/-! ## Testes de sanidade -/

theorem teste_cadeia_y : cadeia (K := Unit) (.y 2 1) = [true, false, true, true, false, true, false, true] := by
  decide

theorem teste_sat_unit : codCNF [[((0 : ℕ), true)]] ∈ SAT :=
  (codCNF_mem_SAT _).mpr ⟨fun _ => true, by simp [Satisfaz]⟩

theorem teste_sat_vazia : codCNF [[]] ∉ SAT := by
  rw [codCNF_mem_SAT]
  exact clausula_vazia_insat

end ClayPvsNPProof.ATK.CookLevinReducao

