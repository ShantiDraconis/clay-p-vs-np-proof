-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/CookLevinTableau.lean
-- (sha256 do original: 1a47f6b4dc45d592…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.CookLevinBase

/-!
# ATK — Ponte B4, marco M2b: o tableau de Cook–Levin para máquinas de pilhas

Para uma máquina `Turing.TM2` qualquer (dados estáticos em `Tab`: programa, pilhas de entrada e
saída, rótulo e estado iniciais, listas que enumeram rótulos, estados e valores de célula, e a
profundidade da janela), `Tab.formula pre cands Q T H acc` é uma CNF sobre as variáveis
`x t k i j` (célula `i` da pilha `k` no tempo `t` tem o valor `j`), `y t j` (rótulo) e `z t j`
(estado). As famílias de cláusulas são:

* (E) exatamente um valor por célula, rótulo e estado (`umSo`);
* (I) a linha inicial: rótulo e estado iniciais, a entrada `pre` seguida de até `Q` células
  livres (valores em `cands`, contíguas) e o resto vazio;
* (R) as transições. Para cada rótulo, estado e padrão das `d` primeiras células de cada pilha,
  a linha `t + 1` é o passo calculado sobre a janela, e o resto de cada pilha é deslocado. Isso
  é local graças ao lema de moldura (`ClayPvsNPProof.ATK.CookLevinBase.stepAux_topo`);
* (P) uma configuração parada fica parada;
* (A) aceitação no tempo `T`: parada, com `acc` no topo da pilha de saída.

**`tableau_iff`**: sob as hipóteses de boa formação `Bom` (listas completas e sem repetição,
símbolos empurrados cobertos, janela ≥ profundidade de leitura, altura suficiente), a fórmula é
satisfatível exatamente quando algum certificado `c` com `|c| ≤ Q` e símbolos em `cands` faz a
execução acolchoada de `T` passos sobre `pre ++ c` parar com `acc` no topo. As duas direções
estão provadas:

* `completo`: a atribuição lida da execução real satisfaz todas as cláusulas;
* `base_correto` + `passo_correto`: a linha 0 de qualquer atribuição satisfatória é a
  configuração inicial com algum certificado, e cada linha força a seguinte.

Sanidade (`Teste`): numa máquina que para na hora, a fórmula é satisfatível com certificados
em `{false, true}` e insatisfatível com certificados só em `{false}`.

Os marcos seguintes são M2c (a redução pura `L ↦ codCNF` para `L ∈ NP`, `ClayPvsNPProof.ATK.CookLevinReducao`)
e M2d (a máquina geradora em tempo polinomial, `ClayPvsNPProof.ATK.CookLevinNP`). Nada aqui decide P vs NP.
**CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.CookLevinTableau

open Turing Turing.TM2 Function ClayPvsNPProof.ATK.CookLevinBase

/-! ## Variáveis, literais, cláusulas -/

/-- Variáveis do tableau: célula `i` da pilha `k` no tempo `t` tem o valor de índice `j`;
o rótulo no tempo `t` tem índice `j`; o estado no tempo `t` tem índice `j`. -/
inductive Var (K : Type) where
  | x (t : ℕ) (k : K) (i j : ℕ)
  | y (t j : ℕ)
  | z (t j : ℕ)

abbrev Lit (K : Type) := Var K × Bool
abbrev Cla (K : Type) := List (Lit K)

/-- `τ` satisfaz todas as cláusulas. -/
def Sat {K : Type} (τ : Var K → Bool) (φ : List (Cla K)) : Prop := ∀ C ∈ φ, ∃ ℓ ∈ C, τ ℓ.1 = ℓ.2

theorem sat_append {K : Type} {τ : Var K → Bool} {φ ψ : List (Cla K)} :
    Sat τ (φ ++ ψ) ↔ Sat τ φ ∧ Sat τ ψ := by
  simp only [Sat, List.mem_append]
  constructor
  · intro h; exact ⟨fun C hC => h C (Or.inl hC), fun C hC => h C (Or.inr hC)⟩
  · rintro ⟨h₁, h₂⟩ C (hC | hC)
    · exact h₁ C hC
    · exact h₂ C hC

theorem sat_flatten {K : Type} {τ : Var K → Bool} {φs : List (List (Cla K))} :
    Sat τ φs.flatten ↔ ∀ φ ∈ φs, Sat τ φ := by
  simp only [Sat, List.mem_flatten]
  constructor
  · intro h φ hφ C hC; exact h C ⟨φ, hφ, hC⟩
  · rintro h C ⟨φ, hφ, hC⟩; exact h φ hφ C hC

theorem sat_flatMap {K α : Type} {τ : Var K → Bool} {l : List α} {f : α → List (Cla K)} :
    Sat τ (l.flatMap f) ↔ ∀ a ∈ l, Sat τ (f a) := by
  rw [List.flatMap, sat_flatten]
  simp

theorem sat_singleton {K : Type} {τ : Var K → Bool} {C : Cla K} :
    Sat τ [C] ↔ ∃ ℓ ∈ C, τ ℓ.1 = ℓ.2 := by
  simp [Sat]

/-! ## Janela: as primeiras células até o primeiro vazio -/

def tomaSome {α : Type} : List (Option α) → List α
  | some a :: l => a :: tomaSome l
  | _ => []

theorem tomaSome_celulas {α : Type} : ∀ (L : List α) (d : ℕ),
    tomaSome ((List.range d).map fun i => L[i]?) = L.take d
  | L, 0 => by simp [tomaSome]
  | [], d + 1 => by simp [List.range_succ_eq_map, tomaSome]
  | a :: L, d + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getElem?_cons_zero, tomaSome, List.take_succ_cons]
    congr 1
    have := tomaSome_celulas L d
    simpa [Function.comp_def] using this


/-! ## Exatamente um -/

section umso
variable {K : Type}

def peloMenos (vs : List (Var K)) : Cla K := vs.map (·, true)

def noMaximo : List (Var K) → List (Cla K)
  | [] => []
  | v :: vs => vs.map (fun u => [(v, false), (u, false)]) ++ noMaximo vs

def umSo (vs : List (Var K)) : List (Cla K) := peloMenos vs :: noMaximo vs

theorem sat_noMaximo {τ : Var K → Bool} : ∀ {vs : List (Var K)},
    Sat τ (noMaximo vs) ↔ ∀ i j (hi : i < vs.length) (hj : j < vs.length), i < j →
      ¬(τ vs[i] = true ∧ τ vs[j] = true)
  | [] => by simp [noMaximo, Sat]
  | v :: vs => by
    rw [noMaximo, sat_append, sat_noMaximo]
    constructor
    · rintro ⟨h1, h2⟩ i j hi hj hij ⟨hti, htj⟩
      rcases i with _ | i
      · rcases j with _ | j
        · omega
        · have hj' : j < vs.length := by simpa using hj
          have := h1 [(v, false), (vs[j], false)] (List.mem_map.mpr ⟨vs[j], List.getElem_mem _, rfl⟩)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at this
          obtain ⟨ℓ, hℓ, hℓv⟩ := this
          rcases hℓ with rfl | rfl
          · simp at hti; simp [hti] at hℓv
          · simp at htj; simp [htj] at hℓv
      · rcases j with _ | j
        · omega
        · exact h2 i j (by simpa using hi) (by simpa using hj) (by omega) ⟨by simpa using hti, by simpa using htj⟩
    · intro h
      refine ⟨fun C hC => ?_, fun i j hi hj hij hh => h (i + 1) (j + 1) (by simpa using hi)
        (by simpa using hj) (by omega) (by simpa using hh)⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hC
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
      by_cases hv : τ v = true
      · refine ⟨(vs[j], false), by simp, ?_⟩
        have := h 0 (j + 1) (by simp) (by simpa using hj) (by omega)
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at this
        simpa [hv] using this
      · exact ⟨(v, false), by simp, by simpa using hv⟩

/-- Se uma variável da lista está verdadeira e vale "no máximo uma", o valor de cada variável
é forçado. -/
theorem umSo_forca {τ : Var K → Bool} {vs : List (Var K)} (h : Sat τ (umSo vs)) {a : ℕ}
    (ha : a < vs.length) (hta : τ vs[a] = true) (j : ℕ) (hj : j < vs.length) :
    τ vs[j] = decide (j = a) := by
  have hmax := (sat_noMaximo.mp (fun C hC => h C (List.mem_cons_of_mem _ hC)))
  by_cases hja : j = a
  · subst hja; simpa using hta
  · simp only [hja, decide_false]
    by_contra hc
    have htj : τ vs[j] = true := by simpa using hc
    rcases Nat.lt_or_gt_of_ne hja with hlt | hlt
    · exact hmax j a hj ha hlt ⟨htj, hta⟩
    · exact hmax a j ha hj hlt ⟨hta, htj⟩

/-- E reciprocamente: uma atribuição "indicadora" satisfaz `umSo`. -/
theorem umSo_de_indicadora {τ : Var K → Bool} {vs : List (Var K)} {a : ℕ} (ha : a < vs.length)
    (h : ∀ j (hj : j < vs.length), τ vs[j] = decide (j = a)) : Sat τ (umSo vs) := by
  intro C hC
  rcases List.mem_cons.mp hC with rfl | hC
  · exact ⟨(vs[a], true), List.mem_map.mpr ⟨vs[a], List.getElem_mem _, rfl⟩, by simp [h a ha]⟩
  · refine (sat_noMaximo.mpr ?_) C hC
    intro i j hi hj hij ⟨hti, htj⟩
    rw [h i hi] at hti; rw [h j hj] at htj
    simp at hti htj; omega

/-- A primeira parte de `umSo` diz que alguma variável está verdadeira. -/
theorem umSo_alguma {τ : Var K → Bool} {vs : List (Var K)} (h : Sat τ (umSo vs)) :
    ∃ a, ∃ ha : a < vs.length, τ vs[a] = true := by
  obtain ⟨ℓ, hℓ, hv⟩ := h (peloMenos vs) (List.mem_cons_self ..)
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hℓ
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hu
  exact ⟨a, ha, hv⟩

end umso


/-! ## Índices numa lista -/

noncomputable def ix {α : Type} (l : List α) (a : α) : ℕ := by
  classical exact l.idxOf a

theorem ix_lt {α : Type} {l : List α} {a : α} (h : a ∈ l) : ix l a < l.length := by
  classical
  unfold ix
  exact List.idxOf_lt_length_of_mem h

theorem getElem_ix {α : Type} {l : List α} {a : α} (h : a ∈ l) : l[ix l a]'(ix_lt h) = a := by
  classical
  unfold ix
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem h)

theorem getElem?_ix {α : Type} {l : List α} {a : α} (h : a ∈ l) : l[ix l a]? = some a := by
  rw [List.getElem?_eq_getElem (ix_lt h), getElem_ix h]

/-- Numa lista sem repetição, `l[j]? = some a` exatamente quando `j` é o índice de `a`. -/
theorem getElem?_eq_iff_ix {α : Type} {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l) {j : ℕ}
    (hj : j < l.length) : l[j]? = some a ↔ j = ix l a := by
  constructor
  · intro h
    have h1 := getElem?_ix ha
    rw [← h1] at h
    rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem (ix_lt ha)] at h
    exact (List.Nodup.getElem_inj_iff hl).mp (Option.some.inj h)
  · rintro rfl; exact getElem?_ix ha

theorem ix_getElem {α : Type} {l : List α} (hl : l.Nodup) {j : ℕ} (hj : j < l.length) :
    ix l l[j] = j := by
  have := (getElem?_eq_iff_ix hl (List.getElem_mem hj) hj).mp (List.getElem?_eq_getElem hj)
  exact this.symm

/-! ## O tableau de uma máquina de pilhas -/

/-- Dados estáticos do tableau: a máquina, as pilhas de entrada/saída, o rótulo e o estado
iniciais, listas que enumeram rótulos, estados e valores de célula, e a profundidade da janela. -/
structure Tab (K : Type) (Γ : K → Type) (Λ σ : Type) where
  M : Λ → Stmt Γ Λ σ
  k₀ : K
  k₁ : K
  l₀ : Λ
  v₀ : σ
  labs : List (Option Λ)
  sts : List σ
  vals : ∀ k, List (Option (Γ k))
  d : ℕ

namespace Tab

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)

noncomputable def ks : List K := (Finset.univ : Finset K).toList

omit [DecidableEq K] in
theorem mem_ks (k : K) : k ∈ ks (K := K) := by simp [ks]

def celulas (t : ℕ) (k : K) (i : ℕ) : List (Var K) := (List.range (A.vals k).length).map (Var.x t k i)
def rotulos (t : ℕ) : List (Var K) := (List.range A.labs.length).map (Var.y t)
def estados (t : ℕ) : List (Var K) := (List.range A.sts.length).map (Var.z t)

/-- (E) exatamente um valor por célula, rótulo e estado, nos tempos `0..T`. -/
noncomputable def fE (T H : ℕ) : List (Cla K) :=
  (List.range (T + 1)).flatMap fun t =>
    umSo (A.rotulos t) ++ umSo (A.estados t) ++
      ks.flatMap fun k => (List.range H).flatMap fun i => umSo (A.celulas t k i)

open Classical in
/-- (I) a linha inicial: rótulo e estado iniciais, pilhas vazias fora da entrada, a entrada
`pre` seguida de até `Q` células livres (valores em `cands`, contíguas). -/
noncomputable def fI (pre cands : List (Γ A.k₀)) (Q H : ℕ) : List (Cla K) :=
  [[(.y 0 (ix A.labs (some A.l₀)), true)], [(.z 0 (ix A.sts A.v₀), true)]] ++
  (ks.filter (· ≠ A.k₀)).flatMap (fun k =>
    (List.range H).map fun i => [(.x 0 k i (ix (A.vals k) none), true)]) ++
  (List.range H).flatMap (fun i =>
    if i < pre.length then [[(.x 0 A.k₀ i (ix (A.vals A.k₀) pre[i]?), true)]]
    else if i < pre.length + Q then
      ((List.range (A.vals A.k₀).length).filter (fun j =>
          (A.vals A.k₀).getD j none ∉ none :: cands.map some)).map
        (fun j => [(.x 0 A.k₀ i j, false)]) ++
      (if i + 1 < H then
        [[(.x 0 A.k₀ i (ix (A.vals A.k₀) none), false),
          (.x 0 A.k₀ (i + 1) (ix (A.vals A.k₀) none), true)]] else [])
    else [[(.x 0 A.k₀ i (ix (A.vals A.k₀) none), true)]])

/-- Padrões de janela: os índices dos valores das `d` primeiras células de cada pilha. -/
abbrev Pat := (k : K) → Fin A.d → Fin (A.vals k).length

noncomputable def pats : List A.Pat := (Finset.univ : Finset A.Pat).toList

theorem mem_pats (p : A.Pat) : p ∈ A.pats := by simp [pats]

/-- O conteúdo do topo de cada pilha descrito por um padrão. -/
def janela (p : A.Pat) (k : K) : List (Γ k) :=
  tomaSome ((List.finRange A.d).map fun i => (A.vals k)[(p k i).val]'(p k i).isLt)

/-- Antecedentes: "no tempo `t` o rótulo é `jl`, o estado é `jv` e o topo segue `p`". -/
noncomputable def antes (t jl jv : ℕ) (p : A.Pat) : Cla K :=
  (.y t jl, false) :: (.z t jv, false) ::
    ks.flatMap fun k => (List.finRange A.d).map fun i => (.x t k i.val (p k i).val, false)

/-- Consequentes: a linha `t + 1` é o resultado `r` do passo sobre a janela, com o resto de
cada pilha deslocado. -/
noncomputable def conseq (H t : ℕ) (r : Cfg Γ Λ σ) : List (Cla K) :=
  [[(.y (t + 1) (ix A.labs r.l), true)], [(.z (t + 1) (ix A.sts r.var), true)]] ++
  ks.flatMap fun k =>
    ((List.range (r.stk k).length).map fun i =>
      [(.x (t + 1) k i (ix (A.vals k) (r.stk k)[i]?), true)]) ++
    ((List.range H).filter (fun j => (r.stk k).length + j < H)).flatMap fun j =>
      if A.d + j < H then
        (List.range (A.vals k).length).map fun a =>
          [(.x t k (A.d + j) a, false), (.x (t + 1) k ((r.stk k).length + j) a, true)]
      else [[(.x (t + 1) k ((r.stk k).length + j) (ix (A.vals k) none), true)]]

/-- (R) transições, para cada tempo, rótulo, estado e padrão de janela. -/
noncomputable def fR (T H : ℕ) : List (Cla K) :=
  (List.range T).flatMap fun t =>
    (List.range A.labs.length).flatMap fun jl =>
      (List.range A.sts.length).flatMap fun jv =>
        A.pats.flatMap fun p =>
          match A.labs[jl]?, A.sts[jv]? with
          | some (some l), some v =>
              (A.conseq H t (stepAux (A.M l) v (A.janela p))).map (A.antes t jl jv p ++ ·)
          | _, _ => []

/-- (P) configuração parada fica parada. -/
noncomputable def fP (T H : ℕ) : List (Cla K) :=
  (List.range T).flatMap fun t =>
    [[(.y t (ix A.labs none), false), (.y (t + 1) (ix A.labs none), true)]] ++
    ((List.range A.sts.length).map fun jv =>
      [(.y t (ix A.labs none), false), (.z t jv, false), (.z (t + 1) jv, true)]) ++
    ks.flatMap fun k => (List.range H).flatMap fun i =>
      (List.range (A.vals k).length).map fun a =>
        [(.y t (ix A.labs none), false), (.x t k i a, false), (.x (t + 1) k i a, true)]

/-- (A) aceitação no tempo `T`: parada, com `acc` no topo da pilha de saída. -/
noncomputable def fA (T : ℕ) (acc : Γ A.k₁) : List (Cla K) :=
  [[(.y T (ix A.labs none), true)], [(.x T A.k₁ 0 (ix (A.vals A.k₁) (some acc)), true)]]

/-- **O tableau**. -/
noncomputable def formula (pre cands : List (Γ A.k₀)) (Q T H : ℕ) (acc : Γ A.k₁) : List (Cla K) :=
  A.fE T H ++ A.fI pre cands Q H ++ A.fR T H ++ A.fP T H ++ A.fA T acc

/-- Configuração inicial com a entrada `x` na pilha `k₀`. -/
def init (x : List (Γ A.k₀)) : Cfg Γ Λ σ := ⟨some A.l₀, A.v₀, update (fun _ => []) A.k₀ x⟩

/-- A execução acolchoada. -/
def run (x : List (Γ A.k₀)) (t : ℕ) : Cfg Γ Λ σ := (passoA A.M)^[t] (A.init x)

/-- A linha `t` de `τ` codifica a configuração `C`. -/
def Cod (τ : Var K → Bool) (H t : ℕ) (C : Cfg Γ Λ σ) : Prop :=
  (∀ j, j < A.labs.length → (τ (.y t j) = true ↔ A.labs[j]? = some C.l)) ∧
  (∀ j, j < A.sts.length → (τ (.z t j) = true ↔ A.sts[j]? = some C.var)) ∧
  (∀ k i j, i < H → j < (A.vals k).length →
    (τ (.x t k i j) = true ↔ (A.vals k)[j]? = some (C.stk k)[i]?))

/-- Hipóteses de boa formação do tableau. -/
structure Bom (pre cands : List (Γ A.k₀)) (Q T H D : ℕ) (acc : Γ A.k₁) : Prop where
  labs_nodup : A.labs.Nodup
  labs_all : ∀ l, l ∈ A.labs
  sts_nodup : A.sts.Nodup
  sts_all : ∀ v, v ∈ A.sts
  vals_nodup : ∀ k, (A.vals k).Nodup
  none_mem : ∀ k, none ∈ A.vals k
  pre_mem : ∀ a ∈ pre, some a ∈ A.vals A.k₀
  cands_mem : ∀ a ∈ cands, some a ∈ A.vals A.k₀
  acc_mem : some acc ∈ A.vals A.k₁
  push_mem : ∀ l k a, (⟨k, a⟩ : Σ k, Γ k) ∈ simbolos (A.M l) → some a ∈ A.vals k
  prof_le : ∀ l, prof (A.M l) ≤ A.d
  emp_le : ∀ l, emp (A.M l) ≤ D
  altura : pre.length + Q + D * T + A.d < H

end Tab


/-! ## Lemas auxiliares -/

theorem passoA_some {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    passoA M ⟨some l, v, S⟩ = stepAux (M l) v S := rfl

theorem map_finRange_val {α : Type} (d : ℕ) (g : ℕ → α) :
    (List.finRange d).map (fun i : Fin d => g i.val) = (List.range d).map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- Lista "contígua": depois de um vazio, só vazios. -/
def Contigua {α : Type} (L : List (Option α)) : Prop :=
  ∀ j (h : j + 1 < L.length), L[j]'(by omega) = none → L[j + 1] = none

theorem tomaSome_getElem? {α : Type} : ∀ (L : List (Option α)), Contigua L →
    ∀ j : ℕ, (tomaSome L)[j]? = (L[j]?).join
  | [], _, j => by simp [tomaSome]
  | none :: L, h, j => by
    have hL : ∀ j (hj : j < L.length), L[j] = none := by
      intro j hj
      induction j with
      | zero => exact h 0 (by simp; omega) rfl
      | succ j ih => exact h (j + 1) (by simp; omega) (ih (by omega))
    rcases j with _ | j
    · simp [tomaSome]
    · simp only [tomaSome, List.getElem?_nil, List.getElem?_cons_succ]
      rcases Nat.lt_or_ge j L.length with hj | hj
      · rw [List.getElem?_eq_getElem hj, hL j hj]; rfl
      · rw [List.getElem?_eq_none hj]; rfl
  | some a :: L, h, j => by
    have h' : Contigua L := fun j hj hn => h (j + 1) (by simp; omega) hn
    rcases j with _ | j
    · simp [tomaSome]
    · simp only [tomaSome, List.getElem?_cons_succ]
      exact tomaSome_getElem? L h' j

theorem length_tomaSome_le {α : Type} : ∀ L : List (Option α), (tomaSome L).length ≤ L.length
  | [] => by simp [tomaSome]
  | none :: L => by simp [tomaSome]
  | some a :: L => by simp [tomaSome, length_tomaSome_le L]

theorem mem_tomaSome {α : Type} : ∀ {L : List (Option α)} {a : α}, a ∈ tomaSome L → some a ∈ L
  | [], a, h => by simp [tomaSome] at h
  | none :: L, a, h => by simp [tomaSome] at h
  | some b :: L, a, h => by
    simp only [tomaSome, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (mem_tomaSome h)

/-! ## Forçamento por "exatamente um" -/

section forca
variable {K : Type} {α : Type} {τ : Var K → Bool}

/-- `umSo` sobre os índices de `l`, mais uma variável verdadeira: a linha codifica o valor. -/
theorem forca_cod {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l) {f : ℕ → Var K}
    (hs : Sat τ (umSo ((List.range l.length).map f))) (ht : τ (f (ix l a)) = true) :
    ∀ j, j < l.length → (τ (f j) = true ↔ l[j]? = some a) := by
  intro j hj
  have h := umSo_forca hs (a := ix l a) (by simpa using ix_lt ha) (by simpa using ht) j
    (by simpa using hj)
  simp only [List.getElem_map, List.getElem_range] at h
  rw [h, decide_eq_true_iff, getElem?_eq_iff_ix hl ha hj]

/-- Reciprocamente, a indicadora de um valor de `l` satisfaz `umSo`. -/
theorem cod_umSo {l : List α} (hl : l.Nodup) {a : α} (ha : a ∈ l) {f : ℕ → Var K}
    (h : ∀ j, j < l.length → (τ (f j) = true ↔ l[j]? = some a)) :
    Sat τ (umSo ((List.range l.length).map f)) := by
  refine umSo_de_indicadora (a := ix l a) (by simpa using ix_lt ha) (fun j hj => ?_)
  simp only [List.length_map, List.length_range] at hj
  simp only [List.getElem_map, List.getElem_range]
  have := (h j hj).trans (getElem?_eq_iff_ix hl ha hj)
  cases hb : τ (f j) <;> simp_all

end forca

/-! ## Invariantes da execução -/

namespace Tab

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)

omit [Fintype K] in
theorem run_zero (x : List (Γ A.k₀)) : A.run x 0 = A.init x := rfl

omit [Fintype K] in
theorem run_succ (x : List (Γ A.k₀)) (t : ℕ) : A.run x (t + 1) = passoA A.M (A.run x t) :=
  Function.iterate_succ_apply' _ _ _

omit [Fintype K] in
theorem init_stk_k₀ (x : List (Γ A.k₀)) : (A.init x).stk A.k₀ = x := by simp [init]

omit [Fintype K] in
theorem init_stk_ne (x : List (Γ A.k₀)) {k : K} (hk : k ≠ A.k₀) : (A.init x).stk k = [] := by
  simp [init, update_of_ne hk]

omit [Fintype K] in
/-- Altura e alfabeto ao longo da execução. -/
theorem run_inv (D : ℕ) (hemp : ∀ l, emp (A.M l) ≤ D) (P : ∀ k, Γ k → Prop)
    (hpush : ∀ l k a, (⟨k, a⟩ : Σ k, Γ k) ∈ simbolos (A.M l) → P k a)
    (x : List (Γ A.k₀)) (hx : ∀ a ∈ x, P A.k₀ a) : ∀ t,
    (∀ k, ((A.run x t).stk k).length ≤ x.length + D * t) ∧ (∀ k, ∀ a ∈ (A.run x t).stk k, P k a)
  | 0 => by
    refine ⟨fun k => ?_, fun k a ha => ?_⟩
    · by_cases hk : k = A.k₀
      · subst hk; simp [run_zero, init_stk_k₀]
      · simp [run_zero, init_stk_ne A x hk]
    · by_cases hk : k = A.k₀
      · subst hk; rw [run_zero, init_stk_k₀] at ha; exact hx a ha
      · rw [run_zero, init_stk_ne A x hk] at ha; simp at ha
  | t + 1 => by
    obtain ⟨h1, h2⟩ := run_inv D hemp P hpush x hx t
    rw [run_succ]
    rcases hc : A.run x t with ⟨_ | l, v, S⟩
    · rw [hc] at h1 h2
      rw [passoA_parada _ _ rfl]
      exact ⟨fun k => (h1 k).trans (by nlinarith), h2⟩
    · rw [hc] at h1 h2
      rw [passoA_some]
      refine ⟨fun k => ?_, fun k a ha => ?_⟩
      · have := length_stepAux_le (A.M l) v S k
        have := hemp l
        have := h1 k
        simp only at *
        nlinarith
      · rcases mem_stepAux (A.M l) v S k a ha with h | h
        · exact h2 k a h
        · exact hpush l k a h

/-! ## Completude: a execução real satisfaz o tableau -/

open Classical in
/-- A atribuição que lê a execução real. -/
noncomputable def τrun (x : List (Γ A.k₀)) : Var K → Bool
  | .x t k i j => decide ((A.vals k)[j]? = some ((A.run x t).stk k)[i]?)
  | .y t j => decide (A.labs[j]? = some (A.run x t).l)
  | .z t j => decide (A.sts[j]? = some (A.run x t).var)

omit [Fintype K] in
theorem cod_τrun (x : List (Γ A.k₀)) (H t : ℕ) : A.Cod (A.τrun x) H t (A.run x t) :=
  ⟨fun _ _ => by simp [τrun], fun _ _ => by simp [τrun], fun _ _ _ _ _ => by simp [τrun]⟩

omit [Fintype K] in
theorem celula_mem {pre cands : List (Γ A.k₀)} {Q T H D : ℕ} {acc : Γ A.k₁}
    (h : A.Bom pre cands Q T H D acc) {x : List (Γ A.k₀)} (hx : ∀ a ∈ x, some a ∈ A.vals A.k₀)
    (t : ℕ) (k : K) (i : ℕ) : ((A.run x t).stk k)[i]? ∈ A.vals k := by
  have inv := (A.run_inv D h.emp_le (fun k a => some a ∈ A.vals k) h.push_mem x hx t).2
  rcases Nat.lt_or_ge i ((A.run x t).stk k).length with hi | hi
  · rw [List.getElem?_eq_getElem hi]; exact inv k _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none hi]; exact h.none_mem k

omit [DecidableEq K] [Fintype K] in
theorem sat_par {τ : Var K → Bool} {a b : Cla K} (ha : ∃ ℓ ∈ a, τ ℓ.1 = ℓ.2)
    (hb : ∃ ℓ ∈ b, τ ℓ.1 = ℓ.2) : Sat τ [a, b] := by
  intro C hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · exact ha
  · exact hb

omit [DecidableEq K] [Fintype K] in
theorem sat_unit {τ : Var K → Bool} {v : Var K} {b : Bool} : Sat τ [[(v, b)]] ↔ τ v = b := by
  simp [Sat]

/-- Os consequentes valem quando a linha `t + 1` é o passo calculado sobre a janela. -/
theorem conseq_sat {x : List (Γ A.k₀)} {H t : ℕ} {r : Cfg Γ Λ σ}
    (hlabs : r.l ∈ A.labs) (hsts : r.var ∈ A.sts) (hnone : ∀ k, none ∈ A.vals k)
    (hmemr : ∀ k a, a ∈ r.stk k → some a ∈ A.vals k)
    (hH : ∀ k, ((A.run x t).stk k).length ≤ H)
    (hstep : A.run x (t + 1) =
      ⟨r.l, r.var, fun k => r.stk k ++ ((A.run x t).stk k).drop A.d⟩) :
    ∀ C ∈ A.conseq H t r, ∃ ℓ ∈ C, A.τrun x ℓ.1 = ℓ.2 := by
  classical
  intro C hC
  simp only [conseq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_map, List.mem_range, List.mem_filter] at hC
  rcases hC with (rfl | rfl) | ⟨k, -, hC | hC⟩
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [τrun, hstep, getElem?_ix hlabs, decide_true]
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [τrun, hstep, getElem?_ix hsts, decide_true]
  · obtain ⟨i, hi, rfl⟩ := hC
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have hm : (r.stk k)[i]? ∈ A.vals k := by
      rw [List.getElem?_eq_getElem hi]; exact hmemr k _ (List.getElem_mem hi)
    simp only [τrun, hstep, List.getElem?_append_left hi, getElem?_ix hm, decide_true]
  · obtain ⟨j, ⟨hjH, hjP⟩, hC⟩ := hC
    have hsh : (r.stk k ++ ((A.run x t).stk k).drop A.d)[(r.stk k).length + j]? =
        ((A.run x t).stk k)[A.d + j]? := by
      rw [List.getElem?_append_right (by omega), List.getElem?_drop]
      congr 1; omega
    split_ifs at hC with hdj
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hC
      by_cases hτ : A.τrun x (.x t k (A.d + j) a) = true
      · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        simp only [τrun, decide_eq_true_eq] at hτ
        simp only [τrun, hstep, hsh, hτ, decide_true]
      · exact ⟨_, List.mem_cons_self .., by simpa using hτ⟩
    · simp only [List.mem_singleton] at hC
      subst hC
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      have hn : ((A.run x t).stk k)[A.d + j]? = none :=
        List.getElem?_eq_none (by have := hH k; omega)
      simp only [τrun, hstep, hsh, hn, getElem?_ix (hnone k), decide_true]

omit [DecidableEq K] in
theorem antes_neg {t jl jv : ℕ} {p : A.Pat} : ∀ ℓ ∈ A.antes t jl jv p, ℓ.2 = false := by
  intro ℓ hℓ
  simp only [antes, List.mem_cons, List.mem_flatMap, List.mem_map] at hℓ
  rcases hℓ with rfl | rfl | ⟨k, -, i, -, rfl⟩ <;> rfl

/-- **Completude do tableau**: a execução real com um certificado aceito satisfaz a fórmula. -/
theorem completo {pre cands : List (Γ A.k₀)} {Q T H D : ℕ} {acc : Γ A.k₁}
    (h : A.Bom pre cands Q T H D acc) (c : List (Γ A.k₀)) (hc : c.length ≤ Q)
    (hcc : ∀ a ∈ c, a ∈ cands) (hl : (A.run (pre ++ c) T).l = none)
    (hacc : ((A.run (pre ++ c) T).stk A.k₁)[0]? = some acc) :
    Sat (A.τrun (pre ++ c)) (A.formula pre cands Q T H acc) := by
  classical
  have hx : ∀ a ∈ pre ++ c, some a ∈ A.vals A.k₀ := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h.pre_mem a ha
    · exact h.cands_mem a (hcc a ha)
  have inv := A.run_inv D h.emp_le (fun k a => some a ∈ A.vals k) h.push_mem (pre ++ c) hx
  have hcel := A.celula_mem h hx
  have halt : ∀ t, t ≤ T → ∀ k, ((A.run (pre ++ c) t).stk k).length + A.d ≤ H := by
    intro t ht k
    have h1 := (inv t).1 k
    have h2 := h.altura
    have h3 : D * t ≤ D * T := Nat.mul_le_mul_left _ ht
    simp only [List.length_append] at h1
    omega
  simp only [formula, sat_append]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- (E)
    rw [fE, sat_flatMap]
    intro t _
    rw [sat_append, sat_append, sat_flatMap]
    refine ⟨⟨cod_umSo h.labs_nodup (h.labs_all _) (fun j hj => (A.cod_τrun _ H t).1 j hj),
      cod_umSo h.sts_nodup (h.sts_all _) (fun j hj => (A.cod_τrun _ H t).2.1 j hj)⟩,
      fun k _ => ?_⟩
    rw [sat_flatMap]
    intro i hi
    exact cod_umSo (h.vals_nodup k) (hcel t k i)
      (fun j hj => (A.cod_τrun _ H t).2.2 k i j (List.mem_range.mp hi) hj)
  · -- (I)
    rw [fI, sat_append, sat_append]
    refine ⟨⟨sat_par ⟨_, List.mem_singleton_self _, ?_⟩ ⟨_, List.mem_singleton_self _, ?_⟩, ?_⟩, ?_⟩
    · simp [τrun, run_zero, init, getElem?_ix (h.labs_all _)]
    · simp [τrun, run_zero, init, getElem?_ix (h.sts_all _)]
    · rw [sat_flatMap]
      intro k hk
      have hk' : k ≠ A.k₀ := by simpa using (List.mem_filter.mp hk).2
      intro C hC
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hC
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp [τrun, run_zero, init_stk_ne A _ hk', getElem?_ix (h.none_mem k)]
    · rw [sat_flatMap]
      intro i hi
      have hiH := List.mem_range.mp hi
      have hrest : ¬ i < pre.length → i < pre.length + Q → Sat (A.τrun (pre ++ c))
          (((List.range (A.vals A.k₀).length).filter (fun j =>
            (A.vals A.k₀).getD j none ∉ none :: cands.map some)).map
              (fun j => [(Var.x 0 A.k₀ i j, false)])) := by
        intro h1 h2
        have e : (pre ++ c)[i]? = c[i - pre.length]? :=
          List.getElem?_append_right (by omega)
        intro C hC
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hC
        obtain ⟨hjr, hjf⟩ := List.mem_filter.mp hj
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        simp only [τrun, run_zero, init_stk_k₀, decide_eq_false_iff_not]
        intro heq
        have hg : (A.vals A.k₀).getD j none = (pre ++ c)[i]? := by
          rw [List.getD_eq_getElem?_getD, heq]; rfl
        simp only [decide_eq_true_eq] at hjf
        apply hjf
        rw [hg, e]
        rcases hcj : c[i - pre.length]? with _ | a
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _
            (List.mem_map.mpr ⟨a, hcc a (List.mem_of_getElem? hcj), rfl⟩)
      split_ifs with h1 h2 h3
      · rw [sat_unit]
        have e : (pre ++ c)[i]? = pre[i]? := List.getElem?_append_left h1
        have hm : pre[i]? ∈ A.vals A.k₀ := by
          rw [List.getElem?_eq_getElem h1]; exact h.pre_mem _ (List.getElem_mem h1)
        simp [τrun, run_zero, init_stk_k₀, e, getElem?_ix hm]
      · rw [sat_append]
        refine ⟨hrest h1 h2, ?_⟩
        intro C hC
        simp only [List.mem_singleton] at hC
        subst hC
        by_cases hn : (pre ++ c)[i]? = none
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
          have hn' : (pre ++ c)[i + 1]? = none :=
            List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hn; omega)
          simp [τrun, run_zero, init_stk_k₀, hn', getElem?_ix (h.none_mem _)]
        · refine ⟨_, List.mem_cons_self .., ?_⟩
          simp only [τrun, run_zero, init_stk_k₀, getElem?_ix (h.none_mem _)]
          simpa [eq_comm] using hn
      · rw [List.append_nil]; exact hrest h1 h2
      · rw [sat_unit]
        have e : (pre ++ c)[i]? = none := List.getElem?_eq_none (by simp; omega)
        simp [τrun, run_zero, init_stk_k₀, e, getElem?_ix (h.none_mem _)]
  · -- (R)
    rw [fR, sat_flatMap]
    intro t ht
    have htT : t < T := List.mem_range.mp ht
    rw [sat_flatMap]; intro jl _
    rw [sat_flatMap]; intro jv _
    rw [sat_flatMap]; intro p _
    rcases hlj : A.labs[jl]? with _ | _ | l
    · simp [Sat]
    · simp [Sat]
    rcases hvj : A.sts[jv]? with _ | v
    · simp [Sat]
    simp only []
    intro C hC
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hC
    by_cases hall : ∀ ℓ ∈ A.antes t jl jv p, A.τrun (pre ++ c) ℓ.1 = true
    · have hy := hall (.y t jl, false) (List.mem_cons_self ..)
      have hz := hall (.z t jv, false) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hcells : ∀ k (i : Fin A.d), A.τrun (pre ++ c) (.x t k i (p k i)) = true := fun k i =>
        hall _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨k, mem_ks k, List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩⟩)))
      simp only [τrun, decide_eq_true_eq, hlj, hvj, Option.some.injEq] at hy hz hcells
      have hval : ∀ k (i : Fin A.d), (A.vals k)[(p k i : ℕ)] = ((A.run (pre ++ c) t).stk k)[(i : ℕ)]? := by
        intro k i
        have := hcells k i
        rw [List.getElem?_eq_getElem (p k i).isLt] at this
        exact Option.some.inj this
      have hjan : A.janela p = fun k => ((A.run (pre ++ c) t).stk k).take A.d := by
        funext k
        simp only [janela]
        rw [List.map_congr_left (g := fun i : Fin A.d => ((A.run (pre ++ c) t).stk k)[(i : ℕ)]?)
          (fun i _ => hval k i), map_finRange_val, tomaSome_celulas]
      have hcfg : A.run (pre ++ c) t = ⟨some l, v, (A.run (pre ++ c) t).stk⟩ := by
        rcases hc : A.run (pre ++ c) t with ⟨l', v', S⟩
        rw [hc] at hy hz
        simp only at hy hz
        rw [← hy, hz]
      have hstep : A.run (pre ++ c) (t + 1) =
          ⟨(stepAux (A.M l) v (A.janela p)).l, (stepAux (A.M l) v (A.janela p)).var,
            fun k => (stepAux (A.M l) v (A.janela p)).stk k ++
              ((A.run (pre ++ c) t).stk k).drop A.d⟩ := by
        rw [run_succ, hcfg, passoA_some, stepAux_topo _ v _ (h.prof_le l), hjan]
      obtain ⟨ℓ, hℓ, hτ⟩ := A.conseq_sat (h.labs_all _) (h.sts_all _) h.none_mem
        (fun k a ha => by
          rcases mem_stepAux (A.M l) v (A.janela p) k a ha with ha' | ha'
          · rw [hjan] at ha'
            exact (inv t).2 k a (List.mem_of_mem_take ha')
          · exact h.push_mem l k a ha')
        (fun k => by have := halt t htT.le k; omega) hstep C' hC'
      exact ⟨ℓ, List.mem_append_right _ hℓ, hτ⟩
    · push Not at hall
      obtain ⟨ℓ, hℓ, hτ⟩ := hall
      refine ⟨ℓ, List.mem_append_left _ hℓ, ?_⟩
      rw [A.antes_neg ℓ hℓ]
      simpa using hτ
  · -- (P)
    rw [fP, sat_flatMap]
    intro t _
    rw [sat_append, sat_append]
    by_cases hn : (A.run (pre ++ c) t).l = none
    · have hs : A.run (pre ++ c) (t + 1) = A.run (pre ++ c) t := by
        rw [run_succ, passoA_parada _ _ hn]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro C hC
        simp only [List.mem_singleton] at hC
        subst hC
        refine ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
        simp [τrun, hs, hn, getElem?_ix (h.labs_all none)]
      · intro C hC
        obtain ⟨jv, _, rfl⟩ := List.mem_map.mp hC
        by_cases hz : A.τrun (pre ++ c) (.z t jv) = true
        · exact ⟨(.z (t + 1) jv, true), by simp, by simpa [τrun, hs] using hz⟩
        · exact ⟨(.z t jv, false), by simp, by simpa using hz⟩
      · rw [sat_flatMap]; intro k _
        rw [sat_flatMap]; intro i _ C hC
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hC
        by_cases hxv : A.τrun (pre ++ c) (.x t k i a) = true
        · exact ⟨(.x (t + 1) k i a, true), by simp, by simpa [τrun, hs] using hxv⟩
        · exact ⟨(.x t k i a, false), by simp, by simpa using hxv⟩
    · have hy : A.τrun (pre ++ c) (.y t (ix A.labs none)) = false := by
        simp only [τrun, getElem?_ix (h.labs_all none), decide_eq_false_iff_not]
        intro e
        exact hn (Option.some.inj e).symm
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro C hC
        simp only [List.mem_singleton] at hC
        subst hC
        exact ⟨_, List.mem_cons_self .., hy⟩
      · intro C hC
        obtain ⟨jv, _, rfl⟩ := List.mem_map.mp hC
        exact ⟨_, List.mem_cons_self .., hy⟩
      · rw [sat_flatMap]; intro k _
        rw [sat_flatMap]; intro i _ C hC
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hC
        exact ⟨_, List.mem_cons_self .., hy⟩
  · -- (A)
    rw [fA]
    exact sat_par ⟨_, List.mem_singleton_self _, by simp [τrun, hl, getElem?_ix (h.labs_all none)]⟩
      ⟨_, List.mem_singleton_self _, by simp [τrun, hacc, getElem?_ix h.acc_mem]⟩

/-! ## Correção: toda atribuição que satisfaz o tableau lê uma execução real -/

omit [DecidableEq K] [Fintype K] in
theorem unit_true {τ : Var K → Bool} {φ : List (Cla K)} (hs : Sat τ φ) {v : Var K}
    (hm : [(v, true)] ∈ φ) : τ v = true := by
  obtain ⟨ℓ, hℓ, h⟩ := hs _ hm
  simp only [List.mem_singleton] at hℓ
  subst hℓ; exact h

omit [DecidableEq K] [Fintype K] in
theorem imp_true {τ : Var K → Bool} {φ : List (Cla K)} (hs : Sat τ φ) {u w : Var K}
    (hm : [(u, false), (w, true)] ∈ φ) (hu : τ u = true) : τ w = true := by
  obtain ⟨ℓ, hℓ, h⟩ := hs _ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl
  · simp [hu] at h
  · exact h

omit [DecidableEq K] [Fintype K] in
theorem imp2_true {τ : Var K → Bool} {φ : List (Cla K)} (hs : Sat τ φ) {u u' w : Var K}
    (hm : [(u, false), (u', false), (w, true)] ∈ φ) (hu : τ u = true) (hu' : τ u' = true) :
    τ w = true := by
  obtain ⟨ℓ, hℓ, h⟩ := hs _ hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl
  · simp [hu] at h
  · simp [hu'] at h
  · exact h

omit [DecidableEq K] in
theorem umSo_de_fE {τ : Var K → Bool} {T H : ℕ} (hs : Sat τ (A.fE T H)) {t : ℕ} (ht : t ≤ T) :
    Sat τ (umSo (A.rotulos t)) ∧ Sat τ (umSo (A.estados t)) ∧
      ∀ k i, i < H → Sat τ (umSo (A.celulas t k i)) := by
  rw [fE, sat_flatMap] at hs
  have h := hs t (List.mem_range.mpr (by omega))
  rw [sat_append, sat_append, sat_flatMap] at h
  refine ⟨h.1.1, h.1.2, fun k i hi => ?_⟩
  have h2 := h.2 k (mem_ks k)
  rw [sat_flatMap] at h2
  exact h2 i (List.mem_range.mpr hi)

theorem mem_fR {T H t jl jv : ℕ} {l : Λ} {v : σ} {p : A.Pat} (ht : t < T)
    (hjl : A.labs[jl]? = some (some l)) (hjv : A.sts[jv]? = some v) {C' : Cla K}
    (hC' : C' ∈ A.conseq H t (stepAux (A.M l) v (A.janela p))) :
    A.antes t jl jv p ++ C' ∈ A.fR T H := by
  have hjl' : jl < A.labs.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hjl; simp at hjl
  have hjv' : jv < A.sts.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hjv; simp at hjv
  simp only [fR, List.mem_flatMap, List.mem_range]
  refine ⟨t, ht, jl, hjl', jv, hjv', p, A.mem_pats p, ?_⟩
  simp only [hjl, hjv]
  exact List.mem_map.mpr ⟨C', hC', rfl⟩

/-- **Passo da correção**: se a linha `t` codifica a execução, a linha `t + 1` também. -/
theorem passo_correto {pre cands : List (Γ A.k₀)} {Q T H D : ℕ} {acc : Γ A.k₁}
    (h : A.Bom pre cands Q T H D acc) {x : List (Γ A.k₀)}
    (hx : ∀ a ∈ x, some a ∈ A.vals A.k₀) (hxl : x.length ≤ pre.length + Q)
    {τ : Var K → Bool} (hs : Sat τ (A.formula pre cands Q T H acc)) {t : ℕ} (ht : t < T)
    (hc : A.Cod τ H t (A.run x t)) : A.Cod τ H (t + 1) (A.run x (t + 1)) := by
  classical
  simp only [formula, sat_append] at hs
  obtain ⟨⟨⟨⟨hE, -⟩, hR⟩, hP⟩, -⟩ := hs
  obtain ⟨uL, uS, uC⟩ := A.umSo_de_fE hE (t := t + 1) (by omega)
  have inv := A.run_inv D h.emp_le (fun k a => some a ∈ A.vals k) h.push_mem x hx
  have hcel := A.celula_mem h hx
  have halt : ∀ k, ((A.run x t).stk k).length + A.d < H := by
    intro k
    have h1 := (inv t).1 k
    have h2 := h.altura
    have h3 : D * t ≤ D * T := Nat.mul_le_mul_left _ ht.le
    omega
  have hdH : A.d < H := by have := h.altura; omega
  obtain ⟨cL, cS, cC⟩ := hc
  -- a linha `t + 1` é forçada por um literal verdadeiro em cada grupo
  have fecha : ∀ (C' : Cfg Γ Λ σ),
      τ (.y (t + 1) (ix A.labs C'.l)) = true → τ (.z (t + 1) (ix A.sts C'.var)) = true →
      (∀ k i, i < H → τ (.x (t + 1) k i (ix (A.vals k) (C'.stk k)[i]?)) = true) →
      (∀ k (i : ℕ), (C'.stk k)[i]? ∈ A.vals k) → A.Cod τ H (t + 1) C' := by
    intro C' h1 h2 h3 h4
    exact ⟨forca_cod h.labs_nodup (h.labs_all _) uL h1,
      forca_cod h.sts_nodup (h.sts_all _) uS h2,
      fun k i j hi hj => forca_cod (h.vals_nodup k) (h4 k i) (uC k i hi) (h3 k i hi) j hj⟩
  rcases hcl : (A.run x t).l with _ | l
  · -- parada
    have hs' : A.run x (t + 1) = A.run x t := by rw [run_succ, passoA_parada _ _ hcl]
    have hy : τ (.y t (ix A.labs none)) = true := by
      rw [cL _ (ix_lt (h.labs_all none)), getElem?_ix (h.labs_all none), hcl]
    rw [fP, sat_flatMap] at hP
    have hPt := hP t (List.mem_range.mpr ht)
    rw [sat_append, sat_append] at hPt
    obtain ⟨⟨hP1, hP2⟩, hP3⟩ := hPt
    rw [hs']
    refine fecha _ ?_ ?_ ?_ (hcel t)
    · rw [hcl]; exact imp_true hP1 (List.mem_singleton_self _) hy
    · have hz : τ (.z t (ix A.sts (A.run x t).var)) = true := by
        rw [cS _ (ix_lt (h.sts_all _)), getElem?_ix (h.sts_all _)]
      exact imp2_true hP2 (List.mem_map.mpr ⟨_, List.mem_range.mpr (ix_lt (h.sts_all _)), rfl⟩) hy hz
    · intro k i hi
      have hxv : τ (.x t k i (ix (A.vals k) ((A.run x t).stk k)[i]?)) = true := by
        rw [cC k i _ hi (ix_lt (hcel t k i)), getElem?_ix (hcel t k i)]
      rw [sat_flatMap] at hP3
      have := hP3 k (mem_ks k)
      rw [sat_flatMap] at this
      exact imp2_true (this i (List.mem_range.mpr hi))
        (List.mem_map.mpr ⟨_, List.mem_range.mpr (ix_lt (hcel t k i)), rfl⟩) hy hxv
  · -- passo
    set S := (A.run x t).stk with hS
    set v := (A.run x t).var with hv
    let p : A.Pat := fun k i => ⟨ix (A.vals k) (S k)[(i : ℕ)]?, ix_lt (hcel t k i)⟩
    have hjan : A.janela p = fun k => (S k).take A.d := by
      funext k
      have hg : ∀ i : ℕ, (A.vals k)[ix (A.vals k) (S k)[i]?]'(ix_lt (hcel t k i)) = (S k)[i]? :=
        fun i => getElem_ix (hcel t k i)
      simp only [janela, p, hg]
      rw [map_finRange_val, tomaSome_celulas]
    have hcfg : A.run x t = ⟨some l, v, S⟩ := by
      rcases hc' : A.run x t with ⟨l', v', S'⟩
      rw [hc'] at hcl; simp only at hcl; subst hcl
      simp [hS, hv, hc']
    set r := stepAux (A.M l) v (A.janela p) with hr
    have hstep : A.run x (t + 1) = ⟨r.l, r.var, fun k => r.stk k ++ (S k).drop A.d⟩ := by
      rw [run_succ, hcfg, passoA_some, stepAux_topo _ v _ (h.prof_le l), hr, hjan]
    -- os antecedentes do padrão verdadeiro são falsos
    have hant : ∀ ℓ ∈ A.antes t (ix A.labs (some l)) (ix A.sts v) p, τ ℓ.1 ≠ ℓ.2 := by
      intro ℓ hℓ
      simp only [antes, List.mem_cons, List.mem_flatMap, List.mem_map] at hℓ
      rcases hℓ with rfl | rfl | ⟨k, -, i, -, rfl⟩
      · dsimp only
        have := (cL _ (ix_lt (h.labs_all (some l)))).mpr (by rw [getElem?_ix (h.labs_all _), hcl])
        simp [this]
      · dsimp only
        have := (cS _ (ix_lt (h.sts_all v))).mpr (by rw [getElem?_ix (h.sts_all _)])
        simp [this]
      · dsimp only
        have := (cC k i _ (by have := i.isLt; omega) (ix_lt (hcel t k i))).mpr
          (by rw [getElem?_ix (hcel t k i)])
        simp [p, hS, this]
    have hcons : ∀ C' ∈ A.conseq H t r, ∃ ℓ ∈ C', τ ℓ.1 = ℓ.2 := by
      intro C' hC'
      obtain ⟨ℓ, hℓ, hτ⟩ := hR _ (A.mem_fR (ht := ht) (getElem?_ix (h.labs_all _))
        (getElem?_ix (h.sts_all _)) hC')
      rcases List.mem_append.mp hℓ with hℓ | hℓ
      · exact absurd hτ (hant ℓ hℓ)
      · exact ⟨ℓ, hℓ, hτ⟩
    have unitc : ∀ w : Var K, [(w, true)] ∈ A.conseq H t r → τ w = true := by
      intro w hw
      obtain ⟨ℓ, hℓ, hτ⟩ := hcons _ hw
      simp only [List.mem_singleton] at hℓ; subst hℓ; exact hτ
    have hmem1 : ∀ k, [(Var.x (t + 1) k 0 0, true)] ∈ ([] : List (Cla K)) → False := by simp
    rw [hstep]
    refine fecha _ ?_ ?_ ?_ ?_
    · exact unitc _ (by simp [conseq])
    · exact unitc _ (by simp [conseq])
    · intro k i hi
      rcases Nat.lt_or_ge i (r.stk k).length with hiP | hiP
      · have e : (r.stk k ++ (S k).drop A.d)[i]? = (r.stk k)[i]? := List.getElem?_append_left hiP
        rw [e]
        exact unitc _ (by
          simp only [conseq, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
          exact Or.inr ⟨k, mem_ks k, Or.inl ⟨i, hiP, rfl⟩⟩)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hiP
        have e : (r.stk k ++ (S k).drop A.d)[(r.stk k).length + j]? = (S k)[A.d + j]? := by
          rw [List.getElem?_append_right (by omega), List.getElem?_drop]
          congr 1; omega
        rw [e]
        by_cases hdj : A.d + j < H
        · have hxv : τ (.x t k (A.d + j) (ix (A.vals k) (S k)[A.d + j]?)) = true := by
            rw [cC k _ _ hdj (ix_lt (hcel t k _)), getElem?_ix (hcel t k _)]
          obtain ⟨ℓ, hℓ, hτ⟩ := hcons [(.x t k (A.d + j) (ix (A.vals k) (S k)[A.d + j]?), false),
              (.x (t + 1) k ((r.stk k).length + j) (ix (A.vals k) (S k)[A.d + j]?), true)] (by
            simp only [conseq, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
              List.mem_filter]
            refine Or.inr ⟨k, mem_ks k, Or.inr ⟨j, ⟨by omega, by simpa using hi⟩, ?_⟩⟩
            simp only [hdj, ite_true]
            exact List.mem_map.mpr ⟨_, List.mem_range.mpr (ix_lt (hcel t k _)), rfl⟩)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
          rcases hℓ with rfl | rfl
          · simp [hxv] at hτ
          · exact hτ
        · have hn : (S k)[A.d + j]? = none :=
            List.getElem?_eq_none (by have := halt k; omega)
          rw [hn]
          exact unitc _ (by
            simp only [conseq, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range,
              List.mem_filter]
            refine Or.inr ⟨k, mem_ks k, Or.inr ⟨j, ⟨by omega, by simpa using hi⟩, ?_⟩⟩
            simp only [hdj, ite_false]
            exact List.mem_singleton_self _)
    · intro k i
      have := hcel (t + 1) k i
      rwa [hstep] at this

/-- **Base da correção**: a linha 0 de uma atribuição que satisfaz o tableau é a configuração
inicial com algum certificado `c` (até `Q` símbolos de `cands`). -/
theorem base_correto {pre cands : List (Γ A.k₀)} {Q T H D : ℕ} {acc : Γ A.k₁}
    (h : A.Bom pre cands Q T H D acc) {τ : Var K → Bool}
    (hs : Sat τ (A.formula pre cands Q T H acc)) :
    ∃ c : List (Γ A.k₀), c.length ≤ Q ∧ (∀ a ∈ c, a ∈ cands) ∧ A.Cod τ H 0 (A.init (pre ++ c)) := by
  classical
  simp only [formula, sat_append] at hs
  obtain ⟨⟨⟨⟨hE, hI⟩, -⟩, -⟩, -⟩ := hs
  obtain ⟨uL, uS, uC⟩ := A.umSo_de_fE hE (t := 0) (Nat.zero_le _)
  have hQH : pre.length + Q < H := by have := h.altura; omega
  -- valor forçado de cada célula da pilha de entrada
  have hval : ∀ i, i < H → ∃ w, w ∈ A.vals A.k₀ ∧ ∀ j, j < (A.vals A.k₀).length →
      (τ (.x 0 A.k₀ i j) = true ↔ (A.vals A.k₀)[j]? = some w) := by
    intro i hi
    obtain ⟨a, ha, hτ⟩ := umSo_alguma (uC A.k₀ i hi)
    simp only [celulas, List.length_map, List.length_range] at ha
    simp only [celulas, List.getElem_map, List.getElem_range] at hτ
    refine ⟨(A.vals A.k₀)[a], List.getElem_mem ha, ?_⟩
    refine forca_cod (h.vals_nodup _) (List.getElem_mem ha) (uC A.k₀ i hi) ?_
    rw [ix_getElem (h.vals_nodup _) ha]; exact hτ
  let g : ℕ → Option (Γ A.k₀) := fun i => if hi : i < H then Classical.choose (hval i hi) else none
  have hg : ∀ i (hi : i < H), g i ∈ A.vals A.k₀ ∧ ∀ j, j < (A.vals A.k₀).length →
      (τ (.x 0 A.k₀ i j) = true ↔ (A.vals A.k₀)[j]? = some (g i)) := by
    intro i hi
    simp only [g, hi, dite_true]
    exact Classical.choose_spec (hval i hi)
  have hgu : ∀ i (hi : i < H) (w : Option (Γ A.k₀)), w ∈ A.vals A.k₀ →
      τ (.x 0 A.k₀ i (ix (A.vals A.k₀) w)) = true → g i = w := by
    intro i hi w hw ht
    have := ((hg i hi).2 _ (ix_lt hw)).mp ht
    rw [getElem?_ix hw] at this
    exact (Option.some.inj this).symm
  have hgt : ∀ i (hi : i < H), τ (.x 0 A.k₀ i (ix (A.vals A.k₀) (g i))) = true := by
    intro i hi
    exact ((hg i hi).2 _ (ix_lt (hg i hi).1)).mpr (getElem?_ix (hg i hi).1)
  -- as cláusulas da linha inicial, por posição
  rw [fI, sat_append, sat_append] at hI
  obtain ⟨⟨hI0, hIk⟩, hIk₀⟩ := hI
  rw [sat_flatMap] at hIk₀
  have hpre : ∀ i, i < pre.length → g i = pre[i]? := by
    intro i hi
    have hiH : i < H := by omega
    have hm : pre[i]? ∈ A.vals A.k₀ := by
      rw [List.getElem?_eq_getElem hi]; exact h.pre_mem _ (List.getElem_mem hi)
    have := hIk₀ i (List.mem_range.mpr hiH)
    simp only [hi, ite_true] at this
    exact hgu i hiH _ hm (unit_true this (List.mem_singleton_self _))
  have hfora : ∀ i, i < H → pre.length + Q ≤ i → g i = none := by
    intro i hiH hi
    have := hIk₀ i (List.mem_range.mpr hiH)
    simp only [show ¬ i < pre.length by omega, show ¬ i < pre.length + Q by omega,
      ite_false] at this
    exact hgu i hiH _ (h.none_mem _) (unit_true this (List.mem_singleton_self _))
  have hjan : ∀ i, pre.length ≤ i → i < pre.length + Q →
      g i ∈ none :: cands.map some ∧ (i + 1 < pre.length + Q → g i = none → g (i + 1) = none) := by
    intro i h1 h2
    have hiH : i < H := by omega
    have := hIk₀ i (List.mem_range.mpr hiH)
    simp only [show ¬ i < pre.length by omega, h2, ite_false, ite_true] at this
    rw [sat_append] at this
    obtain ⟨hr, hc⟩ := this
    refine ⟨?_, fun hi1 hn => ?_⟩
    · by_contra hn
      have hmem : [(Var.x 0 A.k₀ i (ix (A.vals A.k₀) (g i)), false)] ∈
          ((List.range (A.vals A.k₀).length).filter (fun j =>
            (A.vals A.k₀).getD j none ∉ none :: cands.map some)).map
            (fun j => [(Var.x 0 A.k₀ i j, false)]) := by
        refine List.mem_map.mpr ⟨_, List.mem_filter.mpr ⟨List.mem_range.mpr (ix_lt (hg i hiH).1), ?_⟩, rfl⟩
        rw [List.getD_eq_getElem?_getD, getElem?_ix (hg i hiH).1]
        simpa using hn
      obtain ⟨ℓ, hℓ, hτ⟩ := hr _ hmem
      simp only [List.mem_singleton] at hℓ
      subst hℓ
      simp [hgt i hiH] at hτ
    · simp only [show i + 1 < H by omega, ite_true] at hc
      have hnt : τ (.x 0 A.k₀ i (ix (A.vals A.k₀) none)) = true := by rw [← hn]; exact hgt i hiH
      exact hgu (i + 1) (by omega) _ (h.none_mem _)
        (imp_true hc (List.mem_singleton_self _) hnt)
  -- o certificado
  let L : List (Option (Γ A.k₀)) := (List.range Q).map fun j => g (pre.length + j)
  have hLc : Contigua L := by
    intro j hj hn
    simp only [L, List.length_map, List.length_range] at hj
    simp only [L, List.getElem_map, List.getElem_range] at hn ⊢
    have := (hjan (pre.length + j) (by omega) (by omega)).2 (by omega) hn
    rwa [show pre.length + (j + 1) = pre.length + j + 1 by omega]
  refine ⟨tomaSome L, (length_tomaSome_le L).trans (by simp [L]), fun a ha => ?_, ?_⟩
  · have hm := mem_tomaSome ha
    obtain ⟨j, hj, hj'⟩ := List.mem_map.mp hm
    have hj := List.mem_range.mp hj
    have := (hjan (pre.length + j) (by omega) (by omega)).1
    rw [hj'] at this
    simpa using this
  · have hcel : ∀ i, i < H → (pre ++ tomaSome L)[i]? = g i := by
      intro i hi
      rcases Nat.lt_or_ge i pre.length with h1 | h1
      · rw [List.getElem?_append_left h1, hpre i h1]
      · rw [List.getElem?_append_right h1, tomaSome_getElem? L hLc]
        rcases Nat.lt_or_ge (i - pre.length) Q with h2 | h2
        · simp only [L, List.getElem?_map, List.getElem?_range h2, Option.map_some, Option.join_some]
          congr 1; omega
        · rw [hfora i hi (by omega)]
          simp [L, List.getElem?_eq_none (by simpa using h2 : (List.map (fun j => g (pre.length + j)) (List.range Q)).length ≤ i - pre.length)]
    refine ⟨?_, ?_, ?_⟩
    · have ht : τ (.y 0 (ix A.labs (some A.l₀))) = true := unit_true hI0 (by simp)
      intro j hj
      exact forca_cod h.labs_nodup (h.labs_all _) uL ht j hj
    · have ht : τ (.z 0 (ix A.sts A.v₀)) = true := unit_true hI0 (by simp)
      intro j hj
      exact forca_cod h.sts_nodup (h.sts_all _) uS ht j hj
    · intro k i j hi hj
      by_cases hk : k = A.k₀
      · subst hk
        rw [(hg i hi).2 j hj, init_stk_k₀, hcel i hi]
      · rw [init_stk_ne A _ hk]
        have ht : τ (.x 0 k i (ix (A.vals k) none)) = true := by
          rw [sat_flatMap] at hIk
          exact unit_true (hIk k (List.mem_filter.mpr ⟨mem_ks k, by simpa using hk⟩))
            (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
        simpa using forca_cod (h.vals_nodup k) (h.none_mem k) (uC k i hi) ht j hj

/-- **O tableau de Cook–Levin**: a fórmula é satisfatível exatamente quando algum certificado
`c` (até `Q` símbolos de `cands`) faz a execução acolchoada de `T` passos sobre `pre ++ c` parar
com `acc` no topo da pilha de saída. -/
theorem tableau_iff {pre cands : List (Γ A.k₀)} {Q T H D : ℕ} {acc : Γ A.k₁}
    (h : A.Bom pre cands Q T H D acc) :
    (∃ τ, Sat τ (A.formula pre cands Q T H acc)) ↔
      ∃ c : List (Γ A.k₀), c.length ≤ Q ∧ (∀ a ∈ c, a ∈ cands) ∧
        (A.run (pre ++ c) T).l = none ∧ ((A.run (pre ++ c) T).stk A.k₁)[0]? = some acc := by
  constructor
  · rintro ⟨τ, hs⟩
    obtain ⟨c, hcQ, hcc, h0⟩ := A.base_correto h hs
    have hx : ∀ a ∈ pre ++ c, some a ∈ A.vals A.k₀ := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact h.pre_mem a ha
      · exact h.cands_mem a (hcc a ha)
    have hxl : (pre ++ c).length ≤ pre.length + Q := by simp; omega
    have hcod : ∀ t, t ≤ T → A.Cod τ H t (A.run (pre ++ c) t) := by
      intro t
      induction t with
      | zero => intro _; rw [run_zero]; exact h0
      | succ t ih => intro ht; exact A.passo_correto h hx hxl hs (by omega) (ih (by omega))
    obtain ⟨cL, -, cC⟩ := hcod T le_rfl
    have hs' := hs
    simp only [formula, sat_append] at hs'
    obtain ⟨-, hA⟩ := hs'
    rw [fA] at hA
    have hy : τ (.y T (ix A.labs none)) = true := unit_true hA (by simp)
    have hx1 : τ (.x T A.k₁ 0 (ix (A.vals A.k₁) (some acc))) = true := unit_true hA (by simp)
    rw [cL _ (ix_lt (h.labs_all none)), getElem?_ix (h.labs_all none)] at hy
    rw [cC _ _ _ (by have := h.altura; omega) (ix_lt h.acc_mem), getElem?_ix h.acc_mem] at hx1
    exact ⟨c, hcQ, hcc, (Option.some.inj hy).symm, (Option.some.inj hx1).symm⟩
  · rintro ⟨c, hcQ, hcc, hl, hacc⟩
    exact ⟨_, A.completo h c hcQ hcc hl hacc⟩

end Tab

/-! ## Testes de sanidade: uma máquina que para na hora e aceita se o topo for `true` -/

namespace Teste

/-- Uma pilha de `Bool`, um rótulo, um estado; o programa só para. -/
def M₀ : Unit → Stmt (fun _ : Unit => Bool) Unit Unit := fun _ => .halt

def A₀ : Tab Unit (fun _ => Bool) Unit Unit where
  M := M₀
  k₀ := ()
  k₁ := ()
  l₀ := ()
  v₀ := ()
  labs := [some (), none]
  sts := [()]
  vals := fun _ => [none, some false, some true]
  d := 0

theorem bom₀ (cands : List Bool) : A₀.Bom [] cands 1 1 2 0 true where
  labs_nodup := by decide
  labs_all := by intro l; cases l <;> simp [A₀]
  sts_nodup := by decide
  sts_all := by intro v; simp [A₀]
  vals_nodup := fun _ => by simp [A₀]
  none_mem := fun _ => by simp [A₀]
  pre_mem := by simp
  cands_mem := by intro a _; cases a <;> simp [A₀]
  acc_mem := by simp [A₀]
  push_mem := by intro l k a h; simp [A₀, M₀, simbolos] at h
  prof_le := by intro l; simp [A₀, M₀, prof]
  emp_le := by intro l; simp [A₀, M₀, emp]
  altura := by simp [A₀]

/-- Com certificados em `{false, true}`, o tableau é satisfatível (certificado `[true]`). -/
theorem teste_aceita : ∃ τ, Sat τ (A₀.formula [] [false, true] 1 1 2 true) :=
  (A₀.tableau_iff (bom₀ _)).mpr ⟨[true], by simp, by simp, rfl, rfl⟩

/-- Com certificados só em `{false}`, nenhuma atribuição satisfaz o tableau. -/
theorem teste_recusa : ¬ ∃ τ, Sat τ (A₀.formula [] [false] 1 1 2 true) := by
  rw [A₀.tableau_iff (bom₀ _)]
  rintro ⟨c, hc, hcc, -, hacc⟩
  rcases c with _ | ⟨a, _ | ⟨b, c⟩⟩
  · exact absurd hacc (by decide)
  · have : a = false := by simpa using hcc
    subst this
    exact absurd hacc (by decide)
  · simp at hc

end Teste

end ClayPvsNPProof.ATK.CookLevinTableau

