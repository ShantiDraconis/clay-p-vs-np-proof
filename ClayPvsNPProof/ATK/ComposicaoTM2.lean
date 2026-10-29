-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/ComposicaoTM2.lean
-- (sha256 do original: afd2dad6b7a9cc25…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import Mathlib.Computability.TuringMachine.Computable

/-!
# Composição de máquinas `Turing.FinTM2` em tempo polinomial
-/

open Turing Computability StateTransition Function

namespace ClayPvsNPProof.ATK.ComposicaoTM2

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-! ### Iteração de `Option` sob uma simulação -/

theorem iterate_none {α : Type*} (f : α → Option α) (n : ℕ) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply]; exact ih

/-- Se `φ` comuta com os passos enquanto a máquina não parou, toda execução de `f` de `a` até
`b` em `n` passos vira uma execução de `g` de `φ a` até `φ b` em `n` passos. -/
theorem iterate_sim {α β : Type*} (f : α → Option α) (g : β → Option β) (φ : α → β)
    (hφ : ∀ a, f a ≠ none → g (φ a) = (f a).map φ) :
    ∀ (n : ℕ) (a b : α), (flip bind f)^[n] (some a) = some b →
      (flip bind g)^[n] (some (φ a)) = some (φ b) := by
  intro n
  induction n with
  | zero => intro a b h; simp only [iterate_zero, id] at h ⊢; rw [Option.some_inj.mp h]
  | succ n ih =>
    intro a b h
    rw [iterate_succ_apply] at h ⊢
    have hb : flip bind f (some a) = f a := rfl
    have hg : flip bind g (some (φ a)) = g (φ a) := rfl
    rw [hb] at h
    rw [hg]
    cases hfa : f a with
    | none => rw [hfa, iterate_none] at h; exact absurd h (by simp)
    | some a' =>
      rw [hfa] at h
      rw [hφ a (by rw [hfa]; simp), hfa, Option.map_some]
      exact ih a' b h


/-! ### A máquina composta -/

section Maquina

variable (M₁ M₂ : FinTM2)

/-- Pilhas: as de `M₁`, as de `M₂` e uma auxiliar. -/
abbrev Kc := M₁.K ⊕ M₂.K ⊕ Unit

/-- Alfabeto de cada pilha. -/
@[reducible] def Γc : Kc M₁ M₂ → Type
  | .inl k => M₁.Γ k
  | .inr (.inl k) => M₂.Γ k
  | .inr (.inr _) => Bool

/-- Rótulos: os de `M₁`, os de `M₂` e dois de transferência. -/
abbrev Λc := M₁.Λ ⊕ M₂.Λ ⊕ Bool

/-- Estado: o de `M₁`, o de `M₂` e um registrador de um bit opcional. -/
abbrev σc := M₁.σ × M₂.σ × Option Bool

abbrev Stc := Turing.TM2.Stmt (Γc M₁ M₂) (Λc M₁ M₂) (σc M₁ M₂)

/-- Rótulo da primeira transferência. -/
abbrev t₁ : Λc M₁ M₂ := .inr (.inr false)
/-- Rótulo da segunda transferência. -/
abbrev t₂ : Λc M₁ M₂ := .inr (.inr true)
/-- A pilha auxiliar. -/
abbrev aux : Kc M₁ M₂ := .inr (.inr ())

open Turing.TM2.Stmt

/-- Os comandos de `M₁` dentro da composta; `halt` vira um salto para a transferência. -/
def liftA : Turing.TM2.Stmt M₁.Γ M₁.Λ M₁.σ → Stc M₁ M₂
  | push k f q => push (.inl k) (fun v => f v.1) (liftA q)
  | peek k f q => peek (.inl k) (fun v o => (f v.1 o, v.2)) (liftA q)
  | pop k f q => pop (.inl k) (fun v o => (f v.1 o, v.2)) (liftA q)
  | load a q => load (fun v => (a v.1, v.2)) (liftA q)
  | branch f q₁ q₂ => branch (fun v => f v.1) (liftA q₁) (liftA q₂)
  | goto l => goto (fun v => .inl (l v.1))
  | halt => goto (fun _ => t₁ M₁ M₂)

/-- Os comandos de `M₂` dentro da composta. -/
def liftB : Turing.TM2.Stmt M₂.Γ M₂.Λ M₂.σ → Stc M₁ M₂
  | push k f q => push (.inr (.inl k)) (fun v => f v.2.1) (liftB q)
  | peek k f q => peek (.inr (.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftB q)
  | pop k f q => pop (.inr (.inl k)) (fun v o => (v.1, f v.2.1 o, v.2.2)) (liftB q)
  | load a q => load (fun v => (v.1, a v.2.1, v.2.2)) (liftB q)
  | branch f q₁ q₂ => branch (fun v => f v.2.1) (liftB q₁) (liftB q₂)
  | goto l => goto (fun v => .inr (.inl (l v.2.1)))
  | halt => halt

variable (e₁ : M₁.Γ M₁.k₁ → Bool) (e₂ : Bool → M₂.Γ M₂.k₀)

/-- Primeira transferência: saída de `M₁` → pilha auxiliar (inverte a ordem). -/
def transf₁ : Stc M₁ M₂ :=
  pop (Γ := Γc M₁ M₂) (Λ := Λc M₁ M₂) (σ := σc M₁ M₂) (Sum.inl M₁.k₁)
    (fun v o => (v.1, v.2.1, o.map e₁))
    (branch (fun v => v.2.2.isSome)
      (push (Γ := Γc M₁ M₂) (aux M₁ M₂) (fun v => (v.2.2.getD false : Bool))
        (load (fun v => (v.1, v.2.1, none)) (goto fun _ => t₁ M₁ M₂)))
      (goto fun _ => t₂ M₁ M₂))

/-- Segunda transferência: pilha auxiliar → entrada de `M₂` (restaura a ordem). -/
def transf₂ : Stc M₁ M₂ :=
  pop (Γ := Γc M₁ M₂) (Λ := Λc M₁ M₂) (σ := σc M₁ M₂) (aux M₁ M₂)
    (fun v (o : Option Bool) => (v.1, v.2.1, o))
    (branch (fun v => v.2.2.isSome)
      (push (Γ := Γc M₁ M₂) (Sum.inr (Sum.inl M₂.k₀)) (fun v => e₂ (v.2.2.getD false))
        (load (fun v => (v.1, v.2.1, none)) (goto fun _ => t₂ M₁ M₂)))
      (goto fun _ => .inr (.inl M₂.main)))

/-- O programa da composta. -/
def progc : Λc M₁ M₂ → Stc M₁ M₂
  | .inl l => liftA M₁ M₂ (M₁.m l)
  | .inr (.inl l) => liftB M₁ M₂ (M₂.m l)
  | .inr (.inr false) => transf₁ M₁ M₂ e₁
  | .inr (.inr true) => transf₂ M₁ M₂ e₂

/-- **A máquina composta**: roda `M₁`, transfere a saída para a entrada de `M₂`, roda `M₂`. -/
def compTM : FinTM2 where
  K := Kc M₁ M₂
  k₀ := .inl M₁.k₀
  k₁ := .inr (.inl M₂.k₁)
  Γ := Γc M₁ M₂
  Λ := Λc M₁ M₂
  main := .inl M₁.main
  σ := σc M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  m := progc M₁ M₂ e₁ e₂

end Maquina

/-! ### Fase 1: a composta simula `M₁` -/

section FaseA

variable (M₁ M₂ : FinTM2) (e₁ : M₁.Γ M₁.k₁ → Bool) (e₂ : Bool → M₂.Γ M₂.k₀)

abbrev Cfgc := Turing.TM2.Cfg (Γc M₁ M₂) (Λc M₁ M₂) (σc M₁ M₂)

/-- Pilhas da composta na fase 1: as de `M₁`; as demais vazias. -/
def stkA (S : ∀ k, List (M₁.Γ k)) : ∀ k : Kc M₁ M₂, List (Γc M₁ M₂ k)
  | .inl k => S k
  | .inr _ => []

/-- Rótulo da composta correspondente a um rótulo (ou à parada) de `M₁`. -/
def labA : Option M₁.Λ → Option (Λc M₁ M₂)
  | none => some (t₁ M₁ M₂)
  | some l => some (.inl l)

/-- Configuração da composta correspondente a uma de `M₁`. -/
def cfgA (r : M₂.σ × Option Bool) (c : Turing.TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : Cfgc M₁ M₂ :=
  ⟨labA M₁ M₂ c.l, (c.var, r), stkA M₁ M₂ c.stk⟩

theorem update_stkA (S : ∀ k, List (M₁.Γ k)) (k : M₁.K) (x : List (M₁.Γ k)) :
    update (stkA M₁ M₂ S) (Sum.inl k) x = stkA M₁ M₂ (update S k x) := by
  funext k'
  rcases k' with k' | k'
  · by_cases h : k' = k
    · subst h; simp [stkA]
    · rw [update_of_ne (by simpa using h)]
      simp only [stkA]
      rw [update_of_ne h]
  · rw [update_of_ne (by simp)]; rfl

theorem stepAux_liftA (q : Turing.TM2.Stmt M₁.Γ M₁.Λ M₁.σ) :
    ∀ (v : M₁.σ) (r : M₂.σ × Option Bool) (S : ∀ k, List (M₁.Γ k)),
      Turing.TM2.stepAux (liftA M₁ M₂ q) (v, r) (stkA M₁ M₂ S) =
        cfgA M₁ M₂ r (Turing.TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro v r S
    simp only [liftA, Turing.TM2.stepAux]
    rw [show stkA M₁ M₂ S (Sum.inl k) = S k from rfl, update_stkA]
    exact ih _ _ _
  | peek k f q ih =>
    intro v r S
    simp only [liftA, Turing.TM2.stepAux]
    exact ih _ _ _
  | pop k f q ih =>
    intro v r S
    simp only [liftA, Turing.TM2.stepAux]
    rw [show stkA M₁ M₂ S (Sum.inl k) = S k from rfl, update_stkA]
    exact ih _ _ _
  | load a q ih =>
    intro v r S
    simp only [liftA, Turing.TM2.stepAux]
    exact ih _ _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v r S
    simp only [liftA, Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ _ _
    · exact ih₁ _ _ _
  | goto l => intro v r S; rfl
  | halt => intro v r S; rfl

theorem step_cfgA (r : M₂.σ × Option Bool) (c : Turing.TM2.Cfg M₁.Γ M₁.Λ M₁.σ)
    (hc : Turing.TM2.step M₁.m c ≠ none) :
    Turing.TM2.step (progc M₁ M₂ e₁ e₂) (cfgA M₁ M₂ r c) =
      (Turing.TM2.step M₁.m c).map (cfgA M₁ M₂ r) := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd rfl hc
  · simp only [cfgA, labA, Turing.TM2.step, progc, Option.map_some]
    exact congrArg some (stepAux_liftA M₁ M₂ (M₁.m l) v r S)

theorem run_fase1 (r : M₂.σ × Option Bool) (n : ℕ) (a b : Turing.TM2.Cfg M₁.Γ M₁.Λ M₁.σ)
    (h : (flip bind (Turing.TM2.step M₁.m))^[n] (some a) = some b) :
    (flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂)))^[n] (some (cfgA M₁ M₂ r a)) =
      some (cfgA M₁ M₂ r b) :=
  iterate_sim _ _ _ (fun c hc => step_cfgA M₁ M₂ e₁ e₂ r c hc) n a b h

end FaseA

/-! ### Transferências -/

section Transf

variable (M₁ M₂ : FinTM2) (e₁ : M₁.Γ M₁.k₁ → Bool) (e₂ : Bool → M₂.Γ M₂.k₀)

/-- Pilhas durante as transferências: saída de `M₁`, auxiliar e entrada de `M₂`. -/
def stkT (L : List (M₁.Γ M₁.k₁)) (A : List Bool) (B : List (M₂.Γ M₂.k₀)) :
    ∀ k : Kc M₁ M₂, List (Γc M₁ M₂ k) :=
  update (update (update (fun k => ([] : List (Γc M₁ M₂ k))) (Sum.inl M₁.k₁) L) (aux M₁ M₂) A)
    (Sum.inr (Sum.inl M₂.k₀)) B

section
variable {M₁ M₂}

theorem ne₁ : (Sum.inl M₁.k₁ : Kc M₁ M₂) ≠ aux M₁ M₂ := by simp
theorem ne₂ : (Sum.inl M₁.k₁ : Kc M₁ M₂) ≠ Sum.inr (Sum.inl M₂.k₀) := by simp
theorem ne₃ : aux M₁ M₂ ≠ (Sum.inr (Sum.inl M₂.k₀) : Kc M₁ M₂) := by simp

theorem stkT_inl (L A B) : stkT M₁ M₂ L A B (Sum.inl M₁.k₁) = L := by
  simp only [stkT]
  rw [update_of_ne ne₂, update_of_ne ne₁, update_self]

theorem stkT_aux (L A B) : stkT M₁ M₂ L A B (aux M₁ M₂) = A := by
  simp only [stkT]
  rw [update_of_ne ne₃, update_self]

theorem stkT_in₂ (L A B) : stkT M₁ M₂ L A B (Sum.inr (Sum.inl M₂.k₀)) = B := by
  simp only [stkT]
  rw [update_self]

theorem upd_inl (L A B L') :
    update (stkT M₁ M₂ L A B) (Sum.inl M₁.k₁) L' = stkT M₁ M₂ L' A B := by
  simp only [stkT]
  rw [update_comm ne₂.symm, update_comm ne₁.symm, update_idem]

theorem upd_aux (L A B A') :
    update (stkT M₁ M₂ L A B) (aux M₁ M₂) A' = stkT M₁ M₂ L A' B := by
  simp only [stkT]
  rw [update_comm ne₃.symm, update_idem]

theorem upd_in₂ (L A B B') :
    update (stkT M₁ M₂ L A B) (Sum.inr (Sum.inl M₂.k₀)) B' = stkT M₁ M₂ L A B' := by
  simp only [stkT]
  rw [update_idem]
end

/-- Configuração de transferência. -/
def cfgT (l : Λc M₁ M₂) (s₁ : M₁.σ) (s₂ : M₂.σ) (L : List (M₁.Γ M₁.k₁)) (A : List Bool)
    (B : List (M₂.Γ M₂.k₀)) : Cfgc M₁ M₂ :=
  ⟨some l, (s₁, s₂, none), stkT M₁ M₂ L A B⟩

theorem transf₁_cons (s₁ s₂ a L A B) :
    Turing.TM2.step (progc M₁ M₂ e₁ e₂) (cfgT M₁ M₂ (t₁ M₁ M₂) s₁ s₂ (a :: L) A B) =
      some (cfgT M₁ M₂ (t₁ M₁ M₂) s₁ s₂ L (e₁ a :: A) B) := by
  simp only [cfgT, Turing.TM2.step, progc, transf₁, Turing.TM2.stepAux, stkT_inl,
    List.head?_cons, List.tail_cons, Option.map_some, Option.isSome_some, Bool.cond_true,
    Option.getD_some, upd_inl, stkT_aux, upd_aux]

theorem transf₁_nil (s₁ s₂ A B) :
    Turing.TM2.step (progc M₁ M₂ e₁ e₂) (cfgT M₁ M₂ (t₁ M₁ M₂) s₁ s₂ [] A B) =
      some (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] A B) := by
  simp only [cfgT, Turing.TM2.step, progc, transf₁, Turing.TM2.stepAux, stkT_inl,
    List.head?_nil, List.tail_nil, Option.map_none, Option.isSome_none, Bool.cond_false, upd_inl]

theorem run_transf₁ (s₁ s₂) : ∀ (L : List (M₁.Γ M₁.k₁)) (A B),
    (flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂)))^[L.length + 1]
        (some (cfgT M₁ M₂ (t₁ M₁ M₂) s₁ s₂ L A B)) =
      some (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] ((L.map e₁).reverse ++ A) B)
  | [], A, B => by
    rw [List.length_nil, zero_add, iterate_one]
    exact transf₁_nil M₁ M₂ e₁ e₂ s₁ s₂ A B
  | a :: L, A, B => by
    rw [List.length_cons, iterate_succ_apply]
    have h : flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂))
        (some (cfgT M₁ M₂ (t₁ M₁ M₂) s₁ s₂ (a :: L) A B)) =
        some (cfgT M₁ M₂ (t₁ M₁ M₂) s₁ s₂ L (e₁ a :: A) B) := transf₁_cons M₁ M₂ e₁ e₂ s₁ s₂ a L A B
    rw [h, run_transf₁ s₁ s₂ L (e₁ a :: A) B]
    simp

theorem transf₂_cons (s₁ s₂ b A B) :
    Turing.TM2.step (progc M₁ M₂ e₁ e₂) (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] (b :: A) B) =
      some (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] A (e₂ b :: B)) := by
  simp only [cfgT, Turing.TM2.step, progc, transf₂, Turing.TM2.stepAux, stkT_aux,
    List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
    Option.getD_some, upd_aux, stkT_in₂, upd_in₂]

theorem transf₂_nil (s₁ s₂ B) :
    Turing.TM2.step (progc M₁ M₂ e₁ e₂) (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] [] B) =
      some ⟨some (Sum.inr (Sum.inl M₂.main)), (s₁, s₂, none), stkT M₁ M₂ [] [] B⟩ := by
  simp only [cfgT, Turing.TM2.step, progc, transf₂, Turing.TM2.stepAux, stkT_aux,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false, upd_aux]

theorem run_transf₂ (s₁ s₂) : ∀ (A : List Bool) (B),
    (flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂)))^[A.length + 1]
        (some (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] A B)) =
      some ⟨some (Sum.inr (Sum.inl M₂.main)), (s₁, s₂, none),
        stkT M₁ M₂ [] [] ((A.map e₂).reverse ++ B)⟩
  | [], B => by
    rw [List.length_nil, zero_add, iterate_one]
    exact transf₂_nil M₁ M₂ e₁ e₂ s₁ s₂ B
  | b :: A, B => by
    rw [List.length_cons, iterate_succ_apply]
    have h : flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂))
        (some (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] (b :: A) B)) =
        some (cfgT M₁ M₂ (t₂ M₁ M₂) s₁ s₂ [] A (e₂ b :: B)) := transf₂_cons M₁ M₂ e₁ e₂ s₁ s₂ b A B
    rw [h, run_transf₂ s₁ s₂ A (e₂ b :: B)]
    simp

end Transf

/-! ### Fase 2: a composta simula `M₂` -/

section FaseB

variable (M₁ M₂ : FinTM2) (e₁ : M₁.Γ M₁.k₁ → Bool) (e₂ : Bool → M₂.Γ M₂.k₀)

/-- Pilhas da composta na fase 2: as de `M₂`; as demais vazias. -/
def stkB (S : ∀ k, List (M₂.Γ k)) : ∀ k : Kc M₁ M₂, List (Γc M₁ M₂ k)
  | .inl _ => []
  | .inr (.inl k) => S k
  | .inr (.inr _) => []

/-- Configuração da composta correspondente a uma de `M₂`. -/
def cfgB (s₁ : M₁.σ) (c : Turing.TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : Cfgc M₁ M₂ :=
  ⟨c.l.map (fun l => Sum.inr (Sum.inl l)), (s₁, c.var, none), stkB M₁ M₂ c.stk⟩

theorem update_stkB (S : ∀ k, List (M₂.Γ k)) (k : M₂.K) (x : List (M₂.Γ k)) :
    update (stkB M₁ M₂ S) (Sum.inr (Sum.inl k)) x = stkB M₁ M₂ (update S k x) := by
  funext k'
  rcases k' with k' | k' | k'
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [stkB]
    · rw [update_of_ne (by simpa using h)]
      simp only [stkB]
      rw [update_of_ne h]
  · rw [update_of_ne (by simp)]; rfl

theorem stepAux_liftB (q : Turing.TM2.Stmt M₂.Γ M₂.Λ M₂.σ) :
    ∀ (s₁ : M₁.σ) (v : M₂.σ) (S : ∀ k, List (M₂.Γ k)),
      Turing.TM2.stepAux (liftB M₁ M₂ q) (s₁, v, none) (stkB M₁ M₂ S) =
        cfgB M₁ M₂ s₁ (Turing.TM2.stepAux q v S) := by
  induction q with
  | push k f q ih =>
    intro s₁ v S
    simp only [liftB, Turing.TM2.stepAux]
    rw [show stkB M₁ M₂ S (Sum.inr (Sum.inl k)) = S k from rfl, update_stkB]
    exact ih _ _ _
  | peek k f q ih =>
    intro s₁ v S
    simp only [liftB, Turing.TM2.stepAux]
    exact ih _ _ _
  | pop k f q ih =>
    intro s₁ v S
    simp only [liftB, Turing.TM2.stepAux]
    rw [show stkB M₁ M₂ S (Sum.inr (Sum.inl k)) = S k from rfl, update_stkB]
    exact ih _ _ _
  | load a q ih =>
    intro s₁ v S
    simp only [liftB, Turing.TM2.stepAux]
    exact ih _ _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro s₁ v S
    simp only [liftB, Turing.TM2.stepAux]
    cases f v
    · exact ih₂ _ _ _
    · exact ih₁ _ _ _
  | goto l => intro s₁ v S; rfl
  | halt => intro s₁ v S; rfl

theorem step_cfgB (s₁ : M₁.σ) (c : Turing.TM2.Cfg M₂.Γ M₂.Λ M₂.σ)
    (hc : Turing.TM2.step M₂.m c ≠ none) :
    Turing.TM2.step (progc M₁ M₂ e₁ e₂) (cfgB M₁ M₂ s₁ c) =
      (Turing.TM2.step M₂.m c).map (cfgB M₁ M₂ s₁) := by
  rcases c with ⟨_ | l, v, S⟩
  · exact absurd rfl hc
  · simp only [cfgB, Option.map_some, Turing.TM2.step, progc]
    exact congrArg some (stepAux_liftB M₁ M₂ (M₂.m l) s₁ v S)

theorem run_fase2 (s₁ : M₁.σ) (n : ℕ) (a b : Turing.TM2.Cfg M₂.Γ M₂.Λ M₂.σ)
    (h : (flip bind (Turing.TM2.step M₂.m))^[n] (some a) = some b) :
    (flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂)))^[n] (some (cfgB M₁ M₂ s₁ a)) =
      some (cfgB M₁ M₂ s₁ b) :=
  iterate_sim _ _ _ (fun c hc => step_cfgB M₁ M₂ e₁ e₂ s₁ c hc) n a b h

end FaseB

/-! ### Colagem das fases -/

section Cola

variable (M₁ M₂ : FinTM2) (e₁ : M₁.Γ M₁.k₁ → Bool) (e₂ : Bool → M₂.Γ M₂.k₀)

theorem initList_comp (x : List (M₁.Γ M₁.k₀)) :
    initList (compTM M₁ M₂ e₁ e₂) x = cfgA M₁ M₂ (M₂.initialState, none) (initList M₁ x) := by
  simp only [initList, cfgA, labA, compTM]
  congr 1
  funext k
  rcases k with k | k
  · by_cases h : k = M₁.k₀
    · subst h; simp [stkA]; rfl
    · simp [stkA, h]
  · simp [stkA]

theorem haltList_fase1 (y : List (M₁.Γ M₁.k₁)) :
    cfgA M₁ M₂ (M₂.initialState, none) (haltList M₁ y) =
      cfgT M₁ M₂ (t₁ M₁ M₂) M₁.initialState M₂.initialState y [] [] := by
  simp only [cfgA, labA, haltList, cfgT]
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = M₁.k₁
    · subst h; simp only [stkA]; rw [stkT_inl]; simp
    · simp only [stkA, h, ↓reduceDIte]
      simp only [stkT]
      rw [update_of_ne (by simp), update_of_ne (by simp), update_of_ne (by simpa using h)]
  · simp only [stkA]
    by_cases h : k = M₂.k₀
    · subst h; rw [stkT_in₂]
    · simp only [stkT]
      rw [update_of_ne (by simpa using h), update_of_ne (by simp), update_of_ne (by simp)]
  · simp only [stkA]
    cases k; rw [stkT_aux]

theorem initList_fase2 (B : List (M₂.Γ M₂.k₀)) :
    (⟨some (Sum.inr (Sum.inl M₂.main)), (M₁.initialState, M₂.initialState, none),
        stkT M₁ M₂ [] [] B⟩ : Cfgc M₁ M₂) = cfgB M₁ M₂ M₁.initialState (initList M₂ B) := by
  simp only [cfgB, initList, Option.map_some]
  congr 1
  funext k
  rcases k with k | k | k
  · simp only [stkB]
    by_cases h : k = M₁.k₁
    · subst h; rw [stkT_inl]
    · simp only [stkT]
      rw [update_of_ne (by simp), update_of_ne (by simp), update_of_ne (by simpa using h)]
  · simp only [stkB]
    by_cases h : k = M₂.k₀
    · subst h; rw [stkT_in₂]; simp
    · simp only [h, ↓reduceDIte]
      simp only [stkT]
      rw [update_of_ne (by simpa using h), update_of_ne (by simp), update_of_ne (by simp)]
  · simp only [stkB]
    cases k; rw [stkT_aux]

theorem haltList_comp (z : List (M₂.Γ M₂.k₁)) :
    cfgB M₁ M₂ M₁.initialState (haltList M₂ z) = haltList (compTM M₁ M₂ e₁ e₂) z := by
  simp only [cfgB, haltList, compTM, Option.map_none]
  congr 1
  funext k
  rcases k with k | k | k
  · simp [stkB]
  · by_cases h : k = M₂.k₁
    · subst h; simp [stkB]; rfl
    · simp [stkB, h]
  · simp [stkB]

end Cola

/-! ### Execução completa da composta -/

section Execucao

variable (M₁ M₂ : FinTM2) (e₁ : M₁.Γ M₁.k₁ → Bool) (e₂ : Bool → M₂.Γ M₂.k₀)

/-- **Execução da composta**: `M₁` leva `x` a `y` em `n₁` passos, `M₂` leva `y` (convertida) a
`z` em `n₂` passos; a composta leva `x` a `z` em `n₂ + (|y| + 1) + (|y| + 1) + n₁` passos. -/
theorem run_comp (x : List (M₁.Γ M₁.k₀)) (y : List (M₁.Γ M₁.k₁)) (z : List (M₂.Γ M₂.k₁))
    (n₁ n₂ : ℕ)
    (h₁ : (flip bind (Turing.TM2.step M₁.m))^[n₁] (some (initList M₁ x)) = some (haltList M₁ y))
    (h₂ : (flip bind (Turing.TM2.step M₂.m))^[n₂] (some (initList M₂ ((y.map e₁).map e₂))) =
      some (haltList M₂ z)) :
    (flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂)))^[n₂ + ((y.length + 1) + ((y.length + 1) + n₁))]
        (some (initList (compTM M₁ M₂ e₁ e₂) x)) = some (haltList (compTM M₁ M₂ e₁ e₂) z) := by
  have s1 : (flip bind (Turing.TM2.step (progc M₁ M₂ e₁ e₂)))^[n₁]
      (some (initList (compTM M₁ M₂ e₁ e₂) x)) =
      some (cfgT M₁ M₂ (t₁ M₁ M₂) M₁.initialState M₂.initialState y [] []) := by
    have := run_fase1 M₁ M₂ e₁ e₂ (M₂.initialState, none) n₁ _ _ h₁
    rw [← haltList_fase1]
    rw [initList_comp]
    exact this
  have s2 := run_transf₁ M₁ M₂ e₁ e₂ M₁.initialState M₂.initialState y [] []
  have s3 := run_transf₂ M₁ M₂ e₁ e₂ M₁.initialState M₂.initialState ((y.map e₁).reverse ++ []) []
  have hA : ((y.map e₁).reverse ++ []).length = y.length := by simp
  have hB : (((y.map e₁).reverse ++ []).map e₂).reverse ++ [] = (y.map e₁).map e₂ := by
    simp [List.map_reverse]
  rw [hA, hB, initList_fase2] at s3
  have s4 := run_fase2 M₁ M₂ e₁ e₂ M₁.initialState n₂ _ _ h₂
  rw [haltList_comp M₁ M₂ e₁ e₂] at s4
  rw [iterate_add_apply _ n₂ ((y.length + 1) + ((y.length + 1) + n₁)),
    iterate_add_apply _ (y.length + 1) ((y.length + 1) + n₁),
    iterate_add_apply _ (y.length + 1) n₁, s1, s2, s3, s4]
  rfl

end Execucao

/-! ### A saída não cresce mais que um número fixo de símbolos por passo -/

section Tamanho

open Turing.TM2.Stmt

variable {K : Type*} [DecidableEq K] [Fintype K] {Γ : K → Type*} {Λ σ : Type*}

/-- Máximo de `push` executados por um comando. -/
def pushes : Turing.TM2.Stmt Γ Λ σ → ℕ
  | push _ _ q => pushes q + 1
  | peek _ _ q => pushes q
  | pop _ _ q => pushes q
  | load _ q => pushes q
  | branch _ q₁ q₂ => max (pushes q₁) (pushes q₂)
  | goto _ => 0
  | halt => 0

/-- Tamanho total das pilhas. -/
def tam (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

theorem tam_update (S : ∀ k, List (Γ k)) (k : K) (x : List (Γ k)) :
    tam (update S k x) + (S k).length = tam S + x.length := by
  unfold tam
  have h : (fun k' => (update S k x k').length) = update (fun k' => (S k').length) k x.length := by
    funext k'
    by_cases hk : k' = k
    · subst hk; simp
    · simp [update_of_ne hk]
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ k)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  ring

theorem tam_stepAux (q : Turing.TM2.Stmt Γ Λ σ) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)), tam (Turing.TM2.stepAux q v S).stk ≤ tam S + pushes q := by
  induction q with
  | push k f q ih =>
    intro v S
    simp only [Turing.TM2.stepAux, pushes]
    have h1 := ih (v) (update S k (f v :: S k))
    have h2 := tam_update S k (f v :: S k)
    simp only [List.length_cons] at h2
    omega
  | peek k f q ih => intro v S; exact ih _ _
  | pop k f q ih =>
    intro v S
    simp only [Turing.TM2.stepAux, pushes]
    have h1 := ih (f v (S k).head?) (update S k (S k).tail)
    have h2 := tam_update S k (S k).tail
    have h3 : (S k).tail.length ≤ (S k).length := by simp
    omega
  | load a q ih => intro v S; exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    intro v S
    simp only [Turing.TM2.stepAux, pushes]
    cases f v
    · exact (ih₂ v S).trans (by omega)
    · exact (ih₁ v S).trans (by omega)
  | goto l => intro v S; simp [Turing.TM2.stepAux]
  | halt => intro v S; simp [Turing.TM2.stepAux]

variable [Fintype Λ]

/-- Máximo de `push` por passo de um programa. -/
def pushMax (m : Λ → Turing.TM2.Stmt Γ Λ σ) : ℕ := Finset.univ.sup fun l => pushes (m l)

theorem tam_step (m : Λ → Turing.TM2.Stmt Γ Λ σ) (c c' : Turing.TM2.Cfg Γ Λ σ)
    (h : Turing.TM2.step m c = some c') : tam c'.stk ≤ tam c.stk + pushMax m := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [Turing.TM2.step] at h
  · simp only [Turing.TM2.step, Option.some.injEq] at h
    subst h
    exact (tam_stepAux (m l) v S).trans
      (Nat.add_le_add_left (Finset.le_sup (f := fun l => pushes (m l)) (Finset.mem_univ l)) _)

theorem tam_iterate (m : Λ → Turing.TM2.Stmt Γ Λ σ) :
    ∀ (n : ℕ) (a b : Turing.TM2.Cfg Γ Λ σ),
      (flip bind (Turing.TM2.step m))^[n] (some a) = some b → tam b.stk ≤ tam a.stk + n * pushMax m := by
  intro n
  induction n with
  | zero => intro a b h; simp only [iterate_zero, id, Option.some.injEq] at h; subst h; simp
  | succ n ih =>
    intro a b h
    rw [iterate_succ_apply] at h
    have hb : flip bind (Turing.TM2.step m) (some a) = Turing.TM2.step m a := rfl
    rw [hb] at h
    cases ha : Turing.TM2.step m a with
    | none => rw [ha, iterate_none] at h; exact absurd h (by simp)
    | some a' =>
      rw [ha] at h
      have h1 := tam_step m a a' ha
      have h2 := ih a' b h
      calc tam b.stk ≤ tam a'.stk + n * pushMax m := h2
        _ ≤ tam a.stk + pushMax m + n * pushMax m := by omega
        _ = tam a.stk + (n + 1) * pushMax m := by ring

end Tamanho

theorem tam_initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tam (initList tm s).stk = s.length := by
  unfold tam
  rw [Finset.sum_eq_single tm.k₀]
  · simp [initList]
  · intro k _ hk; simp [initList, hk]
  · simp

theorem tam_haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tam (haltList tm s).stk = s.length := by
  unfold tam
  rw [Finset.sum_eq_single tm.k₁]
  · simp [haltList]
  · intro k _ hk; simp [haltList, hk]
  · simp

/-- **Cota da saída**: se `tm` leva `s` a `s'` em `n` passos, `|s'| ≤ |s| + n · pushMax`. -/
theorem saida_le (tm : FinTM2) (s : List (tm.Γ tm.k₀)) (s' : List (tm.Γ tm.k₁)) (n : ℕ)
    (h : (flip bind (Turing.TM2.step tm.m))^[n] (some (initList tm s)) = some (haltList tm s')) :
    s'.length ≤ s.length + n * pushMax tm.m := by
  have := tam_iterate tm.m n _ _ h
  rwa [tam_initList, tam_haltList] at this

/-- Avaliação de polinômio com coeficientes naturais é monótona. -/
theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c => simp only [Polynomial.eval_monomial]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-! ### O teorema de composição -/

section Teorema

variable {α β γ αΓ γΓ : Type} {ea : α → List αΓ} {eb : β → List Bool} {ec : γ → List γΓ}
  {f : α → β} {g : β → γ}

/-- Polinômio que majora o tamanho da saída de `hf`. -/
noncomputable def cotaSaida (hf : TM2ComputableInPolyTime ea eb f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (pushMax hf.tm.m) * hf.time

/-- **Composição em tempo polinomial**: se `f` e `g` são computáveis por `FinTM2` em tempo
polinomial (com a codificação intermediária `eb` sobre `Bool`), `g ∘ f` também é. -/
noncomputable def comp (hf : TM2ComputableInPolyTime ea eb f) (hg : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (g ∘ f) where
  tm := compTM hf.tm hg.tm hf.outputAlphabet hg.inputAlphabet.symm
  inputAlphabet := hf.inputAlphabet
  outputAlphabet := hg.outputAlphabet
  time := hg.time.comp (cotaSaida hf) + 2 * cotaSaida hf + 2 + hf.time
  outputsFun a := by
    obtain ⟨⟨n₁, h₁⟩, hn₁⟩ := hf.outputsFun a
    obtain ⟨⟨n₂, h₂⟩, hn₂⟩ := hg.outputsFun (f a)
    replace hn₁ : n₁ ≤ hf.time.eval (ea a).length := hn₁
    replace hn₂ : n₂ ≤ hg.time.eval (eb (f a)).length := hn₂
    set y := List.map hf.outputAlphabet.invFun (eb (f a)) with hy
    have hmid : (y.map hf.outputAlphabet).map hg.inputAlphabet.symm =
        List.map hg.inputAlphabet.invFun (eb (f a)) := by
      simp [hy, List.map_map]
    have h₁' : (flip bind (Turing.TM2.step hf.tm.m))^[n₁]
        (some (initList hf.tm (List.map hf.inputAlphabet.invFun (ea a)))) =
        some (haltList hf.tm y) := by
      simp only [FinTM2.step, Option.map_some] at h₁; exact h₁
    have h₂' : (flip bind (Turing.TM2.step hg.tm.m))^[n₂]
        (some (initList hg.tm ((y.map hf.outputAlphabet).map hg.inputAlphabet.symm))) =
        some (haltList hg.tm (List.map hg.outputAlphabet.invFun (ec (g (f a))))) := by
      rw [hmid]; simp only [FinTM2.step, Option.map_some] at h₂; exact h₂
    have hrun := run_comp hf.tm hg.tm hf.outputAlphabet hg.inputAlphabet.symm _ y _ n₁ n₂ h₁' h₂'
    have hy_le : y.length ≤ (cotaSaida hf).eval (ea a).length := by
      have := saida_le hf.tm _ y n₁ h₁'
      simp only [List.length_map] at this
      simp only [cotaSaida, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      have h3 : n₁ * pushMax hf.tm.m ≤ pushMax hf.tm.m * hf.time.eval (ea a).length := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ hn₁
      omega
    refine ⟨⟨n₂ + ((y.length + 1) + ((y.length + 1) + n₁)), ?_⟩, ?_⟩
    · exact hrun
    · have hyb : y.length = (eb (f a)).length := by simp [hy]
      have h2b : n₂ ≤ hg.time.eval ((cotaSaida hf).eval (ea a).length) := by
        refine hn₂.trans (eval_mono _ ?_)
        rw [← hyb]; exact hy_le
      simp only [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
        Polynomial.eval_ofNat]
      omega

end Teorema

end ClayPvsNPProof.ATK.ComposicaoTM2

