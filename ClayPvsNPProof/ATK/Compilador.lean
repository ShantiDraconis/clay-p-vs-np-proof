-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/Compilador.lean
-- (sha256 do original: a1b3c132b76ddd72…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.Fragmentos
import ClayPvsNPProof.ATK.LigacaoPNP

/-!
# ATK — Ponte B4, marco M2d (parte 1b): um compilador verificado de laços para `FinTM2`

Uma linguagem de laços sobre registradores unários (`Cmd`: `emit`, `emitU`, `zero`, `inc`,
`add`, `lenIn`, `seq`, `forU`, `forBits`), com semântica `sem w c E` (novo ambiente e saída) e
custo `custo w c E`.

* `comp`: compila para fragmentos sobre pilhas `Pilha R A` (entrada, saída, auxiliar, cópia da
  entrada, registradores e contadores de laço);
* **`comp_ok`**: para programas bem formados (`WF`), o código compilado vai do estado que codifica
  `E` ao estado com `(sem w c E).1` nos registradores e `(sem w c E).2` acrescentado à saída, em
  exatamente `custo w c E` passos;
* `maq` / **`maq_run`**: a `FinTM2` completa, com limpeza no fim, parte de `initList w` e para em
  `haltList (sem w c 0).2`;
* **`computavel`**: se o custo total é cotado por um polinômio no tamanho da entrada, a função
  `w ↦ (sem w c 0).2` é `TM2ComputableInPolyTime`;
* sanidade: o comprimento da entrada em unário é computável em tempo `≤ 15 n + 9`.

É a ferramenta para o marco M2d: a redução de Cook–Levin (`ClayPvsNPProof.ATK.CookLevinReducao`) escrita como
programa de laços, com custo cotado, em `ClayPvsNPProof.ATK.CookLevinGerador` e `ClayPvsNPProof.ATK.CookLevinNP`. Nada aqui
decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.Compilador

open Turing Turing.TM2 Function ClayPvsNPProof.ATK.Fragmentos

/-- As pilhas da máquina compilada: entrada, saída (invertida), saída final, auxiliar, cópia da
entrada, registradores unários e contadores de laço. -/
inductive Pilha (R A : ℕ) where
  | inp | out | fin | tmp | bak
  | reg (r : Fin R)
  | aux (a : Fin A)
  deriving DecidableEq, Fintype

variable {R A : ℕ}

abbrev Fr (R A : ℕ) := Frag (Pilha R A) (fun _ => Bool) (Option Bool)

abbrev Stk (R A : ℕ) := Pilha R A → List Bool

/-! ### Emitir uma cadeia constante -/

def pushesOut : List Bool → Stmt (fun _ : Pilha R A => Bool) Unit (Option Bool)
  | [] => .load (fun _ => none) (.goto fun _ => ())
  | b :: s => .push .out (fun _ => b) (pushesOut s)

theorem stepAux_pushesOut : ∀ (s : List Bool) (v : Option Bool) (S : Stk R A),
    stepAux (pushesOut s) v S = ⟨some (), none, update S .out (s.reverse ++ S .out)⟩
  | [], v, S => by simp [pushesOut, stepAux]
  | b :: s, v, S => by
    simp only [pushesOut, stepAux]
    rw [stepAux_pushesOut s]
    simp [update_idem]

def emitF (s : List Bool) : Fr R A := atom (pushesOut s)

theorem faz_emit (s : List Bool) (v : Option Bool) (S : Stk R A) :
    Faz (emitF s) v S none (update S .out (s.reverse ++ S .out)) 1 :=
  faz_atom (stepAux_pushesOut s v S)

/-! ### Mover uma pilha para outras -/

def pushesBit : List (Pilha R A) → Stmt (fun _ : Pilha R A => Bool) Unit (Option Bool)
  | [] => .goto fun _ => ()
  | d :: ds => .push d (fun v => v.getD false) (pushesBit ds)

theorem stepAux_pushesBit : ∀ (ds : List (Pilha R A)), ds.Nodup → ∀ (a : Bool) (S : Stk R A),
    stepAux (pushesBit ds) (some a) S = ⟨some (), some a, fun k => if k ∈ ds then a :: S k else S k⟩
  | [], _, a, S => by simp [pushesBit, stepAux]
  | d :: ds, hnd, a, S => by
    simp only [pushesBit, stepAux]
    rw [stepAux_pushesBit ds (List.nodup_cons.mp hnd).2]
    have hd := (List.nodup_cons.mp hnd).1
    congr 1
    funext k
    by_cases hk : k = d
    · subst hk; simp [hd]
    · simp [hk]

/-- Esvazia `src`, empilhando cada elemento em todas as pilhas de `dsts`. -/
def mover (src : Pilha R A) (dsts : List (Pilha R A)) : Fr R A :=
  laco src (fun _ o => o) Option.isSome (atom (pushesBit dsts))

/-- Estado depois de mover `j` elementos de `L = S src`. -/
def mv (S : Stk R A) (src : Pilha R A) (dsts : List (Pilha R A)) (j : ℕ) : Stk R A :=
  fun k => if k = src then (S src).drop j else if k ∈ dsts then ((S src).take j).reverse ++ S k else S k

theorem faz_mover {src : Pilha R A} {dsts : List (Pilha R A)} (hsrc : src ∉ dsts)
    (hnd : dsts.Nodup) (v : Option Bool) (S : Stk R A) :
    Faz (mover src dsts) v S none (mv S src dsts (S src).length) (2 * (S src).length + 1) := by
  have h0 : mv S src dsts 0 = S := by
    funext k; simp only [mv, List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append]
    split_ifs with h <;> simp [h]
  have key := faz_laco (k := src) (rd := fun _ o => o) (c := Option.isSome)
    (B := atom (pushesBit dsts)) (fun j => mv S src dsts j)
    (fun j => if j = 0 then v else some ((S src).getD (j - 1) false)) (fun _ => 1)
    (S src).length 0
    (fun j _ hj => by
      simp only [zero_add] at hj
      refine ⟨(S src)[j], (S src).drop (j + 1), ?_, rfl, ?_⟩
      · simp only [mv, ite_true]
        exact List.drop_eq_getElem_cons hj
      · apply faz_atom
        rw [stepAux_pushesBit dsts hnd]
        simp only [Nat.add_sub_cancel, Nat.succ_ne_zero, ite_false, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hj, Option.getD_some]
        congr 1
        funext k
        by_cases hk : k = src
        · subst hk
          rw [ite_eq_right hsrc, update_self]
          show _ = if k = k then (S k).drop (j + 1) else _
          rw [ite_eq_left rfl]
        · rw [update_of_ne hk]
          by_cases hkd : k ∈ dsts
          · rw [ite_eq_left hkd]
            unfold mv
            simp only [ite_eq_right hk, ite_eq_left hkd]
            rw [List.take_add_one, List.getElem?_eq_getElem hj]
            simp only [Option.toList_some, List.reverse_append, List.reverse_singleton,
              List.cons_append, List.nil_append]
          · rw [ite_eq_right hkd]
            show (if k = src then _ else if k ∈ dsts then _ else _) =
              (if k = src then _ else if k ∈ dsts then _ else _)
            rw [ite_eq_right hk, ite_eq_right hkd, ite_eq_right hk, ite_eq_right hkd])
    (by simp [mv]) rfl
  simp only [zero_add, h0, Finset.sum_const, Finset.card_range, smul_eq_mul] at key
  convert key using 2
  all_goals first | rfl | exact (ite_eq_left trivial).symm | rw [mul_comm]


/-! ## A linguagem de laços -/

/-- Programas: registradores unários `Fin R`, saída em bits, a entrada `w` só para leitura. -/
inductive Cmd (R : ℕ) where
  | emit (s : List Bool)
  | emitU (x : Fin R) (s : List Bool)
  | zero (x : Fin R)
  | inc (x : Fin R)
  | add (x y : Fin R)
  | lenIn (x : Fin R)
  | seq (c₁ c₂ : Cmd R)
  | forU (x y : Fin R) (body : Cmd R)
  | forBits (b₀ b₁ : Cmd R)

abbrev Env (R : ℕ) := Fin R → ℕ

/-- Repetir `m` vezes: roda `f`, depois soma 1 ao registrador `y`. -/
def semFor {R : ℕ} (f : Env R → Env R × List Bool) (y : Fin R) : ℕ → Env R → Env R × List Bool
  | 0, E => (E, [])
  | m + 1, E =>
    let r₁ := f E
    let r₂ := semFor f y m (update r₁.1 y (r₁.1 y + 1))
    (r₂.1, r₁.2 ++ r₂.2)

/-- Para cada bit da lista: roda `f₀` ou `f₁`. -/
def semBits {R : ℕ} (f₀ f₁ : Env R → Env R × List Bool) : List Bool → Env R → Env R × List Bool
  | [], E => (E, [])
  | b :: bs, E =>
    let r₁ := (if b then f₁ else f₀) E
    let r₂ := semBits f₀ f₁ bs r₁.1
    (r₂.1, r₁.2 ++ r₂.2)

/-- **Semântica**: novo ambiente e saída emitida, com a entrada `w`. -/
def sem {R : ℕ} (w : List Bool) : Cmd R → Env R → Env R × List Bool
  | .emit s, E => (E, s)
  | .emitU x s, E => (E, (List.replicate (E x) s).flatten)
  | .zero x, E => (update E x 0, [])
  | .inc x, E => (update E x (E x + 1), [])
  | .add x y, E => (update E x (E x + E y), [])
  | .lenIn x, E => (update E x (E x + w.length), [])
  | .seq c₁ c₂, E =>
    let r₁ := sem w c₁ E
    let r₂ := sem w c₂ r₁.1
    (r₂.1, r₁.2 ++ r₂.2)
  | .forU x y body, E => semFor (sem w body) y (E x) (update E y 0)
  | .forBits b₀ b₁, E => semBits (sem w b₀) (sem w b₁) w E


/-! ## O compilador -/

section compilador

variable {R A : ℕ}

def auxS (δ : ℕ) : Pilha R A := if h : δ < A then .aux ⟨δ, h⟩ else .tmp

def rdO : Option Bool → Option Bool → Option Bool := fun _ o => o

def stmtInc (x : Fin R) : Stmt (fun _ : Pilha R A => Bool) Unit (Option Bool) :=
  .push (.reg x) (fun _ => true) (.load (fun _ => none) (.goto fun _ => ()))

def stmtLen (x : Fin R) : Stmt (fun _ : Pilha R A => Bool) Unit (Option Bool) :=
  .push .bak (fun v => v.getD false) (.push (.reg x) (fun _ => true) (.goto fun _ => ()))

/-- **O compilador** (na profundidade de laço `δ`). -/
def comp : ℕ → Cmd R → Fr R A
  | _, .emit s => emitF s
  | _, .emitU x s => seq (laco (.reg x) rdO Option.isSome (seq (atom (pushesBit [.tmp])) (emitF s)))
      (mover .tmp [.reg x])
  | _, .zero x => mover (.reg x) []
  | _, .inc x => atom (stmtInc x)
  | _, .add x y => seq (mover (.reg y) [.tmp]) (mover .tmp [.reg y, .reg x])
  | _, .lenIn x => seq (laco .inp rdO Option.isSome (atom (stmtLen x))) (mover .bak [.inp])
  | δ, .seq c₁ c₂ => seq (comp δ c₁) (comp δ c₂)
  | δ, .forU x y body => seq (mover (.reg y) []) (seq (mover (.reg x) [.tmp, auxS δ])
      (seq (mover .tmp [.reg x])
        (laco (auxS δ) rdO Option.isSome (seq (comp (δ + 1) body) (atom (stmtInc y))))))
  | δ, .forBits b₀ b₁ => seq (laco .inp rdO Option.isSome (seq (atom (pushesBit [.bak]))
      (Fragmentos.cond (fun v => v.getD false) (comp δ b₁) (comp δ b₀)))) (mover .bak [.inp])

/-- Boa formação: registradores distintos onde preciso, profundidade de laço `< A`, `forBits`
e `lenIn` fora de `forBits`. -/
def WF (A : ℕ) : Cmd R → ℕ → Bool → Prop
  | .emit _, _, _ => True
  | .emitU _ _, _, _ => True
  | .zero _, _, _ => True
  | .inc _, _, _ => True
  | .add x y, _, _ => x ≠ y
  | .lenIn _, _, β => β = false
  | .seq c₁ c₂, δ, β => WF A c₁ δ β ∧ WF A c₂ δ β
  | .forU x y body, δ, β => x ≠ y ∧ δ < A ∧ WF A body (δ + 1) β
  | .forBits b₀ b₁, δ, β => β = false ∧ WF A b₀ δ true ∧ WF A b₁ δ true

def custoFor (f : Env R → ℕ) (g : Env R → Env R × List Bool) (y : Fin R) : ℕ → Env R → ℕ
  | 0, _ => 1
  | m + 1, E => custoFor f g y m (update (g E).1 y ((g E).1 y + 1)) + (f E + 1) + 1

def custoBits (f₀ f₁ : Env R → ℕ) (g₀ g₁ : Env R → Env R × List Bool) : List Bool → Env R → ℕ
  | [], _ => 1
  | b :: bs, E => custoBits f₀ f₁ g₀ g₁ bs ((if b then g₁ else g₀) E).1 +
      ((if b then f₁ else f₀) E + 1 + 1) + 1

/-- **Custo** exato em passos do código compilado. -/
def custo (w : List Bool) : Cmd R → Env R → ℕ
  | .emit _, _ => 1
  | .emitU x _, E => (2 * E x + 1) + (3 * E x + 1)
  | .zero x, E => 2 * E x + 1
  | .inc _, _ => 1
  | .add _ y, E => (2 * E y + 1) + (2 * E y + 1)
  | .lenIn _, _ => (2 * w.length + 1) + (2 * w.length + 1)
  | .seq c₁ c₂, E => custo w c₂ (sem w c₁ E).1 + custo w c₁ E
  | .forU x y body, E => custoFor (custo w body) (sem w body) y (E x) (update E y 0) +
      (2 * E x + 1) + (2 * E x + 1) + (2 * E y + 1)
  | .forBits b₀ b₁, E => (2 * w.length + 1) +
      custoBits (custo w b₀) (custo w b₁) (sem w b₀) (sem w b₁) w E

/-- Estado depois de um comando: registradores com o novo ambiente, saída acrescentada. -/
def res (S : Stk R A) (E : Env R) (o : List Bool) : Stk R A := fun k =>
  match k with
  | .reg r => List.replicate (E r) true
  | .out => o.reverse ++ S .out
  | k => S k

/-- Pré-condição: registradores codificam `E`, entrada intacta, auxiliar vazia, contadores de
profundidade `≥ δ` vazios, cópia da entrada vazia fora de `forBits`. -/
structure Pre (w : List Bool) (δ : ℕ) (β : Bool) (E : Env R) (S : Stk R A) : Prop where
  reg : ∀ r, S (.reg r) = List.replicate (E r) true
  inp : β = false → S .inp = w
  tmp : S .tmp = []
  aux : ∀ a : Fin A, δ ≤ a.val → S (.aux a) = []
  bak : β = false → S .bak = []

theorem faz_congr {F : Fr R A} {v v' : Option Bool} {S S₁ S' : Stk R A} {n m : ℕ}
    (h : Faz F v S v' S₁ n) (hS : S₁ = S') (hn : n = m) : Faz F v S v' S' m := by
  subst hS hn; exact h

end compilador


section correcao

variable {R A : ℕ} (w : List Bool)

theorem ok_emit (δ : ℕ) (s : List Bool) {β : Bool} {E : Env R} {S : Stk R A} (v : Option Bool)
    (h : Pre w δ β E S) :
    Faz (comp δ (.emit s)) v S none (res S (sem w (.emit s) E).1 (sem w (.emit s) E).2)
      (custo w (.emit s) E) := by
  refine faz_congr (faz_emit s v S) ?_ rfl
  funext k
  cases k <;> simp [res, sem, h.reg]

theorem ok_zero (δ : ℕ) (x : Fin R) {β : Bool} {E : Env R} {S : Stk R A} (v : Option Bool)
    (h : Pre w δ β E S) :
    Faz (comp δ (.zero x)) v S none (res S (sem w (.zero x) E).1 (sem w (.zero x) E).2)
      (custo w (.zero x) E) := by
  refine faz_congr (faz_mover (src := .reg x) (dsts := []) (by simp) List.nodup_nil v S) ?_
    (by simp [custo, h.reg])
  funext k
  cases k with
  | reg r =>
    by_cases hr : r = x
    · subst hr; simp [res, sem, mv, h.reg]
    · simp [res, sem, mv, h.reg, hr]
  | _ => simp [res, sem, mv]

theorem ok_inc (δ : ℕ) (x : Fin R) {β : Bool} {E : Env R} {S : Stk R A} (v : Option Bool)
    (h : Pre w δ β E S) :
    Faz (comp δ (.inc x)) v S none (res S (sem w (.inc x) E).1 (sem w (.inc x) E).2)
      (custo w (.inc x) E) := by
  refine faz_atom ?_
  simp only [stmtInc, stepAux]
  congr 1
  funext k
  cases k with
  | reg r =>
    by_cases hr : r = x
    · subst hr; simp [res, sem, h.reg, List.replicate_succ]
    · simp [res, sem, h.reg, hr]
  | _ => simp [res, sem]

theorem ok_add (δ : ℕ) (x y : Fin R) (hxy : x ≠ y) {β : Bool} {E : Env R} {S : Stk R A}
    (v : Option Bool) (h : Pre w δ β E S) :
    Faz (comp δ (.add x y)) v S none (res S (sem w (.add x y) E).1 (sem w (.add x y) E).2)
      (custo w (.add x y) E) := by
  have h1 := faz_mover (src := .reg y) (dsts := [.tmp]) (by simp) (by simp) v S
  have h2 := faz_mover (src := .tmp) (dsts := [.reg y, .reg x]) (by simp)
    (by simp [Ne.symm hxy]) none (mv S (.reg y) [.tmp] (S (.reg y)).length)
  refine faz_congr (faz_seq h1 h2) ?_ (by simp [custo, mv, h.reg, h.tmp])
  funext k
  cases k with
  | reg r =>
    by_cases hr : r = x
    · subst hr
      simp [res, sem, mv, h.reg, h.tmp, hxy]
      omega
    · by_cases hry : r = y
      · subst hry; simp [res, sem, mv, h.reg, h.tmp, hr]
      · simp [res, sem, mv, h.reg, hr, hry]
  | tmp => simp [res, mv, h.tmp]
  | _ => simp [res, sem, mv]

theorem laco_emitU (x : Fin R) (s : List Bool) : ∀ (m j : ℕ) (S : Stk R A) (v : Option Bool),
    S (.reg x) = List.replicate m true → S .tmp = List.replicate j true →
    Faz (laco (.reg x) rdO Option.isSome (seq (atom (pushesBit [.tmp])) (emitF s))) v S none
      (update (update (update S (.reg x) []) .tmp (List.replicate (j + m) true)) .out
        (((List.replicate m s).flatten).reverse ++ S .out)) (3 * m + 1)
  | 0, j, S, v, hx, ht => by
    refine faz_congr (laco_nil hx rfl) ?_ rfl
    funext k
    cases k with
    | reg r => by_cases hr : r = x
               · subst hr; simp [hx]
               · simp [hr]
    | tmp => simp [ht]
    | _ => simp
  | m + 1, j, S, v, hx, ht => by
    have hS : S (.reg x) = true :: List.replicate m true := by rw [hx, List.replicate_succ]
    have hb : Faz (seq (atom (pushesBit [.tmp])) (emitF s)) (rdO v (some true))
        (update S (.reg x) (List.replicate m true)) none
        (update (fun k => if k ∈ [Pilha.tmp] then true :: update S (.reg x) (List.replicate m true) k
          else update S (.reg x) (List.replicate m true) k) .out
          (s.reverse ++ (S .out))) 2 := by
      have h1 := faz_atom (stepAux_pushesBit (R := R) (A := A) [.tmp] (List.nodup_singleton _) true
        (update S (.reg x) (List.replicate m true)))
      have h2 := faz_emit (R := R) (A := A) s (some true)
        (fun k => if k ∈ [Pilha.tmp] then true :: update S (.reg x) (List.replicate m true) k
          else update S (.reg x) (List.replicate m true) k)
      refine faz_congr (faz_seq h1 h2) ?_ rfl
      congr 2
    have ih := laco_emitU x s m (j + 1)
      (update (fun k => if k ∈ [Pilha.tmp] then true :: update S (.reg x) (List.replicate m true) k
          else update S (.reg x) (List.replicate m true) k) .out (s.reverse ++ (S .out))) none
      (by simp) (by simp [ht, List.replicate_succ])
    refine faz_congr (laco_cons hS rfl hb ih) ?_ (by ring)
    funext k
    cases k with
    | reg r => by_cases hr : r = x
               · subst hr; simp
               · simp [hr]
    | tmp => simp [show j + 1 + m = j + (m + 1) by omega]
    | out => simp [List.replicate_succ, List.flatten_cons]
    | _ => simp

theorem ok_emitU (δ : ℕ) (x : Fin R) (s : List Bool) {β : Bool} {E : Env R} {S : Stk R A}
    (v : Option Bool) (h : Pre w δ β E S) :
    Faz (comp δ (.emitU x s)) v S none (res S (sem w (.emitU x s) E).1 (sem w (.emitU x s) E).2)
      (custo w (.emitU x s) E) := by
  have h1 := laco_emitU x s (E x) 0 S v (h.reg x) (by simp [h.tmp])
  have h2 := faz_mover (src := .tmp) (dsts := [.reg x]) (by simp) (by simp) none
    (update (update (update S (.reg x) []) .tmp (List.replicate (0 + E x) true)) .out
        (((List.replicate (E x) s).flatten).reverse ++ S .out))
  refine faz_congr (faz_seq h1 h2) ?_ (by simp [custo])
  funext k
  cases k with
  | reg r => by_cases hr : r = x
             · subst hr; simp [res, sem, mv]
             · simp [res, sem, mv, hr, h.reg]
  | tmp => simp [res, mv, h.tmp]
  | out => simp [res, sem, mv]
  | _ => simp [res, mv]

theorem laco_lenIn (x : Fin R) : ∀ (L : List Bool) (j : ℕ) (S : Stk R A) (v : Option Bool),
    S .inp = L → S (.reg x) = List.replicate j true →
    Faz (laco .inp rdO Option.isSome (atom (stmtLen x))) v S none
      (update (update (update S .inp []) .bak (L.reverse ++ S .bak)) (.reg x)
        (List.replicate (j + L.length) true)) (2 * L.length + 1)
  | [], j, S, v, hi, hx => by
    refine faz_congr (laco_nil hi rfl) ?_ rfl
    funext k
    cases k with
    | reg r => by_cases hr : r = x
               · subst hr; simp [hx]
               · simp [hr]
    | inp => simp [hi]
    | _ => simp
  | b :: L, j, S, v, hi, hx => by
    have hb : Faz (atom (stmtLen (R := R) (A := A) x)) (rdO v (some b)) (update S .inp L) (some b)
        (update (update (update S .inp L) .bak (b :: S .bak)) (.reg x) (true :: S (.reg x))) 1 := by
      apply faz_atom
      simp [stmtLen, stepAux, rdO]
    have ih := laco_lenIn x L (j + 1)
      (update (update (update S .inp L) .bak (b :: S .bak)) (.reg x) (true :: S (.reg x))) (some b)
      (by simp) (by simp [hx, List.replicate_succ])
    refine faz_congr (laco_cons hi rfl hb ih) ?_ (by simp; ring)
    funext k
    cases k with
    | reg r => by_cases hr : r = x
               · subst hr; simp [show j + 1 + L.length = j + (L.length + 1) by omega]
               · simp [hr]
    | bak => simp
    | _ => simp

theorem ok_lenIn (δ : ℕ) (x : Fin R) {E : Env R} {S : Stk R A} (v : Option Bool)
    (h : Pre w δ false E S) :
    Faz (comp δ (.lenIn x)) v S none (res S (sem w (.lenIn x) E).1 (sem w (.lenIn x) E).2)
      (custo w (.lenIn x) E) := by
  have h1 := laco_lenIn x w (E x) S v (h.inp rfl) (h.reg x)
  have h2 := faz_mover (src := .bak) (dsts := [.inp]) (by simp) (by simp) none
    (update (update (update S .inp []) .bak (w.reverse ++ S .bak)) (.reg x)
        (List.replicate (E x + w.length) true))
  refine faz_congr (faz_seq h1 h2) ?_ (by simp [custo, h.bak rfl])
  funext k
  cases k with
  | reg r => by_cases hr : r = x
             · subst hr; simp [res, sem, mv]
             · simp [res, sem, mv, hr, h.reg]
  | inp => simp [res, mv, h.bak rfl, h.inp rfl, List.take_of_length_le]
  | bak => simp [res, mv, h.bak rfl]
  | _ => simp [res, mv, sem]

/-! ### Álgebra de `res` -/

omit w in
theorem res_res (S : Stk R A) (E₁ E₂ : Env R) (o₁ o₂ : List Bool) :
    res (res S E₁ o₁) E₂ o₂ = res S E₂ (o₁ ++ o₂) := by
  funext k; cases k <;> simp [res]

omit w in
theorem res_self {S : Stk R A} {E : Env R} (h : ∀ r, S (.reg r) = List.replicate (E r) true) :
    res S E [] = S := by
  funext k; cases k <;> simp [res, h]

omit w in
theorem res_update {S : Stk R A} {E : Env R} {o : List Bool} {k : Pilha R A} (l : List Bool)
    (hk : ∀ r, k ≠ .reg r) (hk' : k ≠ .out) : res (update S k l) E o = update (res S E o) k l := by
  funext j
  by_cases hj : j = k
  · subst hj
    cases j with
    | reg r => exact absurd rfl (hk r)
    | out => exact absurd rfl hk'
    | _ => simp [res]
  · cases j <;> simp [res, update_of_ne hj]

theorem pre_res {δ : ℕ} {β : Bool} {E E' : Env R} {S : Stk R A} (o : List Bool)
    (h : Pre w δ β E S) : Pre w δ β E' (res S E' o) where
  reg r := rfl
  inp hb := by simp [res, h.inp hb]
  tmp := by simp [res, h.tmp]
  aux a ha := by simp [res, h.aux a ha]
  bak hb := by simp [res, h.bak hb]

/-! ### O teorema do compilador -/

/-- **Correção do compilador**: o código compilado de um programa bem formado vai do estado `S`
(que codifica `E`) ao estado com os registradores de `(sem w c E).1` e a saída
`(sem w c E).2` acrescentada, em exatamente `custo w c E` passos. -/
theorem comp_ok : ∀ (c : Cmd R) (δ : ℕ) (β : Bool), WF A c δ β → ∀ (E : Env R) (S : Stk R A)
    (v : Option Bool), Pre w δ β E S →
    Faz (comp δ c) v S none (res S (sem w c E).1 (sem w c E).2) (custo w c E)
  | .emit s, δ, _, _, _, _, v, h => ok_emit w δ s v h
  | .emitU x s, δ, _, _, _, _, v, h => ok_emitU w δ x s v h
  | .zero x, δ, _, _, _, _, v, h => ok_zero w δ x v h
  | .inc x, δ, _, _, _, _, v, h => ok_inc w δ x v h
  | .add x y, δ, _, hwf, _, _, v, h => ok_add w δ x y hwf v h
  | .lenIn x, δ, β, hwf, _, _, v, h => by
    have hβ : β = false := hwf
    subst hβ
    exact ok_lenIn w δ x v h
  | .seq c₁ c₂, δ, β, hwf, E, S, v, h => by
    obtain ⟨h₁, h₂⟩ := hwf
    have r₁ := comp_ok c₁ δ β h₁ E S v h
    have r₂ := comp_ok c₂ δ β h₂ (sem w c₁ E).1 (res S (sem w c₁ E).1 (sem w c₁ E).2) none
      (pre_res w _ h)
    refine faz_congr (faz_seq r₁ r₂) ?_ rfl
    rw [res_res]
    rfl
  | .forU x y body, δ, β, hwf, E, S, v, h => by
    obtain ⟨hxy, hδ, hb⟩ := hwf
    have haux : (auxS δ : Pilha R A) = .aux ⟨δ, hδ⟩ := by simp [auxS, hδ]
    have hA0 : S (.aux ⟨δ, hδ⟩) = [] := h.aux _ le_rfl
    -- o laço
    have L : ∀ (m : ℕ) (E' : Env R) (S' : Stk R A) (v' : Option Bool), Pre w (δ + 1) β E' S' →
        S' (.aux ⟨δ, hδ⟩) = List.replicate m true →
        Faz (laco (auxS δ) rdO Option.isSome (seq (comp (δ + 1) body) (atom (stmtInc y)))) v' S'
          none (update (res S' (semFor (sem w body) y m E').1 (semFor (sem w body) y m E').2)
            (.aux ⟨δ, hδ⟩) []) (custoFor (custo w body) (sem w body) y m E') := by
      intro m
      induction m with
      | zero =>
        intro E' S' v' hp ha
        rw [haux]
        refine faz_congr (laco_nil (by simpa using ha) rfl) ?_ rfl
        simp only [semFor]
        rw [res_self hp.reg]
        simp only [List.replicate_zero] at ha
        rw [← ha, update_eq_self]
      | succ m ih =>
        intro E' S' v' hp ha
        have hS : S' (auxS δ) = true :: List.replicate m true := by
          rw [haux, ha, List.replicate_succ]
        set S'₀ := update S' (auxS δ) (List.replicate m true) with hS'₀
        have hp₀ : Pre w (δ + 1) β E' S'₀ := {
          reg := fun r => by simp [S'₀, haux, hp.reg]
          inp := fun hβ => by simp [S'₀, haux, hp.inp hβ]
          tmp := by simp [S'₀, haux, hp.tmp]
          aux := fun a ha' => by
            have hne : a ≠ ⟨δ, hδ⟩ := by intro he; subst he; simp at ha'
            simp [S'₀, haux, hne, hp.aux a ha']
          bak := fun hβ => by simp [S'₀, haux, hp.bak hβ] }
        set r₁ := sem w body E' with hr₁
        have hbody := comp_ok body (δ + 1) β hb E' S'₀ (some true) hp₀
        have hinc : Faz (atom (stmtInc (R := R) (A := A) y)) none (res S'₀ r₁.1 r₁.2) none
            (res S'₀ (update r₁.1 y (r₁.1 y + 1)) r₁.2) 1 := by
          apply faz_atom
          simp only [stmtInc, stepAux]
          congr 1
          funext k
          cases k with
          | reg r => by_cases hr : r = y
                     · subst hr; simp [res, List.replicate_succ]
                     · simp [res, hr]
          | _ => simp [res]
        have hp₁ : Pre w (δ + 1) β (update r₁.1 y (r₁.1 y + 1))
            (res S'₀ (update r₁.1 y (r₁.1 y + 1)) r₁.2) := pre_res w _ hp₀
        have ha₁ : (res S'₀ (update r₁.1 y (r₁.1 y + 1)) r₁.2) (.aux ⟨δ, hδ⟩) =
            List.replicate m true := by simp [res, S'₀, haux]
        have hrest := ih _ _ none hp₁ ha₁
        refine faz_congr (laco_cons hS rfl (faz_seq hbody hinc) hrest) ?_ (by simp [custoFor]; ring)
        simp only [semFor, res_res]
        rw [← hr₁]
        funext k
        by_cases hk : k = .aux ⟨δ, hδ⟩
        · subst hk; simp
        · cases k <;> simp_all [res, S'₀]
    -- as três preparações
    have s1 := faz_mover (src := .reg y) (dsts := []) (by simp) List.nodup_nil v S
    have s2 := faz_mover (src := .reg x) (dsts := [.tmp, auxS δ]) (by simp [haux]) (by simp [haux])
      none (mv S (.reg y) [] (S (.reg y)).length)
    have s3 := faz_mover (src := .tmp) (dsts := [.reg x]) (by simp) (by simp) none
      (mv (mv S (.reg y) [] (S (.reg y)).length) (.reg x) [.tmp, auxS δ]
        ((mv S (.reg y) [] (S (.reg y)).length) (.reg x)).length)
    set S₃ := mv (mv (mv S (.reg y) [] (S (.reg y)).length) (.reg x) [.tmp, auxS δ]
        ((mv S (.reg y) [] (S (.reg y)).length) (.reg x)).length) .tmp [.reg x]
        ((mv (mv S (.reg y) [] (S (.reg y)).length) (.reg x) [.tmp, auxS δ]
          ((mv S (.reg y) [] (S (.reg y)).length) (.reg x)).length) .tmp).length with hS₃
    have e3 : S₃ = update (res S (update E y 0) []) (.aux ⟨δ, hδ⟩) (List.replicate (E x) true) := by
      funext k
      by_cases hk : k = .aux ⟨δ, hδ⟩
      · subst hk
        simp [S₃, mv, haux, h.reg, hA0, h.tmp, hxy]
      · cases k with
        | reg r =>
          by_cases hr : r = x
          · subst hr; simp [S₃, mv, res, h.reg, hxy, h.tmp, haux]
          · by_cases hry : r = y
            · subst hry; simp [S₃, mv, res, haux, hr]
            · simp [S₃, mv, res, h.reg, hr, hry, haux]
        | tmp => simp [S₃, mv, res, h.tmp, haux]
        | aux a =>
          have hne : a ≠ ⟨δ, hδ⟩ := fun he => hk (by rw [he])
          simp [S₃, mv, res, haux, hne]
        | _ => simp [S₃, mv, res, haux]
    have hp3 : Pre w (δ + 1) β (update E y 0) S₃ := by
      rw [e3]
      exact {
        reg := fun r => by simp [res]
        inp := fun hβ => by simp [res, h.inp hβ]
        tmp := by simp [res, h.tmp]
        aux := fun a ha => by
          have hne : a ≠ ⟨δ, hδ⟩ := by intro he; subst he; simp at ha
          simp [res, hne, h.aux a (by omega)]
        bak := fun hβ => by simp [res, h.bak hβ] }
    have s4 := L (E x) (update E y 0) S₃ none hp3 (by rw [e3]; simp)
    refine faz_congr (faz_seq s1 (faz_seq s2 (faz_seq s3 s4))) ?_ ?_
    · rw [e3, res_update _ (by simp) (by simp), res_res, update_idem]
      simp only [sem, List.nil_append]
      funext k
      by_cases hk : k = .aux ⟨δ, hδ⟩
      · subst hk; simp [res, hA0]
      · simp [hk]
    · simp only [custo, mv, h.reg]
      simp [h.tmp, haux, hxy]
  | .forBits b₀ b₁, δ, β, hwf, E, S, v, h => by
    obtain ⟨hβ, hb₀, hb₁⟩ := hwf
    subst hβ
    have L : ∀ (Ls : List Bool) (E' : Env R) (S' : Stk R A) (v' : Option Bool),
        Pre w δ true E' S' → S' .inp = Ls →
        Faz (laco .inp rdO Option.isSome (seq (atom (pushesBit [.bak]))
          (Fragmentos.cond (fun v => v.getD false) (comp δ b₁) (comp δ b₀)))) v' S' none
          (update (update (res S' (semBits (sem w b₀) (sem w b₁) Ls E').1
            (semBits (sem w b₀) (sem w b₁) Ls E').2) .inp []) .bak (Ls.reverse ++ S' .bak))
          (custoBits (custo w b₀) (custo w b₁) (sem w b₀) (sem w b₁) Ls E') := by
      intro Ls
      induction Ls with
      | nil =>
        intro E' S' v' hp hi
        refine faz_congr (laco_nil hi rfl) ?_ rfl
        simp only [semBits, List.reverse_nil, List.nil_append]
        rw [res_self hp.reg]
        rw [← hi, update_eq_self, update_eq_self]
      | cons b Ls ih =>
        intro E' S' v' hp hi
        set S'b : Stk R A := fun k => if k ∈ [Pilha.bak] then b :: update S' .inp Ls k
          else update S' .inp Ls k with hS'b
        have hpb : Pre w δ true E' S'b := {
          reg := fun r => by simp [S'b, hp.reg]
          inp := fun h' => absurd h' (by simp)
          tmp := by simp [S'b, hp.tmp]
          aux := fun a ha => by simp [S'b, hp.aux a ha]
          bak := fun h' => absurd h' (by simp) }
        have h1 := faz_atom (stepAux_pushesBit (R := R) (A := A) [.bak] (List.nodup_singleton _) b
          (update S' .inp Ls))
        have hcond : Faz (Fragmentos.cond (fun v : Option Bool => v.getD false) (comp δ b₁)
            (comp δ b₀)) (some b) S'b none (res S'b ((if b then sem w b₁ else sem w b₀) E').1
              ((if b then sem w b₁ else sem w b₀) E').2)
            ((if b then custo w b₁ else custo w b₀) E' + 1) := by
          cases b
          · exact faz_cond_false rfl (comp_ok b₀ δ true hb₀ E' S'b (some false) hpb)
          · exact faz_cond_true rfl (comp_ok b₁ δ true hb₁ E' S'b (some true) hpb)
        have hpr : Pre w δ true ((if b then sem w b₁ else sem w b₀) E').1
            (res S'b ((if b then sem w b₁ else sem w b₀) E').1
              ((if b then sem w b₁ else sem w b₀) E').2) := pre_res w _ hpb
        have hrest := ih _ _ none hpr (by simp [res, S'b])
        refine faz_congr (laco_cons hi rfl (faz_seq h1 hcond) hrest) ?_
          (by simp only [custoBits])
        simp only [semBits, res_res]
        funext k
        cases k with
        | inp => simp
        | bak => simp [res, S'b]
        | _ => simp [res, S'b]
    have hp' : Pre w δ true E S := ⟨h.reg, fun h' => absurd h' (by simp), h.tmp, h.aux,
      fun h' => absurd h' (by simp)⟩
    have s1 := L w E S v hp' (h.inp rfl)
    have s2 := faz_mover (src := .bak) (dsts := [.inp]) (by simp) (by simp) none
      (update (update (res S (semBits (sem w b₀) (sem w b₁) w E).1
        (semBits (sem w b₀) (sem w b₁) w E).2) .inp []) .bak (w.reverse ++ S .bak))
    refine faz_congr (faz_seq s1 s2) ?_ (by simp [custo, h.bak rfl])
    simp only [sem]
    funext k
    cases k with
    | inp => simp [mv, res, h.bak rfl, h.inp rfl, List.take_of_length_le]
    | bak => simp [mv, res, h.bak rfl]
    | _ => simp [mv, res]

end correcao


/-! ## A máquina completa -/

section maquina

variable {R A : ℕ}

/-- Encadeia uma lista de fragmentos. -/
def seqL : List (Fr R A) → Fr R A
  | [] => atom (.goto fun _ => ())
  | F :: Fs => seq F (seqL Fs)

/-- Limpeza: a saída vai (na ordem certa) para `fin`, os registradores e a entrada esvaziam. -/
def limpeza : Fr R A :=
  seq (mover .out [.fin]) (seq (seqL ((List.finRange R).map fun r => mover (.reg r) []))
    (mover .inp []))

def Ftot (c : Cmd R) : Fr R A := seq (comp 0 c) limpeza

/-- **A máquina** que roda o programa `c` sobre a entrada e devolve a saída em `fin`. -/
abbrev maq (c : Cmd R) : FinTM2 where
  K := Pilha R A
  k₀ := .inp
  k₁ := .fin
  Γ := fun _ => Bool
  Λ := Option (Ftot (A := A) c).Λ
  main := some (Ftot (A := A) c).entry
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := (Ftot (A := A) c).maq

theorem faz_zeraRegs : ∀ (rs : List (Fin R)), rs.Nodup → ∀ (S : Stk R A),
    Faz (seqL (rs.map fun r => mover (A := A) (.reg r) [])) none S none
      (fun k => match k with
        | .reg r => if r ∈ rs then [] else S (.reg r)
        | k => S k)
      ((rs.map fun r => 2 * (S (.reg r)).length + 1).sum + 1)
  | [], _, S => by
    refine faz_congr (faz_atom (q := .goto fun _ => ()) (v := none) (S := S) (v' := none)
      (S' := S) rfl) ?_ (by simp)
    funext k; cases k <;> simp
  | r :: rs, hnd, S => by
    have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
    have h1 := faz_mover (src := .reg r) (dsts := []) (by simp) List.nodup_nil none S
    have h2 := faz_zeraRegs rs (List.nodup_cons.mp hnd).2 (mv S (.reg r) [] (S (.reg r)).length)
    refine faz_congr (faz_seq h1 h2) ?_ ?_
    · funext k
      cases k with
      | reg q => by_cases hq : q = r
                 · subst hq; simp [mv]
                 · simp [mv, hq]
      | _ => simp [mv]
    · have : (rs.map fun q => 2 * (mv S (.reg r) [] (S (.reg r)).length (.reg q)).length + 1) =
          (rs.map fun q => 2 * (S (.reg q)).length + 1) := by
        apply List.map_congr_left; intro q hq
        have hqr : q ≠ r := fun h => hr (h ▸ hq)
        simp [mv, hqr]
      simp only [List.map_cons, List.sum_cons, this]
      omega

/-- Custo da limpeza. -/
def custoLimpa (w : List Bool) (E : Env R) (o : List Bool) : ℕ :=
  (2 * w.length + 1) + (((List.finRange R).map fun r => 2 * E r + 1).sum + 1) + (2 * o.length + 1)

theorem init_pre (c : Cmd R) (w : List Bool) :
    Pre w 0 false (fun _ => 0) (initList (maq (A := A) c) w).stk where
  reg r := by simp [initList, maq]
  inp _ := by simp [initList, maq]
  tmp := by simp [initList, maq]
  aux a _ := by simp [initList, maq]
  bak _ := by simp [initList, maq]

/-- **A execução da máquina**: começa em `initList w`, para em `haltList` com a saída do programa,
em `custoLimpa + custo + 1` passos. -/
theorem maq_run (c : Cmd R) (hwf : WF A c 0 false) (w : List Bool) :
    (flip bind (maq (A := A) c).step)^[custoLimpa w (sem w c (fun _ => 0)).1
      (sem w c (fun _ => 0)).2 + custo w c (fun _ => 0) + 1] (some (initList (maq (A := A) c) w)) =
      some (haltList (maq (A := A) c) (sem w c (fun _ => 0)).2) := by
  set E := (sem w c (fun _ => 0)).1
  set o := (sem w c (fun _ => 0)).2
  set S₀ : Stk R A := (initList (maq (A := A) c) w).stk with hS₀
  have hp := init_pre (A := A) c w
  have r₁ := comp_ok w c 0 false hwf (fun _ => 0) S₀ none hp
  set S₁ := res S₀ E o with hS₁
  have e1 : S₁ .out = o.reverse := by simp [S₁, res, S₀, initList, maq]
  have r₂ := faz_mover (src := .out) (dsts := [.fin]) (by simp) (by simp) none S₁
  set S₂ := mv S₁ .out [.fin] (S₁ .out).length
  have r₃ := faz_zeraRegs (A := A) (List.finRange R) (List.nodup_finRange R) S₂
  set S₃ : Stk R A := fun k => match k with
    | .reg r => if r ∈ List.finRange R then [] else S₂ (.reg r)
    | k => S₂ k
  have r₄ := faz_mover (src := .inp) (dsts := []) (by simp) List.nodup_nil none S₃
  have hrun := faz_seq r₁ (faz_seq r₂ (faz_seq r₃ r₄))
  have hfin : mv S₃ .inp [] (S₃ .inp).length = (haltList (maq (A := A) c) o).stk := by
    funext k
    cases k with
    | fin => simp [mv, S₃, S₂, S₁, res, haltList, maq, S₀, initList, List.take_of_length_le]
    | reg r => simp [mv, S₃, haltList, maq]
    | aux a => simp [mv, S₃, S₂, S₁, res, S₀, initList, haltList, maq]
    | _ => simp [mv, S₃, S₂, S₁, res, S₀, initList, haltList, maq]
  have hcost : (2 * (S₃ .inp).length + 1) + (((List.finRange R).map fun r =>
      2 * (S₂ (.reg r)).length + 1).sum + 1) + (2 * (S₁ .out).length + 1) + custo w c (fun _ => 0) =
      custoLimpa w E o + custo w c (fun _ => 0) := by
    simp [custoLimpa, S₃, S₂, S₁, mv, res, S₀, initList, maq]
  rw [Function.iterate_succ_apply']
  unfold Faz at hrun
  have h2 : (flip bind (maq (A := A) c).step)^[custoLimpa w E o + custo w c (fun _ => 0)]
      (some (initList (maq (A := A) c) w)) =
      some ⟨some none, none, mv S₃ .inp [] (S₃ .inp).length⟩ := by
    rw [← hcost]; exact hrun
  rw [h2]
  show some (stepAux .halt none (mv S₃ .inp [] (S₃ .inp).length)) = _
  simp only [stepAux, hfin]
  rfl

end maquina


/-! ## Computabilidade em tempo polinomial -/

section poli

variable {R A : ℕ}

/-- Um programa bem formado cujo custo total é cotado por um polinômio no tamanho da entrada
computa sua saída em tempo polinomial numa `FinTM2`. -/
noncomputable def computavel (c : Cmd R) (hwf : WF A c 0 false) (P : Polynomial ℕ)
    (hP : ∀ w : List Bool, custoLimpa w (sem w c (fun _ => 0)).1 (sem w c (fun _ => 0)).2 +
      custo w c (fun _ => 0) + 1 ≤ P.eval w.length) :
    TM2ComputableInPolyTime ClayPvsNPProof.ATK.LigacaoPNP.cod ClayPvsNPProof.ATK.LigacaoPNP.cod
      (fun w => (sem w c (fun _ => 0)).2) where
  tm := maq (A := A) c
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P
  outputsFun w :=
    { steps := custoLimpa w (sem w c (fun _ => 0)).1 (sem w c (fun _ => 0)).2 +
        custo w c (fun _ => 0) + 1
      evals_in_steps := by
        have h := maq_run (A := A) c hwf w
        simpa [ClayPvsNPProof.ATK.LigacaoPNP.cod] using h
      steps_le_m := by simpa [ClayPvsNPProof.ATK.LigacaoPNP.cod] using hP w }

/-! ### Sanidade: o comprimento da entrada em unário -/

/-- `x₀ := |w|`; emite `true` `|w|` vezes. -/
def progUnario : Cmd 1 := .seq (.lenIn 0) (.emitU 0 [true])

theorem sem_unario (w : List Bool) :
    (sem w progUnario (fun _ => 0)).2 = List.replicate w.length true := by
  simp [progUnario, sem]

/-- O comprimento em unário é computável em tempo linear (`≤ 15 n + 9`). -/
noncomputable def unarioComputavel :
    TM2ComputableInPolyTime ClayPvsNPProof.ATK.LigacaoPNP.cod ClayPvsNPProof.ATK.LigacaoPNP.cod
      (fun w => (sem w progUnario (fun _ => 0)).2) :=
  computavel (A := 1) progUnario (by simp [progUnario, WF]) (15 * Polynomial.X + 9) (by
    intro w
    simp [custoLimpa, custo, sem, progUnario, List.finRange]
    omega)

end poli

end ClayPvsNPProof.ATK.Compilador

