-- Origem: kernel ATK, espelho público ShantiDraconis/atk-math-core-public @ ffc111a
-- (= ShantiDraconis/M-Core @ 390e378), arquivo imports/M-Core/atk-kernel/ATK/CookLevinGerador.lean
-- (sha256 do original: 67da7751f715b0e0…).
-- Alterações comuns: namespace `ATK.*` → `ClayPvsNPProof.ATK.*`; linhas `#print axioms` removidas
-- (a auditoria está em `ClayPvsNPProof/Audit.lean`). Alterações específicas: nenhuma além das comuns.
import ClayPvsNPProof.ATK.CookLevinLacos
import ClayPvsNPProof.ATK.CookLevinReducao

/-!
# ATK — Ponte B4, marco M2d (parte 2b): o gerador do tableau

Programas da linguagem de laços que imprimem a CNF do tableau de Cook–Levin, família por família,
com a prova de que a saída é exatamente `codCNF (renomeia (tableau))`:

* termos unários, literais `x t k i j`, `y t j`, `z t j` (os nomes de `ClayPvsNPProof.ATK.CookLevinReducao`),
  cláusulas e "exatamente um" (`geraU_umSo`);
* `progE`, `progI`, `progR`, `progP`, `progA`: as famílias (E), (I), (R), (P), (A) do tableau,
  com `geraU_progE` etc.; (I) lê a palavra de entrada (`progPre`, por `forBits`), (R) percorre
  rótulos, estados e padrões de janela e imprime os consequentes com o resto das pilhas deslocado;
* **`geraU_progTab`**: o programa de emissão inteiro imprime `(A.formula …).flatMap cc`.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ClayPvsNPProof.ATK.CookLevinGerador

open Function ClayPvsNPProof.ATK.Compilador ClayPvsNPProof.ATK.SATemNP ClayPvsNPProof.ATK.ModeloPNP ClayPvsNPProof.ATK.CookLevinTableau ClayPvsNPProof.ATK.CookLevinReducao
  ClayPvsNPProof.ATK.CookLevinLacos

variable {R : ℕ} (w : List Bool)

/-! ## Termos unários -/

/-- `simb true` repetido `n` vezes e o terminador `simb false`: os bits de `unario n` vistos
pelo codificador de literais. -/
def sU (n : ℕ) : List Bool := (List.replicate n [false, true]).flatten ++ [false, false]

theorem unario_simb (n : ℕ) : (unario n).flatMap simb = sU n := by
  simp [unario, sU, simb, List.flatMap_replicate]

/-- Um termo: soma de registradores mais uma constante. -/
structure Termo (R : ℕ) where
  rs : List (Fin R)
  c : ℕ

def Termo.val (E : Env R) (τ : Termo R) : ℕ := (τ.rs.map E).sum + τ.c

def pTermo (τ : Termo R) : Cmd R :=
  seqC ((τ.rs.map fun x => Cmd.emitU x [false, true]) ++
    [.emit ((List.replicate τ.c [false, true]).flatten ++ [false, false])])

theorem emite_pTermo (τ : Termo R) (E : Env R) : Emite w (pTermo τ) E (sU (τ.val E)) := by
  have h := emite_seqC_append w
    (emite_seqC_map w (fun x => Cmd.emitU x [false, true])
      (fun x => (List.replicate (E x) [false, true]).flatten) τ.rs (fun x _ => rfl))
    (emite_seqC_cons w (emite_emit w ((List.replicate τ.c [false, true]).flatten ++ [false, false]) E)
      (emite_seqC_nil w E))
  have e : sU (τ.val E) = τ.rs.flatMap (fun x => (List.replicate (E x) [false, true]).flatten) ++
      ((List.replicate τ.c [false, true]).flatten ++ [false, false] ++ []) := by
    unfold sU Termo.val
    rw [List.append_nil, ← List.append_assoc]
    congr 1
    induction τ.rs with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.append_assoc, ← ih, Nat.add_assoc,
        List.replicate_add, List.flatten_append]
  rw [e]
  exact h

/-! ## Literais e cláusulas -/

/-- O literal renomeado, como na redução. -/
noncomputable def ren {K : Type} [Fintype K] (ℓ : Lit K) : Literal := (nome ℓ.1, ℓ.2)

theorem codCNF_renomeia {K : Type} [Fintype K] (φ : List (Cla K)) :
    codCNF (renomeia φ) = φ.flatMap fun C => (C.flatMap fun ℓ => codLiteral (ren ℓ)) ++ [true, true] := by
  simp [codCNF, renomeia, codClausula, ren, List.flatMap_map]

/-- Imprime um literal: polaridade, marca de dois bits, termos unários. -/
def pLit (b : Bool) (tag : List Bool) (ts : List (Termo R)) : Cmd R :=
  seqC ([.emit ([false, b] ++ tag.flatMap simb)] ++ ts.map pTermo ++ [.emit [false, true, true, false]])

theorem emite_pLit (b : Bool) (tag : List Bool) (ts : List (Termo R)) (E : Env R) :
    Emite w (pLit b tag ts) E
      ([false, b] ++ tag.flatMap simb ++ (ts.flatMap fun τ => sU (τ.val E)) ++ [false, true, true, false]) := by
  have h := emite_seqC_append w (emite_seqC_append w
    (emite_seqC_cons w (emite_emit w ([false, b] ++ tag.flatMap simb) E) (emite_seqC_nil w E))
    (emite_seqC_map w pTermo (fun τ => sU (τ.val E)) ts (fun τ _ => emite_pTermo w τ E)))
    (emite_seqC_cons w (emite_emit w [false, true, true, false] E) (emite_seqC_nil w E))
  unfold pLit
  simpa using h

section lits
variable {K : Type} [Fintype K]

theorem codLiteral_nome (v : Var K) (b : Bool) :
    codLiteral (ren (v, b)) = [false, b] ++ (cadeia v).flatMap simb ++ [true, false] := by
  simp [ren, codLiteral, simb, bits_nome]

/-- Literal de célula `x t k i j`. -/
theorem emite_litX (b : Bool) (k : K) (τt τi τj : Termo R) (E : Env R) :
    Emite w (pLit b [true, true] [τt, ⟨[], κ k⟩, τi, τj]) E
      (codLiteral (ren (Var.x (τt.val E) k (τi.val E) (τj.val E), b))) := by
  have h := emite_pLit w b [true, true] [τt, ⟨[], κ k⟩, τi, τj] E
  rw [codLiteral_nome]
  convert h using 1
  simp [cadeia, unario_simb, simb, Termo.val]

theorem emite_litY (b : Bool) (τt τj : Termo R) (E : Env R) :
    Emite w (pLit b [true, false] [τt, τj]) E
      (codLiteral (ren (Var.y (K := K) (τt.val E) (τj.val E), b))) := by
  have h := emite_pLit w b [true, false] [τt, τj] E
  rw [codLiteral_nome]
  convert h using 1
  simp [cadeia, unario_simb, simb]

theorem emite_litZ (b : Bool) (τt τj : Termo R) (E : Env R) :
    Emite w (pLit b [false, true] [τt, τj]) E
      (codLiteral (ren (Var.z (K := K) (τt.val E) (τj.val E), b))) := by
  have h := emite_pLit w b [false, true] [τt, τj] E
  rw [codLiteral_nome]
  convert h using 1
  simp [cadeia, unario_simb, simb]

/-- Imprime uma cláusula: literais e o terminador `[true, true]`. -/
def pCla (lits : List (Cmd R)) : Cmd R := seqC (lits ++ [.emit [true, true]])

theorem emite_pCla {lits : List (Cmd R)} {C : Cla K} {E : Env R}
    (h : List.Forall₂ (fun c ℓ => Emite w c E (codLiteral (ren ℓ))) lits C) :
    Emite w (pCla lits) E ((C.flatMap fun ℓ => codLiteral (ren ℓ)) ++ [true, true]) := by
  have hl : Emite w (seqC lits) E (C.flatMap fun ℓ => codLiteral (ren ℓ)) := by
    induction h with
    | nil => exact emite_seqC_nil w E
    | cons hc _ ih => rw [List.flatMap_cons]; exact emite_seqC_cons w hc ih
  exact emite_seqC_append w hl (emite_seqC_cons w (emite_emit w [true, true] E) (emite_seqC_nil w E))

end lits

/-! ## Literais, cláusulas e "exatamente um" como blocos uniformes -/

/-- Os registradores de um termo estão em `S`. -/
def Termo.em (τ : Termo R) (S : List (Fin R)) : Prop := ∀ r ∈ τ.rs, r ∈ S

theorem Termo.val_igual {τ : Termo R} {S : List (Fin R)} {E₀ E : Env R} (hτ : τ.em S)
    (hE : Igual S E₀ E) : τ.val E = τ.val E₀ := by
  unfold Termo.val
  congr 1
  exact congrArg List.sum (List.map_congr_left (fun r hr => hE r (hτ r hr)))

section blocos
variable {K : Type} [Fintype K]

theorem geraU_litX (b : Bool) (k : K) {τt τi τj : Termo R} {E₀ : Env R} {S : List (Fin R)}
    (ht : τt.em S) (hi : τi.em S) (hj : τj.em S) :
    GeraU w (pLit b [true, true] [τt, ⟨[], κ k⟩, τi, τj]) E₀ S
      (codLiteral (ren (Var.x (τt.val E₀) k (τi.val E₀) (τj.val E₀), b))) := by
  apply geraU_emite
  intro E hE
  have := emite_litX w b k τt τi τj E
  rwa [Termo.val_igual ht hE, Termo.val_igual hi hE, Termo.val_igual hj hE] at this

theorem geraU_litY (b : Bool) {τt τj : Termo R} {E₀ : Env R} {S : List (Fin R)}
    (ht : τt.em S) (hj : τj.em S) :
    GeraU w (pLit b [true, false] [τt, τj]) E₀ S
      (codLiteral (ren (Var.y (K := K) (τt.val E₀) (τj.val E₀), b))) := by
  apply geraU_emite
  intro E hE
  have := emite_litY (K := K) w b τt τj E
  rwa [Termo.val_igual ht hE, Termo.val_igual hj hE] at this

theorem geraU_litZ (b : Bool) {τt τj : Termo R} {E₀ : Env R} {S : List (Fin R)}
    (ht : τt.em S) (hj : τj.em S) :
    GeraU w (pLit b [false, true] [τt, τj]) E₀ S
      (codLiteral (ren (Var.z (K := K) (τt.val E₀) (τj.val E₀), b))) := by
  apply geraU_emite
  intro E hE
  have := emite_litZ (K := K) w b τt τj E
  rwa [Termo.val_igual ht hE, Termo.val_igual hj hE] at this

/-- Uma cláusula impressa a partir de literais impressos. -/
theorem geraU_cla {lits : List (Cmd R)} {C : Cla K} {E₀ : Env R} {S : List (Fin R)}
    (h : List.Forall₂ (fun c ℓ => GeraU w c E₀ S (codLiteral (ren ℓ))) lits C) :
    GeraU w (pCla lits) E₀ S ((C.flatMap fun ℓ => codLiteral (ren ℓ)) ++ [true, true]) := by
  have hl : GeraU w (seqC lits) E₀ S (C.flatMap fun ℓ => codLiteral (ren ℓ)) := by
    induction h with
    | nil => exact geraU_nil w E₀ S
    | cons hc _ ih => rw [List.flatMap_cons]; exact geraU_cons w hc ih
  exact geraU_append w hl (geraU_cons w (geraU_emite w (fun E _ => emite_emit w [true, true] E))
    (geraU_nil w E₀ S))

/-- Cláusula codificada (com renomeação). -/
noncomputable def cc (C : Cla K) : List Bool := (C.flatMap fun ℓ => codLiteral (ren ℓ)) ++ [true, true]

theorem codCNF_renomeia_cc (φ : List (Cla K)) : codCNF (renomeia φ) = φ.flatMap cc :=
  codCNF_renomeia φ

/-- "No máximo um" impresso sobre uma lista de índices. -/
def pNoMax (lit : ℕ → Bool → Cmd R) : List ℕ → List (Cmd R)
  | [] => []
  | j :: js => js.map (fun j' => pCla [lit j false, lit j' false]) ++ pNoMax lit js

/-- "Exatamente um" impresso. -/
def pUmSo (N : ℕ) (lit : ℕ → Bool → Cmd R) : Cmd R :=
  seqC (pCla ((List.range N).map fun j => lit j true) :: pNoMax lit (List.range N))

theorem geraU_noMax (lit : ℕ → Bool → Cmd R) (f : ℕ → Var K) {E₀ : Env R} {S : List (Fin R)}
    (hlit : ∀ j b, GeraU w (lit j b) E₀ S (codLiteral (ren (f j, b)))) :
    ∀ l : List ℕ, GeraU w (seqC (pNoMax lit l)) E₀ S ((noMaximo (l.map f)).flatMap cc)
  | [] => geraU_nil w E₀ S
  | j :: js => by
    simp only [pNoMax, List.map_cons, noMaximo, List.flatMap_append, List.map_map]
    refine geraU_append w ?_ (geraU_noMax lit f hlit js)
    rw [List.flatMap_map]
    refine geraU_map w _ _ js (fun j' _ => ?_)
    exact geraU_cla w (List.Forall₂.cons (hlit j false) (List.Forall₂.cons (hlit j' false) List.Forall₂.nil))

theorem geraU_umSo (N : ℕ) (lit : ℕ → Bool → Cmd R) (f : ℕ → Var K) {E₀ : Env R}
    {S : List (Fin R)} (hlit : ∀ j b, GeraU w (lit j b) E₀ S (codLiteral (ren (f j, b)))) :
    GeraU w (pUmSo N lit) E₀ S ((umSo ((List.range N).map f)).flatMap cc) := by
  simp only [pUmSo, umSo, List.flatMap_cons]
  refine geraU_cons w ?_ (geraU_noMax w lit f hlit (List.range N))
  refine geraU_cla w ?_
  simp only [peloMenos, List.map_map]
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr (fun j _ => hlit j true)

end blocos

/-! ## Abreviações e lemas de apoio -/

def tc (c : ℕ) : Termo R := ⟨[], c⟩
def tr (r : Fin R) (c : ℕ) : Termo R := ⟨[r], c⟩
def tr2 (r s : Fin R) (c : ℕ) : Termo R := ⟨[r, s], c⟩

@[simp] theorem val_tc (E : Env R) (c : ℕ) : (tc c : Termo R).val E = c := by simp [tc, Termo.val]
@[simp] theorem val_tr (E : Env R) (r : Fin R) (c : ℕ) : (tr r c).val E = E r + c := by
  simp [tr, Termo.val]
@[simp] theorem val_tr2 (E : Env R) (r s : Fin R) (c : ℕ) : (tr2 r s c).val E = E r + E s + c := by
  simp [tr2, Termo.val, Nat.add_assoc]

@[simp] theorem em_tc (S : List (Fin R)) (c : ℕ) : (tc c : Termo R).em S := by simp [Termo.em, tc]
@[simp] theorem em_tr (S : List (Fin R)) (r : Fin R) (c : ℕ) : (tr r c).em S ↔ r ∈ S := by
  simp [Termo.em, tr]
@[simp] theorem em_tr2 (S : List (Fin R)) (r s : Fin R) (c : ℕ) :
    (tr2 r s c).em S ↔ r ∈ S ∧ s ∈ S := by simp [Termo.em, tr2]

section lits2
variable {K : Type} [Fintype K]

/-- Literais de célula, rótulo e estado. -/
noncomputable def lx (b : Bool) (k : K) (τt τi τj : Termo R) : Cmd R :=
  pLit b [true, true] [τt, ⟨[], κ k⟩, τi, τj]
def ly (b : Bool) (τt τj : Termo R) : Cmd R := pLit b [true, false] [τt, τj]
def lz (b : Bool) (τt τj : Termo R) : Cmd R := pLit b [false, true] [τt, τj]

theorem gx {b : Bool} {k : K} {τt τi τj : Termo R} {E₀ : Env R} {S : List (Fin R)}
    (ht : τt.em S) (hi : τi.em S) (hj : τj.em S) {t i j : ℕ}
    (et : τt.val E₀ = t) (ei : τi.val E₀ = i) (ej : τj.val E₀ = j) :
    GeraU w (lx b k τt τi τj) E₀ S (codLiteral (ren (Var.x t k i j, b))) := by
  subst et ei ej; exact geraU_litX w b k ht hi hj

theorem gy {b : Bool} {τt τj : Termo R} {E₀ : Env R} {S : List (Fin R)}
    (ht : τt.em S) (hj : τj.em S) {t j : ℕ} (et : τt.val E₀ = t) (ej : τj.val E₀ = j) :
    GeraU w (ly b τt τj) E₀ S (codLiteral (ren (Var.y (K := K) t j, b))) := by
  subst et ej; exact geraU_litY w b ht hj

theorem gz {b : Bool} {τt τj : Termo R} {E₀ : Env R} {S : List (Fin R)}
    (ht : τt.em S) (hj : τj.em S) {t j : ℕ} (et : τt.val E₀ = t) (ej : τj.val E₀ = j) :
    GeraU w (lz b τt τj) E₀ S (codLiteral (ren (Var.z (K := K) t j, b))) := by
  subst et ej; exact geraU_litZ w b ht hj

theorem gcla {lits : List (Cmd R)} {C : Cla K} {E₀ : Env R} {S : List (Fin R)}
    (h : List.Forall₂ (fun c ℓ => GeraU w c E₀ S (codLiteral (ren ℓ))) lits C) :
    GeraU w (pCla lits) E₀ S (cc C) := geraU_cla w h

end lits2

/-! ## Família (E): exatamente um valor por célula, rótulo e estado -/

section familias
variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)

noncomputable def progE (rT1 rH t i : Fin R) : Cmd R :=
  .forU rT1 t (seqC ([pUmSo A.labs.length (fun j b => ly b (tr t 0) (tc j)),
      pUmSo A.sts.length (fun j b => lz b (tr t 0) (tc j))] ++
    Tab.ks.map fun k => .forU rH i (pUmSo (A.vals k).length fun j b => lx b k (tr t 0) (tr i 0) (tc j))))

omit [DecidableEq K] in
theorem geraU_progE {rT1 rH t i : Fin R} {E₀ : Env R} {S : List (Fin R)} {T H : ℕ}
    (h1 : rT1 ∈ S) (h2 : rH ∈ S) (ht : t ∉ S) (hi : i ∉ S) (hti : i ≠ t)
    (eT : E₀ rT1 = T + 1) (eH : E₀ rH = H) :
    GeraU w (progE A rT1 rH t i) E₀ S ((A.fE T H).flatMap cc) := by
  have e : (A.fE T H).flatMap cc = (List.range (E₀ rT1)).flatMap fun tt =>
      (umSo (A.rotulos tt)).flatMap cc ++ ((umSo (A.estados tt)).flatMap cc ++
        Tab.ks.flatMap fun k => (List.range H).flatMap fun ii => (umSo (A.celulas tt k ii)).flatMap cc) := by
    rw [eT]; simp [Tab.fE, List.flatMap_assoc, List.flatMap_append]
  rw [e]
  refine geraU_forU w ht h1 _ (fun tt => ?_)
  have ett : update E₀ t tt t = tt := by simp
  have g1 := geraU_umSo w A.labs.length (fun j b => ly b (tr t 0) (tc j)) (Var.y (K := K) tt)
    (E₀ := update E₀ t tt) (S := t :: S) (fun j b => gy w (by simp) (by simp) (by simp) (by simp))
  have g2 := geraU_umSo w A.sts.length (fun j b => lz b (tr t 0) (tc j)) (Var.z (K := K) tt)
    (E₀ := update E₀ t tt) (S := t :: S) (fun j b => gz w (by simp) (by simp) (by simp) (by simp))
  have g3 : GeraU w (seqC (Tab.ks.map fun k => Cmd.forU rH i
      (pUmSo (A.vals k).length fun j b => lx b k (tr t 0) (tr i 0) (tc j)))) (update E₀ t tt) (t :: S)
      (Tab.ks.flatMap fun k => (List.range H).flatMap fun ii => (umSo (A.celulas tt k ii)).flatMap cc) := by
    refine geraU_map w _ _ _ (fun k _ => ?_)
    have hiS : i ∉ t :: S := by simp [hti, hi]
    have hHS : rH ∈ t :: S := by simp [h2]
    have eH' : update E₀ t tt rH = H := by
      rw [update_of_ne (fun h : rH = t => ht (h ▸ h2)), eH]
    rw [← eH']
    refine geraU_forU w hiS hHS _ (fun ii => ?_)
    exact geraU_umSo w _ _ (Var.x tt k ii) (fun j b => gx w (by simp) (by simp) (by simp)
      (by simp [update_of_ne hti.symm]) (by simp) (by simp))
  exact geraU_congr w (geraU_append w (geraU_cons w g1 (geraU_cons w g2 (geraU_nil w _ _))) g3)
    (by simp [Tab.rotulos, Tab.estados, Tab.celulas])

/-! ## Família (P): configuração parada fica parada -/

noncomputable def progP (rT rH t i : Fin R) : Cmd R :=
  .forU rT t (seqC ([pCla [ly false (tr t 0) (tc (ix A.labs none)), ly true (tr t 1) (tc (ix A.labs none))]] ++
    (List.range A.sts.length).map (fun jv => pCla [ly false (tr t 0) (tc (ix A.labs none)),
      lz false (tr t 0) (tc jv), lz true (tr t 1) (tc jv)]) ++
    Tab.ks.map fun k => .forU rH i (seqC ((List.range (A.vals k).length).map fun a =>
      pCla [ly false (tr t 0) (tc (ix A.labs none)), lx false k (tr t 0) (tr i 0) (tc a),
        lx true k (tr t 1) (tr i 0) (tc a)]))))

omit [DecidableEq K] in
theorem geraU_progP {rT rH t i : Fin R} {E₀ : Env R} {S : List (Fin R)} {T H : ℕ}
    (h1 : rT ∈ S) (h2 : rH ∈ S) (ht : t ∉ S) (hi : i ∉ S) (hti : i ≠ t)
    (eT : E₀ rT = T) (eH : E₀ rH = H) :
    GeraU w (progP A rT rH t i) E₀ S ((A.fP T H).flatMap cc) := by
  have e : (A.fP T H).flatMap cc = (List.range (E₀ rT)).flatMap fun tt =>
      cc [(Var.y (K := K) tt (ix A.labs none), false), (.y (tt + 1) (ix A.labs none), true)] ++
      (((List.range A.sts.length).flatMap fun jv => cc [(Var.y (K := K) tt (ix A.labs none), false),
        (.z tt jv, false), (.z (tt + 1) jv, true)]) ++
      Tab.ks.flatMap fun k => (List.range H).flatMap fun ii => (List.range (A.vals k).length).flatMap
        fun a => cc [(.y tt (ix A.labs none), false), (.x tt k ii a, false), (.x (tt + 1) k ii a, true)]) := by
    rw [eT]; simp [Tab.fP, List.flatMap_assoc, List.flatMap_append, List.flatMap_map]
  rw [e]
  refine geraU_forU w ht h1 _ (fun tt => ?_)
  have g1 : GeraU w (pCla [ly false (tr t 0) (tc (ix A.labs none)), ly true (tr t 1) (tc (ix A.labs none))])
      (update E₀ t tt) (t :: S) (cc [(.y (K := K) tt (ix A.labs none), false), (.y (tt + 1) (ix A.labs none), true)]) :=
    gcla w (.cons (gy w (by simp) (by simp) (by simp) (by simp))
      (.cons (gy w (by simp) (by simp) (by simp) (by simp)) .nil))
  have g2 := geraU_map w (fun jv => pCla [ly false (tr t 0) (tc (ix A.labs none)),
      lz false (tr t 0) (tc jv), lz true (tr t 1) (tc jv)])
    (fun jv => cc [(.y (K := K) tt (ix A.labs none), false), (.z tt jv, false), (.z (tt + 1) jv, true)])
    (E₀ := update E₀ t tt) (S := t :: S) (List.range A.sts.length) (fun jv _ =>
      gcla w (.cons (gy w (by simp) (by simp) (by simp) (by simp))
        (.cons (gz w (by simp) (by simp) (by simp) (by simp))
          (.cons (gz w (by simp) (by simp) (by simp) (by simp)) .nil))))
  have g3 : GeraU w (seqC (Tab.ks.map fun k => Cmd.forU rH i (seqC ((List.range (A.vals k).length).map
      fun a => pCla [ly false (tr t 0) (tc (ix A.labs none)), lx false k (tr t 0) (tr i 0) (tc a),
        lx true k (tr t 1) (tr i 0) (tc a)])))) (update E₀ t tt) (t :: S)
      (Tab.ks.flatMap fun k => (List.range H).flatMap fun ii => (List.range (A.vals k).length).flatMap
        fun a => cc [(.y tt (ix A.labs none), false), (.x tt k ii a, false), (.x (tt + 1) k ii a, true)]) := by
    refine geraU_map w _ _ _ (fun k _ => ?_)
    have hiS : i ∉ t :: S := by simp [hti, hi]
    have hHS : rH ∈ t :: S := by simp [h2]
    have eH' : update E₀ t tt rH = H := by
      rw [update_of_ne (fun h : rH = t => ht (h ▸ h2)), eH]
    rw [← eH']
    refine geraU_forU w hiS hHS _ (fun ii => ?_)
    refine geraU_map w _ _ _ (fun a _ => ?_)
    exact gcla w (.cons (gy w (by simp) (by simp) (by simp [update_of_ne hti.symm]) (by simp))
      (.cons (gx w (by simp) (by simp) (by simp) (by simp [update_of_ne hti.symm]) (by simp) (by simp))
        (.cons (gx w (by simp) (by simp) (by simp) (by simp [update_of_ne hti.symm]) (by simp) (by simp))
          .nil)))
  exact geraU_congr w (geraU_append w (geraU_append w (geraU_cons w g1 (geraU_nil w _ _)) g2) g3)
    (by simp)

/-! ## Família (A): aceitação -/

noncomputable def progA (rT : Fin R) (acc : Γ A.k₁) : Cmd R :=
  seqC [pCla [ly true (tr rT 0) (tc (ix A.labs none))],
    pCla [lx true A.k₁ (tr rT 0) (tc 0) (tc (ix (A.vals A.k₁) (some acc)))]]

omit [DecidableEq K] in
theorem geraU_progA {rT : Fin R} {E₀ : Env R} {S : List (Fin R)} {T : ℕ} (acc : Γ A.k₁)
    (h1 : rT ∈ S) (eT : E₀ rT = T) :
    GeraU w (progA A rT acc) E₀ S ((A.fA T acc).flatMap cc) := by
  have g1 : GeraU w (pCla [ly true (tr rT 0) (tc (ix A.labs none))]) E₀ S
      (cc [(Var.y (K := K) T (ix A.labs none), true)]) :=
    gcla w (.cons (gy w (by simp [h1]) (by simp) (by simp [eT]) (by simp)) .nil)
  have g2 : GeraU w (pCla [lx true A.k₁ (tr rT 0) (tc 0) (tc (ix (A.vals A.k₁) (some acc)))]) E₀ S
      (cc [(Var.x T A.k₁ 0 (ix (A.vals A.k₁) (some acc)), true)]) :=
    gcla w (.cons (gx w (by simp [h1]) (by simp) (by simp) (by simp [eT]) (by simp) (by simp)) .nil)
  refine geraU_congr w (geraU_cons w g1 (geraU_cons w g2 (geraU_nil w _ _))) ?_
  simp [Tab.fA]

/-! ## Família (I): a linha inicial -/

omit [DecidableEq K] in
/-- Bloco da entrada: para cada bit `β` de `w`, as células `2k` e `2k+1`. -/
noncomputable def corpoPre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) (β : Bool) : Cmd R :=
  seqC [pCla [lx true k₀ (tc 0) (tr2 rj rj 0) (tc (bif β then j₁ else j₀))],
    pCla [lx true k₀ (tc 0) (tr2 rj rj 1) (tc (bif β then j₁ else j₀))], .inc rj]

omit [DecidableEq K] in
noncomputable def progPre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) : Cmd R :=
  .seq (.zero rj) (.forBits (corpoPre k₀ rj j₀ j₁ false) (corpoPre k₀ rj j₀ j₁ true))

omit [DecidableEq K] in
noncomputable def gPre (k₀ : K) (j₀ j₁ : ℕ) (β : Bool) (k : ℕ) : List Bool :=
  cc [(Var.x 0 k₀ (2 * k) (bif β then j₁ else j₀), true)] ++
    cc [(Var.x 0 k₀ (2 * k + 1) (bif β then j₁ else j₀), true)]

omit [DecidableEq K] in
theorem ex {b : Bool} {k : K} {τt τi τj : Termo R} {E : Env R} {t i j : ℕ}
    (et : τt.val E = t) (ei : τi.val E = i) (ej : τj.val E = j) :
    Emite w (lx b k τt τi τj) E (codLiteral (ren (Var.x t k i j, b))) := by
  subst et ei ej; exact emite_litX w b k τt τi τj E

omit [DecidableEq K] in
theorem sem_corpoPre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) (β : Bool) (E : Env R) :
    sem w (corpoPre k₀ rj j₀ j₁ β) E = (update E rj (E rj + 1), gPre k₀ j₀ j₁ β (E rj)) := by
  have h1 : Emite w (pCla [lx true k₀ (tc 0) (tr2 rj rj 0) (tc (bif β then j₁ else j₀))]) E
      (cc [(Var.x 0 k₀ (2 * E rj) (bif β then j₁ else j₀), true)]) :=
    emite_pCla w (.cons (ex w (by simp) (by simp; omega) (by simp)) .nil)
  have h2 : Emite w (pCla [lx true k₀ (tc 0) (tr2 rj rj 1) (tc (bif β then j₁ else j₀))]) E
      (cc [(Var.x 0 k₀ (2 * E rj + 1) (bif β then j₁ else j₀), true)]) :=
    emite_pCla w (.cons (ex w (by simp) (by simp; omega) (by simp)) .nil)
  unfold Emite at h1 h2
  simp only [corpoPre, seqC, sem, h1, h2, gPre]
  simp

omit [DecidableEq K] in
theorem semBits_pre (k₀ : K) (rj : Fin R) (j₀ j₁ : ℕ) : ∀ (l : List Bool) (E : Env R),
    semBits (sem w (corpoPre k₀ rj j₀ j₁ false)) (sem w (corpoPre k₀ rj j₀ j₁ true)) l E =
      (update E rj (E rj + l.length),
        (List.range l.length).flatMap fun k => gPre k₀ j₀ j₁ (l.getD k false) (E rj + k))
  | [], E => by simp [semBits]
  | b :: l, E => by
    have hb : (if b then sem w (corpoPre k₀ rj j₀ j₁ true) else sem w (corpoPre k₀ rj j₀ j₁ false)) E =
        (update E rj (E rj + 1), gPre k₀ j₀ j₁ b (E rj)) := by
      cases b <;> simp [sem_corpoPre]
    simp only [semBits, hb, semBits_pre k₀ rj j₀ j₁ l, update_idem, update_self]
    refine Prod.ext (by simp; congr 1; omega) ?_
    simp only [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp [Nat.add_assoc, Nat.add_comm 1]

omit [DecidableEq K] in
theorem geraU_progPre (k₀ : K) {rj : Fin R} (j₀ j₁ : ℕ) {E₀ : Env R} {S : List (Fin R)} (hj : rj ∉ S) :
    GeraU w (progPre k₀ rj j₀ j₁) E₀ S
      ((List.range w.length).flatMap fun k => gPre k₀ j₀ j₁ (w.getD k false) k) := by
  intro E hE
  simp only [progPre, sem, semBits_pre]
  refine ⟨by simp, fun r hr => ?_⟩
  have hr' : r ≠ rj := fun h => hj (h ▸ hr)
  simp [update_of_ne hr']

end familias

section listas

theorem flatMap_range_add {α : Type*} (F : ℕ → List α) (a b : ℕ) :
    (List.range (a + b)).flatMap F = (List.range a).flatMap F ++ (List.range b).flatMap fun j => F (a + j) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

theorem flatMap_range_dobro {α : Type*} (F : ℕ → List α) : ∀ n : ℕ,
    (List.range (2 * n)).flatMap F = (List.range n).flatMap fun k => F (2 * k) ++ F (2 * k + 1)
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, List.flatMap_append,
      List.flatMap_append, flatMap_range_dobro F n, List.range_succ, List.flatMap_append]
    simp

theorem getElem?_dup (w : List Bool) : ∀ k, (w.flatMap fun b => [b, b])[2 * k]? = w[k]? ∧
    (w.flatMap fun b => [b, b])[2 * k + 1]? = w[k]? := by
  induction w with
  | nil => intro k; simp
  | cons b w ih =>
    intro k
    rcases k with _ | k
    · simp
    · obtain ⟨h1, h2⟩ := ih k
      rw [List.flatMap_cons, show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
      exact ⟨h1, h2⟩

theorem length_dup (w : List Bool) : (w.flatMap fun b => [b, b]).length = 2 * w.length := by
  induction w with
  | nil => simp
  | cons b w ih => rw [List.flatMap_cons]; simp [ih]; ring

theorem pre_par {α : Type*} (e : Bool → α) (w : List Bool) {k : ℕ} (hk : k < w.length) :
    (((w.flatMap fun b => [b, b]) ++ [false, true]).map e)[2 * k]? = some (e (w.getD k false)) ∧
    (((w.flatMap fun b => [b, b]) ++ [false, true]).map e)[2 * k + 1]? = some (e (w.getD k false)) := by
  obtain ⟨h1, h2⟩ := getElem?_dup w k
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_append_left (by rw [length_dup]; omega),
    List.getElem?_append_left (by rw [length_dup]; omega), h1, h2, List.getElem?_eq_getElem hk,
    List.getD_eq_getElem _ _ hk]
  simp

theorem pre_fim {α : Type*} (e : Bool → α) (w : List Bool) :
    (((w.flatMap fun b => [b, b]) ++ [false, true]).map e)[2 * w.length]? = some (e false) ∧
    (((w.flatMap fun b => [b, b]) ++ [false, true]).map e)[2 * w.length + 1]? = some (e true) := by
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_append_right (by rw [length_dup]),
    List.getElem?_append_right (by rw [length_dup]; omega), length_dup]
  simp

theorem length_pre {α : Type*} (e : Bool → α) (w : List Bool) :
    (((w.flatMap fun b => [b, b]) ++ [false, true]).map e).length = 2 * w.length + 2 := by
  rw [List.length_map, List.length_append, length_dup]; rfl

end listas

section familias
variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)

open Classical in
/-- Índices de valores proibidos nas células de certificado. -/
noncomputable def livres (cands : List (Γ A.k₀)) : List ℕ :=
  (List.range (A.vals A.k₀).length).filter (fun j =>
    (A.vals A.k₀).getD j none ∉ none :: cands.map some)

/-- A saída esperada da família (I). -/
noncomputable def saidaI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (Q Rr H : ℕ) : List Bool :=
  cc [(Var.y (K := K) 0 (ix A.labs (some A.l₀)), true)] ++ cc [(Var.z (K := K) 0 (ix A.sts A.v₀), true)] ++
  (Tab.ks.filter (· ≠ A.k₀)).flatMap (fun k => (List.range H).flatMap fun ii =>
    cc [(Var.x 0 k ii (ix (A.vals k) none), true)]) ++
  ((List.range w.length).flatMap (fun k => gPre A.k₀ (ix (A.vals A.k₀) (some (e false)))
      (ix (A.vals A.k₀) (some (e true))) (w.getD k false) k) ++
    cc [(Var.x 0 A.k₀ (2 * w.length) (ix (A.vals A.k₀) (some (e false))), true)] ++
    cc [(Var.x 0 A.k₀ (2 * w.length + 1) (ix (A.vals A.k₀) (some (e true))), true)] ++
    (List.range Q).flatMap (fun jj => (livres A cands).flatMap (fun a =>
        cc [(Var.x 0 A.k₀ (2 * w.length + 2 + jj) a, false)]) ++
      cc [(Var.x 0 A.k₀ (2 * w.length + 2 + jj) (ix (A.vals A.k₀) none), false),
        (Var.x 0 A.k₀ (2 * w.length + 2 + jj + 1) (ix (A.vals A.k₀) none), true)]) ++
    (List.range Rr).flatMap (fun jj => cc [(Var.x 0 A.k₀ (2 * w.length + 2 + Q + jj)
      (ix (A.vals A.k₀) none), true)]))

theorem fI_saida (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) {Q Rr H : ℕ}
    (hH : H = 2 * w.length + 2 + Q + Rr) (hR : 0 < Rr) :
    (A.fI ((w.flatMap (fun b => [b, b]) ++ [false, true]).map e) cands Q H).flatMap cc =
      saidaI w A e cands Q Rr H := by
  have hlen := length_pre e w
  unfold Tab.fI saidaI
  rw [List.flatMap_append, List.flatMap_append]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · simp [List.flatMap_assoc, List.flatMap_map]
  · rw [List.flatMap_assoc]
    conv_lhs => rw [hH]
    rw [flatMap_range_add, flatMap_range_add, show 2 * w.length + 2 = 2 * w.length + 1 + 1 by ring,
      List.range_succ, List.range_succ, List.flatMap_append, List.flatMap_append, flatMap_range_dobro]
    simp only [hlen]
    refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_) ?_) ?_
    · refine List.flatMap_congr (fun k hk => ?_)
      have hk' : k < w.length := List.mem_range.mp hk
      obtain ⟨p1, p2⟩ := pre_par e w hk'
      rw [ite_eq_left (by omega), ite_eq_left (by omega), p1, p2]
      cases w.getD k false <;> simp [gPre]
    · obtain ⟨p1, -⟩ := pre_fim e w
      rw [List.flatMap_singleton, ite_eq_left (by omega), p1]
      simp
    · obtain ⟨-, p2⟩ := pre_fim e w
      rw [List.flatMap_singleton, ite_eq_left (by omega), p2]
      simp
    · refine List.flatMap_congr (fun j hj => ?_)
      have hj' : j < Q := List.mem_range.mp hj
      rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
      simp [livres, List.flatMap_map]
    · refine List.flatMap_congr (fun j hj => ?_)
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp

/-- O programa da família (I). -/
noncomputable def progI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (rH rn rip rQ rm rRr t : Fin R) :
    Cmd R :=
  seqC [pCla [ly true (tc 0) (tc (ix A.labs (some A.l₀)))],
    pCla [lz true (tc 0) (tc (ix A.sts A.v₀))],
    seqC ((Tab.ks.filter (· ≠ A.k₀)).map fun k =>
      .forU rH t (pCla [lx true k (tc 0) (tr t 0) (tc (ix (A.vals k) none))])),
    progPre A.k₀ t (ix (A.vals A.k₀) (some (e false))) (ix (A.vals A.k₀) (some (e true))),
    pCla [lx true A.k₀ (tc 0) (tr2 rn rn 0) (tc (ix (A.vals A.k₀) (some (e false))))],
    pCla [lx true A.k₀ (tc 0) (tr2 rn rn 1) (tc (ix (A.vals A.k₀) (some (e true))))],
    .forU rQ t (seqC ((livres A cands).map (fun a => pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc a)]) ++
      [pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc (ix (A.vals A.k₀) none)),
        lx true A.k₀ (tc 0) (tr2 rip t 1) (tc (ix (A.vals A.k₀) none))]])),
    .forU rRr t (pCla [lx true A.k₀ (tc 0) (tr2 rm t 0) (tc (ix (A.vals A.k₀) none))])]

theorem geraU_progI (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) {rH rn rip rQ rm rRr t : Fin R}
    {E₀ : Env R} {S : List (Fin R)} {Q Rr H : ℕ}
    (hH : rH ∈ S) (hn : rn ∈ S) (hip : rip ∈ S) (hQ : rQ ∈ S) (hm : rm ∈ S) (hRr : rRr ∈ S) (ht : t ∉ S)
    (eH : E₀ rH = H) (en : E₀ rn = w.length) (eip : E₀ rip = 2 * w.length + 2) (eQ : E₀ rQ = Q)
    (em : E₀ rm = 2 * w.length + 2 + Q) (eR : E₀ rRr = Rr) :
    GeraU w (progI A e cands rH rn rip rQ rm rRr t) E₀ S (saidaI w A e cands Q Rr H) := by
  have upd : ∀ {r : Fin R} (k : ℕ), r ∈ S → update E₀ t k r = E₀ r := by
    intro r k hr; exact update_of_ne (fun h : r = t => ht (h ▸ hr)) _ _
  have g1 : GeraU w (pCla [ly true (tc 0) (tc (ix A.labs (some A.l₀)))]) E₀ S
      (cc [(Var.y (K := K) 0 (ix A.labs (some A.l₀)), true)]) :=
    gcla w (.cons (gy w (by simp) (by simp) (by simp) (by simp)) .nil)
  have g2 : GeraU w (pCla [lz true (tc 0) (tc (ix A.sts A.v₀))]) E₀ S
      (cc [(Var.z (K := K) 0 (ix A.sts A.v₀), true)]) :=
    gcla w (.cons (gz w (by simp) (by simp) (by simp) (by simp)) .nil)
  have g3 : GeraU w (seqC ((Tab.ks.filter (· ≠ A.k₀)).map fun k =>
      Cmd.forU rH t (pCla [lx true k (tc 0) (tr t 0) (tc (ix (A.vals k) none))]))) E₀ S
      ((Tab.ks.filter (· ≠ A.k₀)).flatMap (fun k => (List.range H).flatMap fun ii =>
        cc [(Var.x 0 k ii (ix (A.vals k) none), true)])) := by
    refine geraU_map w _ _ _ (fun k _ => ?_)
    rw [← eH]
    exact geraU_forU w ht hH _ (fun ii => gcla w (.cons (gx w (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp)) .nil))
  have g4 := geraU_progPre w A.k₀ (ix (A.vals A.k₀) (some (e false))) (ix (A.vals A.k₀) (some (e true)))
    (E₀ := E₀) ht
  have g5 : GeraU w (pCla [lx true A.k₀ (tc 0) (tr2 rn rn 0) (tc (ix (A.vals A.k₀) (some (e false))))]) E₀ S
      (cc [(Var.x 0 A.k₀ (2 * w.length) (ix (A.vals A.k₀) (some (e false))), true)]) :=
    gcla w (.cons (gx w (by simp) (by simp [hn]) (by simp) (by simp) (by simp [en]; ring) (by simp)) .nil)
  have g6 : GeraU w (pCla [lx true A.k₀ (tc 0) (tr2 rn rn 1) (tc (ix (A.vals A.k₀) (some (e true))))]) E₀ S
      (cc [(Var.x 0 A.k₀ (2 * w.length + 1) (ix (A.vals A.k₀) (some (e true))), true)]) :=
    gcla w (.cons (gx w (by simp) (by simp [hn]) (by simp) (by simp) (by simp [en]; ring) (by simp)) .nil)
  have g7 : GeraU w (.forU rQ t (seqC ((livres A cands).map (fun a =>
      pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc a)]) ++
      [pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc (ix (A.vals A.k₀) none)),
        lx true A.k₀ (tc 0) (tr2 rip t 1) (tc (ix (A.vals A.k₀) none))]]))) E₀ S
      ((List.range Q).flatMap (fun jj => (livres A cands).flatMap (fun a =>
        cc [(Var.x 0 A.k₀ (2 * w.length + 2 + jj) a, false)]) ++
        cc [(Var.x 0 A.k₀ (2 * w.length + 2 + jj) (ix (A.vals A.k₀) none), false),
          (Var.x 0 A.k₀ (2 * w.length + 2 + jj + 1) (ix (A.vals A.k₀) none), true)])) := by
    rw [← eQ]
    refine geraU_forU w ht hQ _ (fun jj => ?_)
    have a1 := geraU_map w (fun a => pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc a)])
      (fun a => cc [(Var.x 0 A.k₀ (2 * w.length + 2 + jj) a, false)]) (E₀ := update E₀ t jj) (S := t :: S)
      (livres A cands) (fun a _ => gcla w (.cons (gx w (by simp) (by simp [hip]) (by simp) (by simp)
        (by simp [upd _ hip, eip]) (by simp)) .nil))
    have a2 : GeraU w (pCla [lx false A.k₀ (tc 0) (tr2 rip t 0) (tc (ix (A.vals A.k₀) none)),
        lx true A.k₀ (tc 0) (tr2 rip t 1) (tc (ix (A.vals A.k₀) none))]) (update E₀ t jj) (t :: S)
        (cc [(Var.x 0 A.k₀ (2 * w.length + 2 + jj) (ix (A.vals A.k₀) none), false),
          (Var.x 0 A.k₀ (2 * w.length + 2 + jj + 1) (ix (A.vals A.k₀) none), true)]) :=
      gcla w (.cons (gx w (by simp) (by simp [hip]) (by simp) (by simp) (by simp [upd _ hip, eip])
        (by simp)) (.cons (gx w (by simp) (by simp [hip]) (by simp) (by simp)
        (by simp [upd _ hip, eip]) (by simp)) .nil))
    exact geraU_congr w (geraU_append w a1 (geraU_cons w a2 (geraU_nil w _ _))) (by simp)
  have g8 : GeraU w (.forU rRr t (pCla [lx true A.k₀ (tc 0) (tr2 rm t 0) (tc (ix (A.vals A.k₀) none))]))
      E₀ S ((List.range Rr).flatMap (fun jj => cc [(Var.x 0 A.k₀ (2 * w.length + 2 + Q + jj)
        (ix (A.vals A.k₀) none), true)])) := by
    rw [← eR]
    exact geraU_forU w ht hRr _ (fun jj => gcla w (.cons (gx w (by simp) (by simp [hm]) (by simp)
      (by simp) (by simp [upd _ hm, em]) (by simp)) .nil))
  refine geraU_congr w (geraU_cons w g1 (geraU_cons w g2 (geraU_cons w g3 (geraU_cons w g4
    (geraU_cons w g5 (geraU_cons w g6 (geraU_cons w g7 (geraU_cons w g8 (geraU_nil w _ _))))))))) ?_
  simp only [saidaI, List.append_assoc, List.append_nil]

/-! ## Família (R): transições -/

theorem filter_range_lt (H c : ℕ) :
    (List.range H).filter (fun j => decide (c + j < H)) = List.range (H - c) := by
  by_cases hc : c ≤ H
  · conv_lhs => rw [show H = (H - c) + c by omega]
    rw [List.range_add, List.filter_append, List.filter_eq_self.mpr, List.filter_eq_nil_iff.mpr,
      List.append_nil]
    · intro a ha
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      simp; omega
    · intro a ha
      have := List.mem_range.mp ha
      simp; omega
  · rw [show H - c = 0 by omega, List.range_zero, List.filter_eq_nil_iff.mpr]
    intro a ha
    have := List.mem_range.mp ha
    simp; omega

omit [DecidableEq K] in
/-- Literais dos antecedentes `antes t jl jv p`. -/
noncomputable def antesC (t : Fin R) (jl jv : ℕ) (p : A.Pat) : List (Cmd R) :=
  ly false (tr t 0) (tc jl) :: lz false (tr t 0) (tc jv) ::
    Tab.ks.flatMap fun k => (List.finRange A.d).map fun ii => lx false k (tr t 0) (tc ii.val) (tc (p k ii).val)

omit [DecidableEq K] in
theorem forall₂_antes {t : Fin R} {jl jv : ℕ} {p : A.Pat} {E : Env R} {S : List (Fin R)} {tt : ℕ}
    (ht : t ∈ S) (et : E t = tt) :
    List.Forall₂ (fun c ℓ => GeraU w c E S (codLiteral (ren ℓ))) (antesC A t jl jv p) (A.antes tt jl jv p) :=
  .cons (gy w (by simp [ht]) (by simp) (by simp [et]) (by simp))
    (.cons (gz w (by simp [ht]) (by simp) (by simp [et]) (by simp))
      (forall₂_flatMap _ _ _ (fun k _ => forall₂_map_map _ _ _ (fun ii _ =>
        gx w (by simp [ht]) (by simp) (by simp) (by simp [et]) (by simp) (by simp)))))

omit [DecidableEq K] in
/-- Os consequentes de uma transição, prefixados pelos antecedentes `ant`. -/
noncomputable def progConseq (rHb t i : Fin R) (DD : ℕ) (ant : List (Cmd R)) (r : Turing.TM2.Cfg Γ Λ σ) :
    Cmd R :=
  seqC ([pCla (ant ++ [ly true (tr t 1) (tc (ix A.labs r.l))]),
      pCla (ant ++ [lz true (tr t 1) (tc (ix A.sts r.var))])] ++
    Tab.ks.map fun k => seqC (((List.range (r.stk k).length).map fun ii =>
        pCla (ant ++ [lx true k (tr t 1) (tc ii) (tc (ix (A.vals k) (r.stk k)[ii]?))])) ++
      [.forU rHb i (seqC ((List.range (A.vals k).length).map fun a =>
        pCla (ant ++ [lx false k (tr t 0) (tr i A.d) (tc a), lx true k (tr t 1) (tr i (r.stk k).length) (tc a)])))] ++
      (List.range (A.d + DD - (r.stk k).length)).map fun e =>
        if e < DD then seqC ((List.range (A.vals k).length).map fun a =>
          pCla (ant ++ [lx false k (tr t 0) (tr rHb (A.d + e)) (tc a),
            lx true k (tr t 1) (tr rHb ((r.stk k).length + e)) (tc a)]))
        else pCla (ant ++ [lx true k (tr t 1) (tr rHb ((r.stk k).length + e)) (tc (ix (A.vals k) none))])))

omit [DecidableEq K] in
/-- A saída esperada dos consequentes. -/
noncomputable def saidaC (DD : ℕ) (ant : Cla K) (tt Hb : ℕ) (r : Turing.TM2.Cfg Γ Λ σ) : List Bool :=
  cc (ant ++ [(Var.y (tt + 1) (ix A.labs r.l), true)]) ++ (cc (ant ++ [(Var.z (tt + 1) (ix A.sts r.var), true)]) ++
  Tab.ks.flatMap fun k => (List.range (r.stk k).length).flatMap (fun ii =>
      cc (ant ++ [(Var.x (tt + 1) k ii (ix (A.vals k) (r.stk k)[ii]?), true)])) ++
    ((List.range Hb).flatMap (fun j => (List.range (A.vals k).length).flatMap fun a =>
        cc (ant ++ [(Var.x tt k (A.d + j) a, false), (Var.x (tt + 1) k ((r.stk k).length + j) a, true)])) ++
      (List.range (A.d + DD - (r.stk k).length)).flatMap fun e =>
        if e < DD then (List.range (A.vals k).length).flatMap (fun a =>
          cc (ant ++ [(Var.x tt k (A.d + (Hb + e)) a, false),
            (Var.x (tt + 1) k ((r.stk k).length + (Hb + e)) a, true)]))
        else cc (ant ++ [(Var.x (tt + 1) k ((r.stk k).length + (Hb + e)) (ix (A.vals k) none), true)])))

omit [DecidableEq K] in
theorem conseq_saida {DD Hb H : ℕ} (hH : H = Hb + A.d + DD) (ant : Cla K) (tt : ℕ)
    (r : Turing.TM2.Cfg Γ Λ σ) (hr : ∀ k, (r.stk k).length ≤ A.d + DD) :
    (A.conseq H tt r).flatMap (fun C => cc (ant ++ C)) = saidaC A DD ant tt Hb r := by
  unfold Tab.conseq saidaC
  rw [List.flatMap_append, List.flatMap_assoc]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  refine congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) rfl (List.flatMap_congr (fun k _ => ?_)))
  rw [List.flatMap_append, List.flatMap_map, filter_range_lt,
    show H - (r.stk k).length = Hb + (A.d + DD - (r.stk k).length) by have := hr k; omega,
    flatMap_range_add, List.flatMap_append, List.flatMap_assoc, List.flatMap_assoc]
  refine congrArg₂ (· ++ ·) rfl (congrArg₂ (· ++ ·) (List.flatMap_congr (fun j hj => ?_))
    (List.flatMap_congr (fun e he => ?_)))
  · have := List.mem_range.mp hj
    rw [ite_eq_left (by omega), List.flatMap_map]
  · have := List.mem_range.mp he
    by_cases h : e < DD
    · rw [ite_eq_left (by omega), ite_eq_left h, List.flatMap_map]
    · rw [ite_eq_right (by omega), ite_eq_right h]
      simp

omit [DecidableEq K] in
theorem geraU_progConseq {rHb t i : Fin R} {DD : ℕ} {ant : List (Cmd R)} {antL : Cla K}
    {E₀ : Env R} {S : List (Fin R)} {tt Hb : ℕ} (r : Turing.TM2.Cfg Γ Λ σ)
    (hHb : rHb ∈ S) (ht : t ∈ S) (hi : i ∉ S) (et : E₀ t = tt) (eHb : E₀ rHb = Hb)
    (hant : ∀ (E : Env R) (S' : List (Fin R)), t ∈ S' → E t = tt →
      List.Forall₂ (fun c ℓ => GeraU w c E S' (codLiteral (ren ℓ))) ant antL) :
    GeraU w (progConseq A rHb t i DD ant r) E₀ S (saidaC A DD antL tt Hb r) := by
  have hti : t ≠ i := fun h => hi (h ▸ ht)
  have g1 : GeraU w (pCla (ant ++ [ly true (tr t 1) (tc (ix A.labs r.l))])) E₀ S
      (cc (antL ++ [(Var.y (tt + 1) (ix A.labs r.l), true)])) :=
    gcla w (forall₂_append (hant E₀ S ht et) (.cons (gy w (by simp [ht]) (by simp) (by simp [et])
      (by simp)) .nil))
  have g2 : GeraU w (pCla (ant ++ [lz true (tr t 1) (tc (ix A.sts r.var))])) E₀ S
      (cc (antL ++ [(Var.z (tt + 1) (ix A.sts r.var), true)])) :=
    gcla w (forall₂_append (hant E₀ S ht et) (.cons (gz w (by simp [ht]) (by simp) (by simp [et])
      (by simp)) .nil))
  have g3 : ∀ k : K, GeraU w (seqC (((List.range (r.stk k).length).map fun ii =>
        pCla (ant ++ [lx true k (tr t 1) (tc ii) (tc (ix (A.vals k) (r.stk k)[ii]?))])) ++
      [.forU rHb i (seqC ((List.range (A.vals k).length).map fun a =>
        pCla (ant ++ [lx false k (tr t 0) (tr i A.d) (tc a), lx true k (tr t 1) (tr i (r.stk k).length) (tc a)])))] ++
      (List.range (A.d + DD - (r.stk k).length)).map fun e =>
        if e < DD then seqC ((List.range (A.vals k).length).map fun a =>
          pCla (ant ++ [lx false k (tr t 0) (tr rHb (A.d + e)) (tc a),
            lx true k (tr t 1) (tr rHb ((r.stk k).length + e)) (tc a)]))
        else pCla (ant ++ [lx true k (tr t 1) (tr rHb ((r.stk k).length + e)) (tc (ix (A.vals k) none))])))
      E₀ S ((List.range (r.stk k).length).flatMap (fun ii =>
        cc (antL ++ [(Var.x (tt + 1) k ii (ix (A.vals k) (r.stk k)[ii]?), true)])) ++
      ((List.range Hb).flatMap (fun j => (List.range (A.vals k).length).flatMap fun a =>
          cc (antL ++ [(Var.x tt k (A.d + j) a, false), (Var.x (tt + 1) k ((r.stk k).length + j) a, true)])) ++
        (List.range (A.d + DD - (r.stk k).length)).flatMap fun e =>
          if e < DD then (List.range (A.vals k).length).flatMap (fun a =>
            cc (antL ++ [(Var.x tt k (A.d + (Hb + e)) a, false),
              (Var.x (tt + 1) k ((r.stk k).length + (Hb + e)) a, true)]))
          else cc (antL ++ [(Var.x (tt + 1) k ((r.stk k).length + (Hb + e)) (ix (A.vals k) none), true)]))) := by
    intro k
    have a1 := geraU_map w (fun ii => pCla (ant ++ [lx true k (tr t 1) (tc ii) (tc (ix (A.vals k) (r.stk k)[ii]?))]))
      (fun ii => cc (antL ++ [(Var.x (tt + 1) k ii (ix (A.vals k) (r.stk k)[ii]?), true)])) (E₀ := E₀) (S := S)
      (List.range (r.stk k).length) (fun ii _ => gcla w (forall₂_append (hant E₀ S ht et)
        (.cons (gx w (by simp [ht]) (by simp) (by simp) (by simp [et]) (by simp) (by simp)) .nil)))
    have a2 : GeraU w (.forU rHb i (seqC ((List.range (A.vals k).length).map fun a =>
        pCla (ant ++ [lx false k (tr t 0) (tr i A.d) (tc a), lx true k (tr t 1) (tr i (r.stk k).length) (tc a)]))))
        E₀ S ((List.range Hb).flatMap (fun j => (List.range (A.vals k).length).flatMap fun a =>
          cc (antL ++ [(Var.x tt k (A.d + j) a, false), (Var.x (tt + 1) k ((r.stk k).length + j) a, true)]))) := by
      rw [← eHb]
      refine geraU_forU w hi hHb _ (fun j => ?_)
      have etj : update E₀ i j t = tt := by rw [update_of_ne hti, et]
      exact geraU_map w _ (fun a => cc (antL ++ [(Var.x tt k (A.d + j) a, false),
          (Var.x (tt + 1) k ((r.stk k).length + j) a, true)])) _ (fun a _ =>
        gcla w (forall₂_append (hant _ _ (List.mem_cons_of_mem _ ht) etj)
          (.cons (gx w (by simp [ht]) (by simp) (by simp) (by simp [etj]) (by simp; omega) (by simp))
            (.cons (gx w (by simp [ht]) (by simp) (by simp) (by simp [etj]) (by simp; omega) (by simp)) .nil))))
    have a3 := geraU_map w (fun e =>
        if e < DD then seqC ((List.range (A.vals k).length).map fun a =>
          pCla (ant ++ [lx false k (tr t 0) (tr rHb (A.d + e)) (tc a),
            lx true k (tr t 1) (tr rHb ((r.stk k).length + e)) (tc a)]))
        else pCla (ant ++ [lx true k (tr t 1) (tr rHb ((r.stk k).length + e)) (tc (ix (A.vals k) none))]))
      (fun e => if e < DD then (List.range (A.vals k).length).flatMap (fun a =>
            cc (antL ++ [(Var.x tt k (A.d + (Hb + e)) a, false),
              (Var.x (tt + 1) k ((r.stk k).length + (Hb + e)) a, true)]))
          else cc (antL ++ [(Var.x (tt + 1) k ((r.stk k).length + (Hb + e)) (ix (A.vals k) none), true)]))
      (E₀ := E₀) (S := S) (List.range (A.d + DD - (r.stk k).length)) (fun e _ => by
        by_cases h : e < DD
        · rw [ite_eq_left h, ite_eq_left h]
          exact geraU_map w _ _ _ (fun a _ => gcla w (forall₂_append (hant E₀ S ht et)
            (.cons (gx w (by simp [ht]) (by simp [hHb]) (by simp) (by simp [et]) (by simp [eHb]; omega) (by simp))
              (.cons (gx w (by simp [ht]) (by simp [hHb]) (by simp) (by simp [et]) (by simp [eHb]; omega)
                (by simp)) .nil))))
        · rw [ite_eq_right h, ite_eq_right h]
          exact gcla w (forall₂_append (hant E₀ S ht et)
            (.cons (gx w (by simp [ht]) (by simp [hHb]) (by simp) (by simp [et]) (by simp [eHb]; omega)
              (by simp)) .nil)))
    exact geraU_append w (geraU_append w a1 (geraU_cons w a2 (geraU_nil w _ _))) a3 |>
      (geraU_congr w · (by simp))
  have g3' := geraU_map w _ _ (E₀ := E₀) (S := S) (Tab.ks (K := K)) (fun k _ => g3 k)
  exact geraU_congr w (geraU_append w (geraU_cons w g1 (geraU_cons w g2 (geraU_nil w _ _))) g3')
    (by simp [saidaC])

noncomputable def progRp (rHb t i : Fin R) (DD jl jv : ℕ) (p : A.Pat) : Cmd R :=
  match A.labs[jl]?, A.sts[jv]? with
  | some (some l), some v => progConseq A rHb t i DD (antesC A t jl jv p) (Turing.TM2.stepAux (A.M l) v (A.janela p))
  | _, _ => seqC []

/-- O programa da família (R). -/
noncomputable def progR (rT rHb t i : Fin R) (DD : ℕ) : Cmd R :=
  .forU rT t (seqC ((List.range A.labs.length).map fun jl => seqC ((List.range A.sts.length).map fun jv =>
    seqC (A.pats.map fun p => progRp A rHb t i DD jl jv p))))

noncomputable def saidaR (DD T Hb : ℕ) : List Bool :=
  (List.range T).flatMap fun tt => (List.range A.labs.length).flatMap fun jl =>
    (List.range A.sts.length).flatMap fun jv => A.pats.flatMap fun p =>
      match A.labs[jl]?, A.sts[jv]? with
      | some (some l), some v => saidaC A DD (A.antes tt jl jv p) tt Hb (Turing.TM2.stepAux (A.M l) v (A.janela p))
      | _, _ => []

omit [DecidableEq K] [Fintype K] in
theorem length_janela (p : A.Pat) (k : K) : (A.janela p k).length ≤ A.d := by
  unfold Tab.janela
  exact (length_tomaSome_le _).trans (by simp)

theorem fR_saida {DD T Hb H : ℕ} (hH : H = Hb + A.d + DD) (hemp : ∀ l, ClayPvsNPProof.ATK.CookLevinBase.emp (A.M l) ≤ DD) :
    (A.fR T H).flatMap cc = saidaR A DD T Hb := by
  unfold Tab.fR saidaR
  simp only [List.flatMap_assoc]
  refine List.flatMap_congr (fun tt _ => List.flatMap_congr (fun jl _ => List.flatMap_congr (fun jv _ =>
    List.flatMap_congr (fun p _ => ?_))))
  rcases h1 : A.labs[jl]? with _ | _ | l <;> rcases h2 : A.sts[jv]? with _ | v <;> try simp
  rw [List.flatMap_map]
  exact conseq_saida A hH _ tt _ (fun k => (ClayPvsNPProof.ATK.CookLevinBase.length_stepAux_le _ _ _ k).trans
    (Nat.add_le_add (length_janela A p k) (hemp l)))

theorem geraU_progR {rT rHb t i : Fin R} {DD : ℕ} {E₀ : Env R} {S : List (Fin R)} {T Hb : ℕ}
    (hT : rT ∈ S) (hHb : rHb ∈ S) (ht : t ∉ S) (hi : i ∉ S) (hti : i ≠ t)
    (eT : E₀ rT = T) (eHb : E₀ rHb = Hb) :
    GeraU w (progR A rT rHb t i DD) E₀ S (saidaR A DD T Hb) := by
  unfold progR saidaR
  rw [← eT]
  refine geraU_forU w ht hT _ (fun tt => geraU_map w _ _ _ (fun jl _ => geraU_map w _ _ _ (fun jv _ =>
    geraU_map w _ _ _ (fun p _ => ?_))))
  unfold progRp
  rcases h1 : A.labs[jl]? with _ | _ | l <;> rcases h2 : A.sts[jv]? with _ | v <;>
    try exact geraU_nil w _ _
  exact geraU_progConseq w A _ (List.mem_cons_of_mem _ hHb) (List.mem_cons_self ..) (by simp [hti, hi])
    (by simp) (by rw [update_of_ne (fun h : rHb = t => ht (h ▸ hHb)), eHb])
    (fun E S' ht' et' => forall₂_antes w A ht' et')

/-! ## O tableau inteiro -/

/-- Registradores da fase de emissão. -/
structure Regs (R : ℕ) where
  rT : Fin R
  rT1 : Fin R
  rH : Fin R
  rHb : Fin R
  rn : Fin R
  rip : Fin R
  rQ : Fin R
  rm : Fin R
  rRr : Fin R
  t : Fin R
  i : Fin R

/-- Os registradores de parâmetros. -/
def Regs.params (g : Regs R) : List (Fin R) := [g.rT, g.rT1, g.rH, g.rHb, g.rn, g.rip, g.rQ, g.rm, g.rRr]

/-- O programa de emissão do tableau. -/
noncomputable def progTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁) (DD : ℕ) :
    Cmd R :=
  seqC [progE A g.rT1 g.rH g.t g.i, progI A e cands g.rH g.rn g.rip g.rQ g.rm g.rRr g.t,
    progR A g.rT g.rHb g.t g.i DD, progP A g.rT g.rH g.t g.i, progA A g.rT acc]

/-- Valores dos parâmetros. -/
structure Vals (g : Regs R) (E₀ : Env R) (n Q T Hb Rr H : ℕ) : Prop where
  eT : E₀ g.rT = T
  eT1 : E₀ g.rT1 = T + 1
  eH : E₀ g.rH = H
  eHb : E₀ g.rHb = Hb
  en : E₀ g.rn = n
  eip : E₀ g.rip = 2 * n + 2
  eQ : E₀ g.rQ = Q
  em : E₀ g.rm = 2 * n + 2 + Q
  eR : E₀ g.rRr = Rr

theorem geraU_progTab (g : Regs R) (e : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (acc : Γ A.k₁)
    {DD Q T Hb Rr H : ℕ} {E₀ : Env R} (hv : Vals g E₀ w.length Q T Hb Rr H)
    (ht : g.t ∉ g.params) (hi : g.i ∉ g.params) (hti : g.i ≠ g.t)
    (hH₁ : H = 2 * w.length + 2 + Q + Rr) (hH₂ : H = Hb + A.d + DD) (hR : 0 < Rr)
    (hemp : ∀ l, ClayPvsNPProof.ATK.CookLevinBase.emp (A.M l) ≤ DD) :
    GeraU w (progTab A g e cands acc DD) E₀ g.params
      ((A.formula ((w.flatMap (fun b => [b, b]) ++ [false, true]).map e) cands Q T H acc).flatMap cc) := by
  have m : ∀ r ∈ g.params, r ∈ g.params := fun _ h => h
  simp only [Regs.params] at ht hi
  have g1 := geraU_progE w A (S := g.params) (by simp [Regs.params]) (by simp [Regs.params])
    (by simpa [Regs.params] using ht) (by simpa [Regs.params] using hi) hti hv.eT1 hv.eH
  have g2 := geraU_progI w A e cands (S := g.params) (by simp [Regs.params]) (by simp [Regs.params])
    (by simp [Regs.params]) (by simp [Regs.params]) (by simp [Regs.params]) (by simp [Regs.params])
    (by simpa [Regs.params] using ht) hv.eH hv.en hv.eip hv.eQ hv.em hv.eR
  have g3 := geraU_progR w A (DD := DD) (S := g.params) (by simp [Regs.params]) (by simp [Regs.params])
    (by simpa [Regs.params] using ht) (by simpa [Regs.params] using hi) hti hv.eT hv.eHb
  have g4 := geraU_progP w A (S := g.params) (by simp [Regs.params]) (by simp [Regs.params])
    (by simpa [Regs.params] using ht) (by simpa [Regs.params] using hi) hti hv.eT hv.eH
  have g5 := geraU_progA w A acc (S := g.params) (by simp [Regs.params]) hv.eT
  refine geraU_congr w (geraU_cons w g1 (geraU_cons w g2 (geraU_cons w g3 (geraU_cons w g4
    (geraU_cons w g5 (geraU_nil w _ _)))))) ?_
  rw [Tab.formula, List.flatMap_append, List.flatMap_append, List.flatMap_append, List.flatMap_append,
    fI_saida w A e cands hH₁ hR, fR_saida A hH₂ hemp]
  simp only [List.append_assoc, List.append_nil]

end familias

end ClayPvsNPProof.ATK.CookLevinGerador

