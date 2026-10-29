# P vs NP — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-p-vs-np-statement`](https://github.com/ShantiDraconis/clay-p-vs-np-statement),
fixado no commit `6375290`. O alvo é `ClayPvsNP.P_eq_NP`, sem redefinição.

`P_eq_NP` é uma proposição a DECIDIR: a prova é `theorem main : ClayPvsNP.P_eq_NP` ou `theorem main : ¬ ClayPvsNP.P_eq_NP`.

Estado: sem prova. `OPEN_MATH = true`.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayPvsNPProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.
