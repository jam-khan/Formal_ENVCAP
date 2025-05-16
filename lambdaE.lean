import Lean

open Definitions

variable  {v        : Definitions.Exp}
variable  {A E E'   : Definitions.Typ}

theorem value_weaken:
    ∀ E v A,
        HasType E v A →
        ∀ E', Value v →
        HasType E' v A :=
    by  intro E v A H E' Hv <;> induction H generalizing E' <;> cases Hv
        case tint E n                   =>  exact HasType.tint E' n
        case tunit E                    =>  exact HasType.tunit E'
        case tmrg E A B e1 e2           =>  apply HasType.tmrg; apply A; assumption; apply B; assumption
        case tclos E' E1' A' e' ev' B'  =>  apply HasType.tclos; repeat assumption
        case trcd E e A l               =>  apply HasType.trcd; apply A; assumption

theorem lookupv_value:
    ∀ v n v',   LookupV v n v'  →
                Value v →
                Value v' :=
    by  intro v n v' Hl
        induction Hl <;> intro Hv <;> cases Hv <;> try assumption
        case lvsucc v1 v2 _  => apply v1; assumption

theorem lookup_pres_ctx:
    ∀ E n A,    Lookup E n A → ∀ v v',
                LookupV v n v'  →
                Value v         →
                HasType top v E →
                HasType E v' A  :=
    by
    intro E n A Hl
    induction Hl <;> intro v v' Hlv Hv Ht
    case lzero =>
        try repeat cases Hlv <;> try repeat cases Hv <;> cases Ht
        case tmrg A' A'' B' v H1 H2 H3 =>
            apply value_weaken <;> assumption
    case lsucc v1 v2 H H_inner  =>
        try repeat cases Hlv <;> try repeat cases Hv <;> cases H_inner
        case lvsucc v1 v2 Hv'   =>
            sorry
