import Lean
namespace Definitions

/-
    A, B, Γ := int | ε | A → B | A & B | {l ∶ A}

    Supporting literal int, unit (top), arrow, intersection and record types.
    Note: Typing context Γ is unified with types, hence typing context Γ is simply a type.
-/
inductive Typ : Type  where
    | int     : Typ
    | top     : Typ
    | arr     : Typ → Typ → Typ
    | and     : Typ → Typ → Typ
    | rcd     : String → Typ → Typ

/-
    e := ? | i | ε | e₁ e₂ | e₁ ▷ e₂ | e₁ ,, e₂ | λA. e | e.i | ⟨v, λA. e⟩ | e.l

    Supporting environment query, int literal, unit (top), application, box construct,
    merge operator, lambda abstractions, indexed projection, closures, and label projection.
-/
inductive Exp : Type where
    | ctx     : Exp
    | lit     : Nat → Exp
    | unit    : Exp
    | app     : Exp → Exp → Exp
    | box     : Exp → Exp → Exp
    | mrg     : Exp → Exp → Exp
    | lam     : Typ → Exp → Exp
    | proj    : Exp → Nat → Exp
    | clos    : Exp → Typ → Exp → Exp
    | erec    : String → Exp → Exp
    | rproj   : Exp → String → Exp

/-
    v := i | ε | ⟨v, λA. e⟩
-/
inductive Value : Exp → Prop where
    | vint      : ∀ n, Value (Exp.lit n)
    | vunit     : Value Exp.unit
    | vclos     : ∀ v A e,
        Value v → Value (Exp.clos v A e)
    | vrcd      : ∀ l v,
        Value v → Value (Exp.erec l v)
    | vmrg      : ∀ v1 v2,
        Value v1 → Value v2 → Value (Exp.mrg v1 v2)

inductive Lookup : Typ → Nat → Typ → Prop where
    | lzero : ∀ A B,  Lookup (Typ.and A B) 0 B
    | lsucc : ∀ A B n C,
        Lookup A n C → Lookup (Typ.and A B) (n + 1) C

inductive Lin : String → Typ → Prop where
    | lin_rcd   : ∀ A l, Lin l (Typ.rcd l A)
    | lin_andl  : ∀ A B l, Lin l A → Lin l (Typ.and A B)
    | lin_andr  : ∀ A B l,
        Lin l B → Lin l (Typ.and A B)

inductive RLookup : Typ → String → Typ → Prop where
    | rlzero : ∀ l B, RLookup (Typ.rcd l B) l B
    | landl : ∀ A B C l,
        RLookup A l C →
        ¬ Lin l B →
        RLookup (Typ.and A B) l C
    | landr : ∀ A B C l,
        RLookup B l C →
        ¬ Lin l A →
        RLookup (Typ.and A B) l C

inductive HasType : Typ → Exp → Typ → Prop where
    | tctx      : ∀ E, HasType E Exp.ctx E
    | tint      : ∀ E i, HasType E (Exp.lit i) Typ.int
    | tunit     : ∀ E, HasType E Exp.unit Typ.top
    | tapp      : ∀ E A B e1 e2,
        HasType E e1 (Typ.arr A B)  →
        HasType E e2 A              →
        HasType E (Exp.app e1 e2) B
    | tbox      : ∀ E A E1 e1 e2,
        HasType E e1 E1 →
        HasType E1 e2 A →
        HasType E (Exp.box e1 e2) A
    | tmrg      : ∀ E e1 e2 A B,
        HasType E e1 A              →
        HasType (Typ.and E A) e2 B  →
        HasType E (Exp.mrg e1 e2) (Typ.and A B)
    | tlam      : ∀ E A e B,
        HasType (Typ.and E A) e B →
        HasType E (Exp.lam A e) (Typ.arr A B)
    | tproj     : ∀ E A e B n,
        HasType E e A   →
        Lookup A n B    →
        HasType E (Exp.proj e n) B
    | tclos     : ∀ E E1 A e ev B,
        Value ev                    →
        HasType Typ.top ev E1       →
        HasType (Typ.and E1 A) e B  →
        HasType E (Exp.clos ev A e) (Typ.arr A B)
    | trcd      : ∀ E e A l,
        HasType E e A  →
        HasType E (Exp.erec l e) (Typ.rcd l A)
    | trproj    : ∀ E e B l A,
        HasType E e B →
        RLookup B l A →
        HasType E (Exp.rproj e l) A

inductive LookupV : Exp → Nat → Exp → Prop where
    | lvzero : ∀ v1 v2,
        LookupV (Exp.mrg v1 v2) 0 v2
    | lvsucc : ∀ v1 v2 n v3,
        LookupV v1 n v3 →
        LookupV (Exp.mrg v1 v2) (n + 1) v3

inductive RLookupV : Exp → String → Exp → Prop where
    | rvlzero   : ∀ l e,
        RLookupV (Exp.erec l e) l e
    | vlandl    : ∀ e1 e2 e l,
        RLookupV e1 l e →
        RLookupV (Exp.mrg e1 e2) l e
    | vlandr    : ∀ e1 e2 e l,
        RLookupV e2 l e →
        RLookupV (Exp.mrg e1 e2) l e

inductive Step : Exp → Exp → Exp → Prop where
    | sctx : ∀ v,
        Value v             →
        Step v Exp.ctx v
    | sblapp : ∀ v e1 e2 e1',
        Value v             →
        Step v e1 e1'       →
        Step v (Exp.app e1 e2) (Exp.app e1' e2)
    | sblbox : ∀ v e1 e2 e1',
        Value v             →
        Step v e1 e1'       →
        Step v (Exp.box e1 e2) (Exp.box e1' e2)
    | sblmrg : ∀ v e1 e2 e1',
        Value v             →
        Step v e1 e1'       →
        Step v (Exp.mrg e1 e2) (Exp.mrg e1' e2)
    | sbapp : ∀ v v1 e2 e2',
        Value v             →
        Value v1            →
        Step v e2 e2'       →
        Step v (Exp.app v1 e2) (Exp.app v1 e2')
    | sbbox : ∀ v v1 e2 e2',
        Value v             →
        Value v1            →
        Step v1 e2 e2'      →
        Step v (Exp.box v1 e2) (Exp.box v1 e2')
    | sbmrg : ∀ v v1 e' e,
        Value v             →
        Value v1            →
        Step (Exp.mrg v v1) e e'    →
        Step v (Exp.mrg v1 e) (Exp.mrg v1 e')
    | sclos : ∀ v A e,
        Value v     →
        Step v (Exp.lam A e) (Exp.clos v A e)
    | sbetalam : ∀ v v1 v2 A e,
        Value v     →
        Value v1    →
        Value v2    →
        Step v (Exp.app (Exp.clos v2 A e) v1) (Exp.box (Exp.mrg v2 v1) e)
    | sboxv : ∀ v v1 v2,
        Value v     →
        Value v1    →
        Value v2    →
        Step v (Exp.box v1 v2) v2
    | sproj : ∀ v e1 e2 n,
        Value v         →
        Step v e1 e2    →
        Step v (Exp.proj e1 n) (Exp.proj e2 n)
    | sprojv : ∀ v n v1 v2,
        Value v         →
        Value v1        →
        LookupV v1 n v2 →
        Step v (Exp.proj v1 n) v2
    | srec : ∀ v e1 e2 l,
        Value v         →
        Step v e1 e2    →
        Step v (Exp.erec l e1) (Exp.erec l e2)
    | srproj : ∀ v e1 e2 l,
        Value v         →
        Step v e1 e2    →
        Step v (Exp.rproj e1 l) (Exp.rproj e2 l)
    | srprojv : ∀ v l v1 v2,
        Value v             →
        Value v1            →
        RLookupV v1 l v2    →
        Step v (Exp.rproj v1 l) v2

end Definitions
