import Cat.STLCI.Utils

namespace STLC

inductive Ty : Type where
  | arr   : Ty → Ty → Ty
  | unit  : Ty
  | prod  : Ty → Ty → Ty

declare_syntax_cat stlc_ty

syntax num : stlc_ty
syntax ident : stlc_ty
syntax "!(" term ")" : stlc_ty
syntax "(" stlc_ty ")" : stlc_ty
syntax stlc_ty "→" stlc_ty : stlc_ty
syntax stlc_ty "×" stlc_ty : stlc_ty
syntax stlc_ty "+" stlc_ty : stlc_ty

syntax "[ty|" stlc_ty "]" : term

macro_rules
  | `([ty| 1 ]) => `(Ty.unit)
  | `([ty| $id:ident ]) => `($id)
  | `([ty| !($t) ]) => `($t)
  | `([ty| ($v) ]) => `([ty| $v])
  | `([ty| $a → $b ]) => `(Ty.arr [ty| $a] [ty| $b])
  | `([ty| $a × $b ]) => `(Ty.prod [ty| $a] [ty| $b])

open Lean in
def Ty.uex_inner : Syntax.Term → PrettyPrinter.UnexpandM (TSyntax `stlc_ty)
  | `([ty|$b]) => `(stlc_ty|$b)
  | `($t) => `(stlc_ty|!($t))

@[app_unexpander Ty.unit]
def Ty.unit.uex : Lean.PrettyPrinter.Unexpander
  | `($_p) => `([ty| 1])

@[app_unexpander Ty.arr]
def Ty.arr.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stlc_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_ty)
      | `(stlc_ty|$c → $d) => `(stlc_ty|($c → $d))
      | `(stlc_ty|$c + $d) => `(stlc_ty|($c + $d))
      | v => `(stlc_ty|$v)
    let a ← perenify a
    `([ty| $a → $b])
  | _ => throw ()

@[app_unexpander Ty.prod]
def Ty.prod.uex : Lean.PrettyPrinter.Unexpander
  | `($_p $a $b) => do
    let a ← uex_inner a
    let b ← uex_inner b
    let perenify : Lean.TSyntax `stlc_ty → Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `stlc_ty)
      | `(stlc_ty|$c → $d) => `(stlc_ty|($c → $d))
      | `(stlc_ty|$c + $d) => `(stlc_ty|($c + $d))
      | v => `(stlc_ty|$v)
    let a ← perenify a
    let b ← perenify b
    `([ty| $a × $b])
  | _ => throw ()


inductive ITerm : List Ty → Ty → Type
  | var {ctx ty} : ctx.MemT ty → ITerm ctx ty

  | lam {dom ctx ran} : ITerm (dom :: ctx) ran → ITerm ctx (.arr dom ran)
  | app {ctx dom ran} : ITerm ctx (.arr dom ran) → ITerm ctx dom → ITerm ctx ran

  | fst {Γ A B} : ITerm Γ (.prod A B) → ITerm Γ A
  | snd {Γ A B} : ITerm Γ (.prod A B) → ITerm Γ B
  | mk  {Γ A B} : ITerm Γ A → ITerm Γ B → ITerm Γ (.prod A B)

  | unit {Γ} : ITerm Γ .unit

namespace ITerm

def gshift {t Γ Γ₁ Γ₂} : ITerm (Γ ++ Γ₁) t → ITerm (Γ ++ (Γ₂ ++ Γ₁)) t
  | .var h => .var h.sandwitch_shift

  | .app a b => .app a.gshift b.gshift
  | .lam (dom := dom) v => .lam (v.gshift (Γ := dom :: Γ))

  | .fst v => .fst v.gshift
  | .snd v => .snd v.gshift
  | .mk a b => .mk a.gshift b.gshift
  | .unit => .unit

def shift {t Γ₁} Γ₂ : ITerm Γ₁ t → ITerm (Γ₂ ++ Γ₁) t := gshift (Γ := [])

def parSubst {Γ' Γ t} (hList : HList (ITerm Γ') Γ) : ITerm Γ t → ITerm Γ' t
  | .var h => hList[h]

  | .app a b => .app (a.parSubst hList) (b.parSubst hList)
  | .lam (dom := dom) v => .lam
      <| v.parSubst
      <| .cons (.var .hd)
      <| hList.map
      <| shift [dom]

  | .fst v => .fst <| v.parSubst hList
  | .snd v => .snd <| v.parSubst hList
  | .mk a b => .mk (a.parSubst hList) (b.parSubst hList)

  | .unit => .unit

def parSubst.noopL : {Γ : _} → HList (ITerm Γ) Γ
  | [] => .nil
  | _ :: _ => .cons (.var .hd) <| noopL.map <| shift [_]

theorem parSubst.noopL_get {t}
    : {Γ : _}
    → (h : List.MemT t Γ)
    → (parSubst.noopL (Γ := Γ))[h] = var h 
  | _ :: _, .hd => rfl
  | _ :: _, .tl h => by 
    change HList.get h (HList.map _ noopL) = var h.tl
    rw [HList.get_map', ]
    rw [parSubst.noopL_get]
    cases h
    · simp only [shift, gshift, List.cons_append, List.nil_append, List.MemT.sandwitch_shift, var.injEq]
      rename_i as
      cases as <;> rfl
    · simp [shift, gshift, List.MemT.sandwitch_shift, List.MemT.shift]

theorem parSubst.noop {Γ t} : {e : ITerm Γ t} → e.parSubst parSubst.noopL = e
  | .var h => noopL_get h
  | .app _ _ | .unit | .mk _ _ | .fst _ | .snd _ => by
    dsimp [parSubst]
    repeat rw [parSubst.noop]
  | .lam b => by
    change ITerm.lam (parSubst noopL b) = b.lam
    rw [parSubst.noop]

theorem parSubst.closed {t} : {e : ITerm [] t} → e.parSubst .nil = e := parSubst.noop

