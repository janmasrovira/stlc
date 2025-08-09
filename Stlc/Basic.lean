import Init.Prelude
import Stlc.Prelude

inductive Ty : Type where
  | Fn : Ty → Ty → Ty
  | Nat : Ty

infixr:0 " ⟶ " => Ty.Fn

abbrev interp : Ty → Type := fun
 | .Nat => Nat
 | .Fn l r => interp l → interp r

notation "⟦" t "⟧" => interp t

inductive Context : Nat → Type where
  | nil : Context 0
  | cons : {n : Nat} → Ty → Context n → Context (n + 1)

namespace Context

def get (ctx : Context n) (ix : Fin n) : Ty :=
  let ⟨m, p⟩ := ix
  match ctx with
  | nil => by contradiction
  | cons x xs =>
     match m with
     | .zero => x
     | .succ k => get xs ⟨k, by omega⟩

def toList : Context n → List Ty := fun
  | nil => []
  | cons ty t => ty :: toList t

infixr:67 " ▹ " => cons

end Context

structure Var {n : Nat} (Γ : Context n) (ty : Ty) : Type where
  ix : Fin n
  tyProof : Γ.get ix = ty := by rfl

inductive Expr : {n : Nat} → (Γ : Context n) → Ty → Type where
  | lam
    {Γ : Context n}
    {varTy : Ty}
    {bodyTy : Ty}
    (body : Expr (varTy ▹ Γ) bodyTy)
    : Expr Γ (varTy ⟶ bodyTy)
  | var
    {Γ : Context n}
    {ty : Ty}
    (var : Var Γ ty)
    : Expr Γ ty
  | app
    {Γ : Context n}
    {l r : Ty}
    (fn : Expr Γ (l ⟶ r))
    (arg : Expr Γ l)
    : Expr Γ r
  | zero
    {Γ : Context n}
    : Expr Γ (.Nat)
  | suc
    {Γ : Context n}
    (num : Expr Γ .Nat)
    : Expr Γ .Nat
  -- | prec
  --   {Γ : Context n}
  --   {ty : Ty}
  --   (z : Expr Γ ty)
  --   (s : Expr Γ (.Nat ⟶ ty ⟶ ty))
  --   (m : Expr Γ .Nat)
  --   : Expr Γ ty

mutual

inductive Val : Ty → Type where
  | nat : Nat → Val .Nat
  | closure
    {Γ : Context n}
    (env : Env Γ)
    {varTy retTy : Ty}
    (body : Expr (varTy ▹ Γ) retTy)
    : Val (varTy ⟶ retTy)

inductive Env : (Γ : Context n) → Type where
  | nil : Env .nil
  | cons
    {Γ : Context n}
    {ty : Ty}
    (val : Val ty)
    (env : Env Γ)
    : Env (ty ▹ Γ)

end

def Val.interpNat : Val .Nat → Nat := fun
  | .nat n => n

def Env.get
  {ty : Ty}
  (env : Env Γ)
  (var : Var Γ ty)
  : Val ty :=
  let ⟨⟨ix, l⟩, p⟩ := var
  match Γ with
  | .nil => by contradiction
  | .cons t ctx =>
    match ix, env with
    | 0, (.cons v _) => p ▸ v
    | .succ m, (.cons _ env) => env.get ⟨⟨m, Nat.succ_lt_succ_iff.mp l⟩, by simpa using p⟩

def eval
  {n : Nat}
  {Γ : Context n}
  {ty : Ty}
  (env : Env Γ)
  (expr : Expr Γ ty)
  : Val ty :=
  match expr with
  | .zero => .nat 0
  | .suc e => let .nat m := eval env e
              .nat (m + 1)
  | .lam body => .closure env body
  | .var v => env.get v
  | .app (l := l) (r := r) (fn : Expr Γ (l ⟶ r)) arg =>
      let arg' := eval env arg
      let .closure clEnv body := eval env fn
      eval (.cons arg' clEnv) body

-- val < max expr env.succ
-- env ≤ expr
