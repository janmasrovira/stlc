import Init.Prelude
import Stlc.Prelude

inductive Ty : Type where
  | Fn : Ty → Ty → Ty
  | Nat : Ty

variable (ty : Ty)

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

@[reducible]
def Expr.size (expr :  Expr Γ t) : Nat := match expr with
  | .zero => 1
  | .suc e => e.size.succ
  | .app l r => l.size + r.size |>.succ
  | .var _ => 1
  | .lam l => l.size.succ

mutual
def Val.size (val : Val t) : Nat := match val with
  | .nat _ => 1
  | .closure cenv cbody => cenv.size + cbody.size

def Env.size (env : Env Γ) : Nat := match env with
  | .nil => 0
  | .cons v e => v.size + e.size
end

def eval
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
  -- termination_by env.size + expr.size
  -- decreasing_by
  --   simp
  --   simp
  --   omega
  --   simp
  --   omega
  --   --- hard goal
  --   simp


-- H1: size arg' < arg
-- H2: size clEnv + size body < size env + size fn
-- -------
-- size arg' + size clEnv + size body < size env + size fn + size arg + 1
--
--
-- 1. simplify arg' arg by H1
-- 2. new goal: size clEnv + size body < size env + size fn + 1
-- 3. simplify using H2
-- 4. new goal: 0 < 1

def evalTop
  {ty : Ty}
  (expr : Expr .nil ty)
  : Val ty := eval .nil expr
