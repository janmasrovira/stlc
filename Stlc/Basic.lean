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
    (varTy : Ty)
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
  | prec
    {Γ : Context n}
    {ty : Ty}
    (z : Expr Γ ty)
    (s : Expr Γ (.Nat ⟶ ty ⟶ ty))
    (m : Expr Γ .Nat)
    : Expr Γ ty

mutual

inductive Closure : (varTy : Ty) → (retTy : Ty) → Type where
  | mk
    {n : Nat}
    {Γ : Context n}
    (env : Env Γ)
    {varTy retTy : Ty}
    (body : Expr (varTy ▹ Γ) retTy)
    : Closure varTy retTy

inductive Val : Ty → Type where
  | nat : Nat → Val .Nat
  | closure
    {varTy : Ty}
    {retTy : Ty}
    (cl : Closure varTy retTy)
    : Val (varTy ⟶ retTy)

inductive Env : {n : Nat} → (Γ : Context n) → Type where
  | nil : Env .nil
  | cons
    {n : Nat}
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
  | @Expr.lam _ Γ ty bodyTy body => .closure ⟨env, body⟩
  | .var v => env.get v
  | .app fn x => evalApp env fn x
  | .prec z i n =>
    let z' : Val ty := eval env z
    let i' : Val (Ty.Nat ⟶ ty ⟶ ty) := eval env i
    let nat : Val Ty.Nat := eval env n
    let indCase (prevNum : Nat) (prevVal : Val ty) : Val ty :=
                evalVApp (evalVApp i' (.nat prevNum)) prevVal
    @Nat.rec (fun _ => Val ty) z' indCase nat.interpNat
  where
  evalApp
    {n : Nat}
    {Γ : Context n}
    {ty1 ty2 : Ty}
    (env : Env Γ)
    (fn : Expr Γ (ty1 ⟶ ty2))
    (arg : Expr Γ ty1)
    : Val ty2 := evalVApp (eval env fn) (eval env arg)

  evalVApp
    {ty1 ty2 : Ty}
    (fn : Val (ty1 ⟶ ty2))
    (arg : Val ty1)
    : Val ty2 :=
      let .closure c := fn
      let @Closure.mk _ _ clEnv _ _ body := c
      eval (.cons arg clEnv) body
