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

inductive Val : Ty → Type where
  | nat : Nat → Val .Nat
  | closure {t1 t2 : Ty} : (f : ⟦ t1 ⟶ t2 ⟧) → Val (t1 ⟶ t2)

def Val.interp {ty : Ty} : Val ty → ⟦ ty ⟧ := fun
  | .nat n => n
  | .closure c => c

def reify {ty : Ty} : ⟦ ty ⟧ → Val ty :=
  match ty with
  | .Nat => .nat
  | .Fn _ _ => .closure

abbrev Env {n : Nat} (Γ : Context n) : Type := match Γ with
  | .nil => Unit
  | .cons ty ctx => Val ty × Env ctx

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
    | 0, (v, _) => p ▸ v
    | .succ m, (_, env) => env.get ⟨⟨m, Nat.succ_lt_succ_iff.mp l⟩, by simpa using p⟩

def eval {n : Nat} {Γ : Context n} {ty : Ty} (env : Env Γ) : Expr Γ ty → Val ty := fun
  | .zero => .nat 0
  | .suc e => let .nat m := eval env e
              .nat (m + 1)
  | @Expr.lam _ _ ty bodyTy body => .closure (fun x => (eval (Γ := ty ▹ Γ) ⟨reify x, env⟩ body).interp)
  | .var v => env.get v
  | .app fn x => (eval env fn).interp (eval env x).interp |> reify
  | .prec z i n =>
    let z' := eval env z |>.interp
    let n' := eval env n |>.interp
    let i' : Nat → ⟦ ty ⟧ → ⟦ ty ⟧ := eval env i |>.interp
    @Nat.rec (fun _ => ⟦ ty ⟧) z' i' n' |> reify
