import Init.Prelude
import Stlc.Prelude

inductive Ty : Type where
  | Fn : Ty → Ty → Ty
  | Nat : Ty

variable {ty : Ty}

infixr:0 " ⟶ " => Ty.Fn

abbrev interp : Ty → Type := fun
 | .Nat => Nat
 | .Fn l r => interp l → interp r

notation "⟦" t "⟧" => interp t

abbrev Context : Type := List Ty


namespace Context

@[simp]
def cons (ty : Ty) (ctx : Context) : Context := List.cons ty ctx

infixr:67 " ▹ " => cons

@[simp]
def get (ctx : Context) (ix : Fin ctx.length) : Ty :=
  let ⟨m, p⟩ := ix
  match m, ctx with
  | .zero, .cons x _ => x
  | .succ k, .cons _ xs => get xs ⟨k, by simp at p; omega⟩

def get_congr {ctx ctx' : Context} (eq : ctx = ctx') (ix : Fin ctx.length) :
  ctx.get ix = ctx'.get ⟨ix.val, by cases eq; exact ix.isLt⟩ := sorry

def get_concat_l
  (Δ Γ : Context)
  {ix : Nat}
  (p : ix < Δ.length)
  : (Δ ++ Γ).get ⟨ix, by simp; omega⟩ = Δ.get ⟨ix, p⟩ :=
  by
  induction Δ generalizing ix
  case nil => contradiction
  case cons ih =>
   simp
   cases ix
   case zero => simp
   case succ i => apply ih

def get_concat_r
  (ix : Nat)
  (Δ Γ : Context)
  (ty : Ty)
  (p : Δ.length <= ix)
  (u : ix < Δ.length + Γ.length)
  : (Δ ++ (ty ▹ Γ)).get ⟨ix.succ, by simp; omega⟩ = (Δ ++ Γ).get ⟨ix, by simp; omega⟩ :=
  by
  induction Δ generalizing ix
  case nil => rfl
  case cons n' t Δ' ih =>
    let .succ ix' := ix
    simp at u
    simp at p
    apply ih ix' (by assumption) (by omega)

def get_concat_r2
  (ix : Nat)
  (Δ Ε Γ : Context)
  (p : Δ.length <= ix)
  (u : ix < Γ.length + Δ.length)
  : (Δ ++ Ε ++ Γ).get ⟨ix + Ε.length, by simp; omega⟩ = (Δ ++ Γ).get ⟨ix, by simp; omega⟩ :=
  by sorry

def get_concat_m
  (Δ Γ : Context)
  (ty : Ty)
  : (Δ ++ (ty ▹ Γ)).get ⟨Δ.length, by simp⟩ = ty :=
  by
  induction Δ
  case nil => rfl
  case cons Δ' ih => apply ih

end Context

structure Var (Γ : Context) (ty : Ty) : Type where
  ix : Fin Γ.length
  tyProof : Γ.get ix = ty := by rfl

inductive Expr : (Γ : Context) → Ty → Type where
  | lam
    {Γ : Context}
    {varTy : Ty}
    {bodyTy : Ty}
    (body : Expr (varTy ▹ Γ) bodyTy)
    : Expr Γ (varTy ⟶ bodyTy)
  | var
    {Γ : Context}
    {ty : Ty}
    (var : Var Γ ty)
    : Expr Γ ty
  | app
    {Γ : Context}
    {l r : Ty}
    (fn : Expr Γ (l ⟶ r))
    (arg : Expr Γ l)
    : Expr Γ r
  | zero
    {Γ : Context}
    : Expr Γ (.Nat)
  | suc
    {Γ : Context}
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
    {Γ : Context}
    (env : Env Γ)
    {varTy retTy : Ty}
    (body : Expr (varTy ▹ Γ) retTy)
    : Val (varTy ⟶ retTy)

inductive Env : (Γ : Context) → Type where
  | nil : Env .nil
  | cons
    {Γ : Context}
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

def Expr.weaken
  {ty : Ty}
  {Δ Ε Γ : Context}
  (e : Expr (Δ ++ Γ) ty)
  : Expr (Δ ++ Ε ++ Γ) ty := match e with
  | .zero => .zero
  | .suc n => .suc n.weaken
  | .app l r => .app l.weaken r.weaken
  | .lam (varTy := vt) (bodyTy := bodyTy) b => .lam (b.weaken (Δ := vt ▹ Δ) (Γ := Γ))
  | .var ⟨⟨k, u⟩, p⟩ => by
        apply Expr.var
        by_cases cmp : k < Δ.length
        case pos =>
          refine ⟨⟨k, by simp; omega⟩, ?_⟩
          rw [Context.get_congr (List.append_assoc Δ Ε Γ) ⟨k, by simp; omega⟩]
          rw [Context.get_concat_l Δ (Ε ++ Γ) (by simp; omega)]
          rw [Context.get_concat_l (p := cmp )] at p
          assumption
        case neg =>
          have cmp : Δ.length <= k := by omega
          simp at u
          refine ⟨⟨k + Ε.length, by simp; omega⟩, ?_⟩
          rw [Context.get_concat_r2 k Δ Ε Γ]
          assumption
          assumption
          omega

def Expr.substH
  {l r : Ty}
  {Δ Γ : Context}
  (fn : Expr (Δ ++ (l ▹ Γ)) r)
  (arg : Expr Γ l)
  : Expr (Δ ++ Γ) r := match fn with
  | .zero => .zero
  | .suc n => n.substH arg
  | .app f x => .app (f.substH arg) (x.substH arg)
  | .lam (varTy := varTy) (bodyTy := bodyTy) body => .lam (body.substH (Δ := varTy ▹ Δ) arg)
  | .var var@⟨⟨k, u⟩, p⟩ => by
    by_cases h : k < Δ.length
    case pos =>
      have h1 := Context.get_concat_l Δ Γ h
      have h2 := Context.get_concat_l Δ (l ▹ Γ) h
      refine (.var ⟨⟨k , by simp; omega⟩ , ?_⟩)
      rw [h1, ←h2, p]
    case neg =>
      by_cases h2 : k = Δ.length
      case pos =>
        subst h2
        have h1 := Context.get_concat_m Δ Γ l
        rw [p] at h1
        rw [h1]
        exact (arg.weaken (Δ := .nil))
      case neg =>
        have h1 : k > Δ.length := by omega
        let .succ ks := k
        simp at u
        refine (.var ⟨⟨ks, by simp; omega⟩, ?_⟩)
        rw [← Context.get_concat_r ks Δ Γ l (by omega) (by omega)]
        assumption

def Expr.subst
  {l r : Ty}
  {Γ : Context}
  (fn : Expr (l ▹ Γ) r)
  (arg : Expr Γ l)
  : Expr Γ r := Expr.substH (Δ := .nil) fn arg

inductive Equiv (Γ : Context) : {ty : Ty} → (e1 e2 : Expr Γ ty) → Type where
  | refl : {e : Expr Γ ty} → Equiv Γ e e
  | βreduction (body : Expr (α ▹ Γ) γ) (arg : Expr Γ α)
          : Equiv Γ (.app (.lam body) arg) (body.subst arg)

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
  termination_by 0
  decreasing_by repeat sorry

def evalTop
  {ty : Ty}
  (expr : Expr .nil ty)
  : Val ty := eval .nil expr
