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

inductive Context : Nat → Type where
  | nil : Context 0
  | cons : {n : Nat} → Ty → Context n → Context (n + 1)

namespace Context

infixr:67 " ▹ " => cons

@[simp]
def concat (Δ : Context n) (Γ : Context m) : Context (m + n) :=
  match Δ with
  | .nil => by simp; exact Γ
  | .cons (n := k) ty as => .cons ty (concat as Γ)

@[simp]
def get (ctx : Context n) (ix : Fin n) : Ty :=
  let ⟨m, p⟩ := ix
  match m, ctx with
  | .zero, .cons x _ => x
  | .succ k, .cons _ xs => get xs ⟨k, by omega⟩

def get_concat_l
  (Δ : Context n)
  (Γ : Context m)
  (ix : Nat)
  (p : ix < n)
  : (Δ.concat Γ).get ⟨ix, by omega⟩ = Δ.get ⟨ix, p⟩ :=
  by
  induction Δ generalizing ix
  case nil => contradiction
  case cons k ty Δ' ih =>
   simp
   cases ix
   case zero => simp
   case succ i => apply ih

def get_concat_r
  (ix : Nat)
  (Δ : Context n)
  (ty : Ty)
  (Γ : Context m)
  (p : n <= ix)
  (u : ix < m + n)
  : (Δ.concat (ty ▹ Γ)).get ⟨ix.succ, by omega⟩ = (Δ.concat Γ).get ⟨ix, by omega⟩ :=
  by
  induction Δ generalizing ix
  case nil => rfl
  case cons n' t Δ' ih =>
    let .succ ix' := ix
    apply ih ix' (by omega) (by omega)

def help
  {n m : Nat}
  (Δ : Context n)
  (eq : n = m)
  : Context m := sorry

def concat_assoc
  {Δ : Context n}
  {Ε : Context l}
  {Γ : Context m}
  : Δ.concat (Ε.concat Γ) = help ((Δ.concat Ε).concat Γ)
    (by omega : m + (l + n) = m + l + n)
  := by
  induction Δ
  simp
  case cons t Δ' ih =>
  simp
  rw [ih]


def get_concat_r2
  (ix : Nat)
  (Δ : Context n)
  (Ε : Context l)
  (Γ : Context m)
  (p : n <= ix)
  (u : ix < m + n)
  : (Δ.concat (Ε.concat Γ)).get ⟨ix + l, by omega⟩ = (Δ.concat Γ).get ⟨ix, by omega⟩ :=
  by
  induction Δ generalizing ix
  case nil => simp
              sorry
  case cons n' t Δ' ih =>
    let .succ ix' := ix
    sorry

def get_concat_m
  (Δ : Context n)
  (ty : Ty)
  (Γ : Context m)
  : (Δ.concat (ty ▹ Γ)).get ⟨n, by omega⟩ = ty :=
  by
  induction Δ
  case nil => rfl
  case cons Δ' ih => apply ih

def toList : Context n → List Ty := fun
  | nil => []
  | cons ty t => ty :: toList t

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
  {Δ : Context n}
  {Ε : Context l}
  {Γ : Context m}
  (e : Expr (Δ.concat Γ) ty)
  : Expr (Δ.concat (Ε.concat Γ)) ty := match e with
  | .zero => .zero
  | .suc n => .suc n.weaken
  | .app l r => .app l.weaken r.weaken
  | .lam (varTy := vt) (bodyTy := bodyTy) b => .lam (b.weaken (Δ := vt ▹ Δ) (Γ := Γ))
  | .var ⟨⟨k, u⟩, p⟩ => by
        apply Expr.var
        by_cases cmp : k < n
        case pos =>
          refine ⟨⟨k, by omega⟩, ?_⟩
          rw [Context.get_concat_l (p := cmp)]
          rw [Context.get_concat_l (p := cmp )] at p
          assumption
        case neg =>
          have cmp : n <= k := by omega
          refine ⟨⟨k + l, by omega⟩, ?_⟩
          rw [Context.get_concat_r2]
          assumption
          assumption

def Expr.substH
  {l r : Ty}
  {Δ : Context m}
  {Γ : Context n}
  (fn : Expr (Δ.concat (l ▹ Γ)) r)
  (arg : Expr Γ l)
  : Expr (Δ.concat Γ) r := match fn with
  | .zero => .zero
  | .suc n => n.substH arg
  | .app f x => .app (f.substH arg) (x.substH arg)
  | .lam (varTy := varTy) (bodyTy := bodyTy) body => .lam (body.substH (Δ := varTy ▹ Δ) arg)
  | .var var@⟨⟨k, u⟩, p⟩ => by
    by_cases h : k < m
    case pos =>
      have h1 := Context.get_concat_l Δ Γ k h
      have h2 := Context.get_concat_l Δ (l ▹ Γ) k h
      refine (.var ⟨⟨k , by omega⟩ , ?_⟩)
      simpa [h1, h2] using p
    case neg =>
      by_cases h2 : k = m
      case pos =>
        subst h2
        have h1 := Context.get_concat_m Δ l Γ
        rw [p] at h1
        rw [h1]
        exact (arg.weaken (Δ := .nil))
      case neg =>
        have h1 : k > m := by omega
        let .succ ks := k
        refine (.var ⟨⟨ks, by omega⟩, ?_⟩)
        simpa [Context.get_concat_r ks Δ l Γ (by omega) (by omega)] using p

def Expr.subst
  {l r : Ty}
  {Γ : Context n}
  (fn : Expr (l ▹ Γ) r)
  (arg : Expr Γ l)
  : Expr Γ r := Expr.substH (Δ := .nil) fn arg

inductive Equiv (Γ : Context n) : {ty : Ty} → (e1 e2 : Expr Γ ty) → Type where
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
