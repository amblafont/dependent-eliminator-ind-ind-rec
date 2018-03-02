
Set Implicit Arguments.

Axiom (K : forall A (x : A) (e : x =x), e = eq_refl).

Definition  tr : forall {A : Type}(B : A -> Type)
                   {a₀ : A}{a₁ : A}(a₂ : a₀ = a₁)
                   , B a₀ -> B a₁.
  induction 1.
  easy.
Defined.
Definition J : forall{A : Type} {a₀ : A} (P : forall (a₁ : A) , a₀ = a₁ -> Type) , P _ eq_refl ->
                forall {a₁}(p : a₀ = a₁) , P a₁ p.
  destruct p.
  assumption.
Defined.

Definition is_center (A : Type) (a : A) := forall ( a' : A),  a' = a.

Definition is_subCenter (A : Type) (P : A -> Type) (a : A) := forall a' ,  P a' -> a = a'.
