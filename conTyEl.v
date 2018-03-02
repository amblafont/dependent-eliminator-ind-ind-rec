
(*  Définition de l'éliminateur dépendant en coq [elimin_term] du HIIT suivant :

constructors
  Con  : U;
  Ty   : Con → U;
  nil  : Con;
  cons : (Γ : Con) → Ty Γ → Con;
  u    : (Γ : Con) → Ty Γ;
  π    : (Γ : Con)(A : Ty Γ) → Ty (cons Γ A) → Ty Γ;
 *)
(* Pour dependent destruction *)
Require Import Coq.Program.Equality.


Require Import DepInd.lib.

Set Implicit Arguments.

(* Syntaxe non typée *)

Inductive Con :=
  nil
| cons : Con -> Ty -> Con
with Ty :=
       unitt : Ty
     | prod : Ty -> Ty -> Ty .

Inductive Conᵂ : Con -> Type :=
  nilᵂ : Conᵂ nil
| consᵂ Γ (A : Ty) : Conᵂ Γ -> Tyᵂ Γ A ->
                     Conᵂ (cons Γ A)
with Tyᵂ : Con -> Ty -> Type :=
       unittᵂ Γ : Conᵂ Γ -> Tyᵂ Γ unitt
     | prodᵂ Γ A B : Tyᵂ Γ A -> Tyᵂ (cons Γ A) B ->
                     Tyᵂ Γ (prod A B)
                         .

Lemma Conᵂ_hp Γ (Γᵂ : Conᵂ Γ) : is_center Γᵂ
with Tyᵂ_hp Γ A (Aᵂ : Tyᵂ Γ A) : is_center Aᵂ.
  - destruct Γᵂ.
    + intro nil'.
      now  dependent destruction nil'.
    + rename t into Aᵂ.
      assert (IΓ := Conᵂ_hp _ Γᵂ).
      assert (IA := Tyᵂ_hp _ _ Aᵂ).
      clear Tyᵂ_hp Conᵂ_hp.
      intros Γ'.
      dependent destruction Γ'.
      f_equal.
      * apply  IΓ.
      * apply IA.
  - destruct Aᵂ.
    + rename c into Γᵂ.
      assert (IΓ := Conᵂ_hp _ Γᵂ).
      intro Γ'.
      dependent destruction Γ'.
      f_equal.        
      apply IΓ.
    + rename Aᵂ2 into Bᵂ.
      rename Aᵂ1 into Aᵂ.
      assert (hA := Tyᵂ_hp _ _ Aᵂ).
      assert (hB := Tyᵂ_hp _ _ Bᵂ).
      intro p'.
      dependent destruction p'.
      f_equal; apply Tyᵂ_hp.
Qed.


Local Notation U := Type.
Class methods :=
  { Conᴹ : forall (c : Con), Conᵂ c  -> Type ; 
    Tyᴹ : forall (c : Con) A (wc : Conᵂ c) (Aᵂ : Tyᵂ c A)
      (cᴹ : Conᴹ  wc) , U  ; 
  nilᴹ : Conᴹ  nilᵂ ;
  consᴹ : forall (Γ : Con  )(Γᵂ : Conᵂ Γ)
            (Γᴹ : Conᴹ  Γᵂ)
            (A : Ty )(Aᵂ : Tyᵂ Γ A) ,
      Tyᴹ   Aᵂ Γᴹ 
            -> Conᴹ 
                    (consᵂ  Γᵂ Aᵂ) ;
  uᴹ : forall (Γ : Con ) (Γᵂ : Conᵂ Γ) (Γᴹ : Conᴹ  Γᵂ) ,
         Tyᴹ  (unittᵂ  Γᵂ) Γᴹ ;
  πᴹ : forall (Γ : Con) (Γᵂ : Conᵂ Γ) (Γᴹ : Conᴹ  Γᵂ)
         (B : Ty) (Bᵂ : Tyᵂ Γ B)
         (Bᴹ : Tyᴹ  Bᵂ Γᴹ )
         (C : Ty) (Cᵂ : Tyᵂ (cons Γ B) C)
         (Cᴹ : Tyᴹ   Cᵂ
                   (consᴹ    Bᴹ) ),
      Tyᴹ   
          (prodᵂ  Bᵂ Cᵂ)
          Γᴹ  }.


Section meth.
 Context{d : methods}.

 (* eliminateur (déterminé à partir du programme Haskell d'Ambruse *)
Record elimin  :=
  {
    Conᴱ : forall c (x' : Conᵂ c) , Conᴹ  x';
                           
    Tyᴱ : forall Γ (Γᵂ : Conᵂ Γ)
            B (Bᵂ : Tyᵂ Γ B),
              Tyᴹ Γᵂ Bᵂ (Conᴱ  Γᵂ)
    ;
    nilᴱ : Conᴱ nilᵂ = nilᴹ ;

    consᴱ :
       forall Γ (Γᵂ : Conᵂ Γ)
           B (Bᵂ : Tyᵂ Γ B),
         Conᴱ  (consᵂ  Γᵂ Bᵂ) =
              consᴹ Γᵂ (Conᴱ  Γᵂ)  Bᵂ
              (Tyᴱ  Γᵂ  Bᵂ);
    uᴱ : forall Γ (Γᵂ : Conᵂ Γ) ,
           Tyᴱ  Γᵂ  (unittᵂ Γᵂ) = uᴹ  Γᵂ (Conᴱ Γᵂ);
    πᴱ :
      forall (Γ : Con)(Γᵂ : Conᵂ Γ)
               (A : Ty )(Aᵂ : Tyᵂ Γ A)
               (B : Ty )
               (Bᵂ : Tyᵂ (cons Γ A) B),
       Tyᴱ Γᵂ (prodᵂ  Aᵂ Bᵂ) = πᴹ Γᵂ (Conᴱ Γᵂ) Aᵂ (Tyᴱ Γᵂ Aᵂ) Bᵂ
                                  ((tr (fun uᴹ' =>
                                          forall (x' : Ty) (x'ᵂ : Tyᵂ (cons Γ A) x')  ,
                                            Tyᴹ (consᵂ Γᵂ Aᵂ) x'ᵂ uᴹ' ) (consᴱ Γᵂ Aᵂ) (Tyᴱ (consᵂ Γᵂ Aᵂ))) B Bᵂ)
  }.

 (* description de la relation fonctionnelle *)
Inductive Conᶠ  : forall Γ (Γᵂ : Conᵂ Γ), Conᴹ Γᵂ -> Type :=
  nilᶠ  :  Conᶠ   nilᵂ nilᴹ
| consᶠ : 
       forall Γ (Γᵂ : Conᵂ Γ) Γᴹ (* redondant avec Bᶠ *) (Γᶠ : Conᶠ _ Γᴹ)
           B (Bᵂ : Tyᵂ Γ B) (Bᴹ : Tyᴹ _ Bᵂ Γᴹ) (Bᶠ : Tyᶠ  _ _ _ Bᴹ),
         Conᶠ  _ (consᴹ Γᵂ Γᴹ  Bᵂ Bᴹ)
with Tyᶠ  : forall Γ (Γᵂ : Conᵂ Γ) B (Bᵂ : Tyᵂ Γ B)(Γᴱ : Conᴹ Γᵂ),  
    Tyᴹ Γᵂ Bᵂ Γᴱ -> Type :=
     | uᶠ Γ (Γᵂ : Conᵂ Γ) (Γᴹ : Conᴹ Γᵂ) (Γᶠ : Conᶠ  _ Γᴹ) :
         Tyᶠ  _ _ _ (uᴹ Γᵂ Γᴹ)
     | πᶠ   (Γ : Con)(Γᵂ : Conᵂ Γ)(Γᴹ : Conᴹ Γᵂ) (* redondant avec Aᶠ *) (* (Γᶠ : Conᶠ _ Γᴹ) *)
               (A : Ty )(Aᵂ : Tyᵂ Γ A)(Aᴹ : Tyᴹ _ Aᵂ Γᴹ) (Aᶠ : Tyᶠ  _ _ _ Aᴹ)
               (B : Ty ) (Bᵂ : Tyᵂ (cons Γ A) B)(Bᴹ : Tyᴹ _ Bᵂ (consᴹ Γᵂ Γᴹ Aᵂ Aᴹ))
               (Bᶠ : Tyᶠ  _ _ _ Bᴹ) :
         Tyᶠ  _ _ _ (πᴹ Γᵂ  Γᴹ Aᵂ Aᴹ Bᵂ Bᴹ)
         .


  (* invariants d'induction *)
 Record ConR  (Γ : Con) (Γᵂ : Conᵂ Γ) :=
  { ConR_carrier : Conᴹ Γᵂ;
    ConR_carrierᶠ : Conᶠ _ ConR_carrier }.

 Record TyR  (Γ : Con) (Γᵂ : Conᵂ Γ) A (Aᵂ : Tyᵂ Γ A) :=
   { TyR_ConR :> ConR Γᵂ;
     TyR_carrier : Tyᴹ _ Aᵂ (ConR_carrier TyR_ConR);
     TyR_carrierᶠ :  Tyᶠ _ _ _ TyR_carrier
     }.


Lemma Con_is_subCenter  Γ (Γᵂ : Conᵂ Γ) (Γᴹ : Conᴹ Γᵂ)
      (Γᶠ : Conᶠ Γᵂ Γᴹ)
           : is_subCenter ( Conᶠ Γᵂ) Γᴹ
with Ty_is_subCenter  Γ (Γᵂ : Conᵂ Γ) (Γᴹ : Conᴹ Γᵂ)
                (* (Γᶠ : Conᶠ _ Γᴹ) *)
               A (Aᵂ : Tyᵂ Γ A) (Aᴹ : Tyᴹ _ Aᵂ Γᴹ)
               (Aᶠ : Tyᶠ Γᵂ Aᵂ Γᴹ Aᴹ) 
     : is_subCenter ( Tyᶠ Γᵂ Aᵂ Γᴹ) Aᴹ.
Proof.
  - destruct Γᶠ.
    + intros nil' nil'ᶠ.
      dependent destruction nil'ᶠ.
      reflexivity.
    + assert(IB := Ty_is_subCenter Γ Γᵂ Γᴹ B Bᵂ Bᴹ Bᶠ).
      assert(IΓ := Con_is_subCenter Γ Γᵂ Γᴹ Γᶠ ).
      intros Γe' Γe'ᶠ.
      abstract(
      dependent destruction Γe'ᶠ;
      (* revert Bᶠ0. *)
      assert (eΓ := (IΓ _ Γe'ᶠ));
      destruct eΓ;
      f_equal;
      now apply IB).
  - destruct Aᶠ.
    + intros u' u'ᶠ.
      clear -u'ᶠ.
      dependent destruction u'ᶠ.
      reflexivity.
    + 
      rename Aᶠ2 into Bᶠ.
      rename Aᶠ1 into Aᶠ.
      assert (IA := Ty_is_subCenter Γ Γᵂ Γᴹ A Aᵂ Aᴹ Aᶠ).
      assert (IB := Ty_is_subCenter _ _  _  _ _  _  Bᶠ).
      intros p' p'ᶠ.
      abstract(
      dependent destruction p'ᶠ;
      assert (eA : Aᴹ = Aᴹ0)by ( now apply IA);
      destruct eA;
      f_equal;
      now apply IB).
Qed.

(* uip is used by dependent destruction *)
Print Assumptions Ty_is_subCenter.

 Fixpoint Ty_Conᶠ  Γ (Γᵂ : Conᵂ Γ) (Γᴹ : Conᴹ Γᵂ)
               A (Aᵂ : Tyᵂ Γ A) (Aᴹ : Tyᴹ _ Aᵂ Γᴹ)
               (Aᶠ : Tyᶠ Γᵂ Aᵂ Γᴹ Aᴹ)  : Conᶠ Γᵂ Γᴹ.
 Proof.
   - destruct Aᶠ.
     + assumption.
     + eapply Ty_Conᶠ.
       eassumption.
 Defined.


 (* On habite par récurrence l'éliminateur *)
Fixpoint build_ConR (Γ : Con) (Γᵂ : Conᵂ Γ) {struct Γᵂ} : ConR Γᵂ 
with build_TyR (Γ : Con) (Γᵂ : Conᵂ Γ) (A : Ty) (Aᵂ : Tyᵂ Γ A) {struct Aᵂ} : TyR  Γᵂ Aᵂ.
- destruct Γᵂ.
  + econstructor.
    constructor.
  + assert (h := build_TyR _ Γᵂ _ t).
    econstructor.
    assert (hA := TyR_carrierᶠ (build_TyR _ Γᵂ _ t)).
    constructor.
    * eapply Ty_Conᶠ; exact hA.
    * exact hA.
- destruct Aᵂ.
  + assert (IΓ := build_ConR _ c).
    assert (h : Γᵂ = c) by apply Conᵂ_hp.
    subst.
    econstructor.
    constructor.
    apply ConR_carrierᶠ.
    Unshelve.
    assumption.
  + rename Aᵂ2 into Bᵂ.
    rename Aᵂ1 into Aᵂ.
    assert (IA := build_TyR Γ Γᵂ A Aᵂ).
    assert (IB := build_TyR _ (consᵂ Γᵂ Aᵂ) B Bᵂ).
    assert (h1 : (ConR_carrier IB) =  consᴹ Γᵂ (ConR_carrier IA) Aᵂ (TyR_carrier IA) ).
    {
      apply Con_is_subCenter.
      - apply ConR_carrierᶠ.
      - constructor.
        * eapply Ty_Conᶠ; apply TyR_carrierᶠ.
        * apply TyR_carrierᶠ.
    }
    econstructor.
    constructor.
    *  unshelve apply TyR_carrierᶠ.
       assumption.
    * assert (Bᶠ := TyR_carrierᶠ IB).
      assert (Bᶠ' : Tyᶠ (consᵂ Γᵂ Aᵂ) Bᵂ (consᴹ Γᵂ (ConR_carrier IA) Aᵂ (TyR_carrier IA))
                        (tr (Tyᴹ _ _)  h1 (TyR_carrier IB))
             ).
      {
        now destruct h1.
      }
      exact Bᶠ'.
Defined.
    
Lemma build_TyR_ConR (Γ : Con) (Γᵂ : Conᵂ Γ)  (A : Ty) (Aᵂ : Tyᵂ Γ A) :
  ConR_carrier (build_TyR  Γᵂ Aᵂ) = ConR_carrier (build_ConR Γᵂ) .
Proof.
  apply Con_is_subCenter; apply ConR_carrierᶠ.
Defined.


Definition elimin_term : elimin.
  unshelve refine(
  {| Conᴱ := fun Γ Γᵂ => ConR_carrier ( build_ConR Γᵂ);
     Tyᴱ := fun  (Γ : Con) (Γᵂ : Conᵂ Γ) (A : Ty) (Aᵂ : Tyᵂ Γ A) => tr (Tyᴹ _ _) (build_TyR_ConR Γᵂ Aᵂ) 
             (TyR_carrier (@build_TyR Γ Γᵂ A Aᵂ));

  |}).
  - intros.
    apply Con_is_subCenter.
    + apply ConR_carrierᶠ.
    + set (e := build_TyR_ConR _ _).
      set (T := build_TyR _ _) in *.
      assert (h := TyR_carrierᶠ T).
      constructor. 
      * apply ConR_carrierᶠ.
      * now destruct e .
  - reflexivity.
  - intros ??.
    apply Ty_is_subCenter.
    + 
      set (e := build_TyR_ConR _ _).
      set (unitRR := build_TyR _ _) in *.
      assert (h := TyR_carrierᶠ unitRR).
      now destruct e .
    + constructor.
      apply ConR_carrierᶠ.
  - intros.
    apply Ty_is_subCenter.
    + set (e := build_TyR_ConR _ _).
      set (T := build_TyR _ _) in *.
      assert (h := TyR_carrierᶠ T).
      now destruct e  .
    + constructor.
      * set (e := build_TyR_ConR _ _).
        set (T := build_TyR _ _) in *.
        assert (h := TyR_carrierᶠ T).
        now destruct e    .
      * cbn.
        set (e := build_TyR_ConR _ _).
        set (TA := build_TyR _ _) in *.
        (* revert h. *)
        set (e' := Con_is_subCenter _ _).
        generalize e'; clear e'.
        destruct e .
        cbn .
        intro e'.
        rewrite (K e').
        cbn.
        clear e'.

        fold TA.
        set (TB := build_TyR _ _) .
        set (e := build_TyR_ConR _ _).
        fold TB in  e.
        set (eΓB :=  e:  (ConR_carrier TB) = (consᴹ Γᵂ (ConR_carrier TA) Aᵂ (TyR_carrier TA)) ).
        generalize (TyR_carrierᶠ TB).
        case eΓB.
        easy.
Defined.

Print Assumptions elimin_term.

End meth.



