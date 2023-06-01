Require Import Undecidability.FOL.FullSyntax.
Require Export Undecidability.FOL.Syntax.Theories.
Require Import Undecidability.FOL.Syntax.BinSig.
Require Import Undecidability.FOL.ModelTheory.SearchNat.
Require Import Undecidability.FOL.ModelTheory.FullModelNotation.


Section DC.

    Variable A: Type.
    Variable a: A.
    Variable R: A -> A -> Prop.

    Definition surjective {M N} (f: M -> N) :=
        forall n: N, exists m: M, f m = n.

    Definition a_coutable_model M :=
        exists f: nat -> M, surjective f.

    Definition LS_countable :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), a_coutable_model N /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Instance interp__A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun P v => R (hd v) (last v)
    }.

    Instance Model__A: model :=
    {
        domain := A;
        interp' := interp__A
    }.

    Definition total_form :=
        ∀ (∃ (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _))))).
    Definition forfor_form :=
        (atom _ _ _ _ tt (cons _ ($1) _ (cons _ ($0) _ (nil _)))).

    Lemma total_sat:
        forall h, (forall x, exists y, R x y) -> Model__A ⊨[h] total_form.
    Proof.
        cbn; intros.
        destruct (H d) as [e P].
        now exists e.
    Qed.

    Definition p {N} (α β: N): env N :=
        fun n => match n with
            | 0 => β
            | _ => α end.

    Lemma forfor_sat {N} (h: N -> A) (α β: N):
        R (h α) (h β) <-> Model__A ⊨[(p α β) >> h] forfor_form.
    Proof.
        unfold ">>"; now cbn.
    Qed.

    Lemma exists_next:
    forall B (R': B -> B -> Prop), a_coutable_model B ->
        (forall x, exists y, R' x y) -> exists f: nat -> B,
            forall b, exists n, R' b (f n).
    Proof.
        intros B R' [f sur] total.
        exists f. intro b.
        destruct (total b) as [c Rbc], (sur c) as [m p].
        exists m. now rewrite p.
    Qed.    

    Section dec__R_full.

    Hypothesis dec__R: forall x y, dec (R x y).

    Lemma LS_imples_DC: LS_countable -> @DC_on _ R.
    Proof using dec__R a.
        intros LS total.
        destruct (LS _ _ Model__A a) as [N [[f sur] [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        unfold elementary_homomorphism in ele_el__h.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        assert (forall x, decidable (fun y => R' x y)) as dec__R'.
        intros x y. destruct (dec__R (h x) (h y)); firstorder.
        destruct (@DC_ω _ _ f sur dec__R' P1 n) as [g [case0 Choice]].
        exists (g >> h); unfold ">>". 
        intro n'; now rewrite <- (P2 (g n') (g (S n'))).
    Qed.

    End dec__R_full.

    Section DC_pred_full.



    Definition PDC:= 
        (forall x, exists y, R x y) -> forall w,
            exists P: nat -> A -> Prop, (forall x, exists! y, P x y) /\ P 0 w /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y. 

    Definition bijective_comp {X Y} :=
        exists f g, (forall x: X, g (f x) = x) /\ forall y: Y, f (g y) = y.

    Definition LS_countable_comp :=
        forall (Σf : funcs_signature) (Σp : preds_signature) (M: model), forall m,
            exists (N: model), @bijective_comp N nat /\ (exists h: N -> M, elementary_homomorphism h /\ exists n: N, h n = m).

    Definition WDC_on B (R: B -> B -> Prop) :=
        (forall n, exists y, R n y) -> forall w, exists F : nat -> nat -> B, 
            (forall n, F 0 n  = w) /\ forall n a, exists b, R(F n a) (F (S n) b).

    Lemma LS_imples_WDC: LS_countable_comp -> (@WDC_on A R).
    Proof.
        intros LS total w.
        destruct (LS _ _ Model__A w) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        exists (fun a b => match a, b with | O, b => w | S n, b => h (g b) end); split; [easy|].
        intros [|x] y.
        + rewrite <- Eqan.  
          destruct (P1 n) as [w' Hw'].
          rewrite P2 in Hw'.
          exists (f w'). now rewrite bij_l.
        + destruct (P1 (g y)) as [w' Hw'].
          rewrite P2 in Hw'.
          exists (f w'). now rewrite bij_l.
    Qed.

    Hypothesis definiteness__R: forall x y,  (R x y) \/ ~ (R x y).

    (* Definition OmniscientDependentChoiceP_on {A} (R: A -> A -> Prop) :=
        forall w,
        exists P : nat -> A -> Prop,
            (forall x, exists y, R x y) -> forall n : nat, function_rel P /\ P 0 w /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y.   

    Hypothesis IP_pred':
        forall (A' : Prop) X (P : (nat -> X -> Prop) -> Prop),
            (A' -> { R | P R }) -> { R | A' -> P R }.

    Lemma LS_imples_DC_pred': LS_countable_comp -> (@OmniscientDependentChoiceP_on _ R).
    Proof.
        intros LS m.
        destruct (LS _ _ Model__A m) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        destruct(@IP_pred' (forall x, exists y, R x y) A
        (fun P => forall n : nat, function_rel P /\ P 0 m /\ forall n, exists x y,  P n x /\ P (S n) y /\ R x y)).
        intro total.
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (Σ R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct X as [R' [P1 P2]].
        assert (forall x : N, logical_decidable (R' x)).
        intros x y. destruct (logical_dec__R (h x) (h y)); now try (left + right; rewrite P2).
        edestruct (@DC_pred_ω N R' _ _ bij_r bij_l H P1 n) as [P [case0 Choice]].
        unshelve eexists.
        exact (fun n' a' => exists n, h n = a' /\ P n' n); cbn.
        split.
        (* Proof of functional property*)
        - intro x; destruct (case0 x) as [n' [P1' P2']].
            exists (h n'); constructor.
            now exists n'.    
            intros a' [nn [Pa' Pa'']]. now rewrite (P2' nn).
        (* Proof of spec of the dependent choice predicate *)
        - split.
            + now exists n.
            + intro nA.
            destruct Choice as [_ Choice], (Choice nA) as [x [y Choice']].
            exists (h x), (h y).
            split. now exists x.
            split. now exists y. now rewrite <- P2.
        - now exists x.
    Qed. *)

    Lemma LS_imples_DC_pred: LS_countable_comp -> PDC.
    Proof using definiteness__R.
        intros LS total w.
        destruct (LS _ _ Model__A w) as [N [(f & g & bij_l & bij_r) [h [ele_el__h [n Eqan]]]]].
        specialize (@total_sat ((fun _ => n) >> h) total ) as total'.
        apply ele_el__h in total'.
        assert (exists R', (forall x: N, (exists y: N, R' x y)) /\ (forall α β, R' α β <-> R (h α) (h β))).
        exists (fun x y => tt ₚ[ N] cons N x 1 (cons N y 0 (nil N))).
        split. intro x. now specialize(total' x).
        intros α β; rewrite forfor_sat.
        now unfold elementary_homomorphism in ele_el__h; rewrite <- ele_el__h.
        destruct H as [R' [P1 P2]].
        assert (forall x : N, logical_decidable (R' x)).
        intros x y. destruct (definiteness__R (h x) (h y)); now try (left + right; rewrite P2).
        edestruct (@DC_pred_ω N R' _ _ bij_r bij_l H P1 n) as [P [case0 Choice]].
        unshelve eexists.
        exact (fun n' a' => exists n, h n = a' /\ P n' n); cbn.
        split.
        (* Proof of functional property*)
        - intro x; destruct (case0 x) as [n' [P1' P2']].
          exists (h n'); constructor.
          now exists n'.    
          intros a' [nn [Pa' Pa'']]. now rewrite (P2' nn).
        (* Proof of spec of the dependent choice predicate *)
        - split.
          + now exists n.
          + intro nA.
            destruct Choice as [_ Choice], (Choice nA) as [x [y Choice']].
            exists (h x), (h y).
            split. now exists x.
            split. now exists y. now rewrite <- P2.
    Qed.

    End DC_pred_full.



End DC.

Section DC_by_AC00.


    Definition BDC := forall (A: Type) (R: A -> A -> Prop),
        (forall x, exists y, R x y) ->
        exists f: nat -> A, forall n, exists m, R (f n) (f m).

    Lemma BDC_AC00_DC:
        BDC -> AC00 -> DC .
    Proof.
        intros BDC AC00 A R tR. 
        destruct (BDC A R tR) as [f Hf].
        destruct (AC00 (fun n m => R (f n) (f m)) Hf) as [g Hg].
        exists (fun n => f (iter (fun n => g n tt) n 0)).
        intro n; cbn.
        now destruct (Hg ((iter (fun n : nat => g n tt) n 0))) as [[] Hg'].
    Qed.
    
    
End DC_by_AC00.



Section LS_imples_BCAC.

    Hypothesis LS: (forall F P (M: @model F P), 𝕋 ⪳ M).

    Variable A: Type.
    Variable P: nat -> A -> Prop.

    Instance sig_A : preds_signature | 0 :=
        {| preds := nat;  ar_preds := fun _ => 1 |}.

    Instance interp_A : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun n v => P n (hd v)
    }.

    Instance model_A: model :=
    {
        domain := A;
        interp' := interp_A
    }.

    Variable E_term: nat -> term. 
    Variable term_E: term -> nat. 
    Hypothesis E_Κ: forall w, E_term (term_E w) = w.

    Definition BCAC_on (B: Type) (P': nat -> B -> Prop) :=
        (forall x, exists y, P' x y) ->
            exists f: nat -> (nat -> B), forall n, exists m, P' n (f n m).



    Theorem LS_implies_BCAC: (@BCAC_on A P).
    Proof.
        intros total_R.
        assert (forall n ρ, ρ ⊨ (∃ (atom _ _ _ _ n (cons _ ($0) _ (nil _))))).
        - cbn; intros; apply total_R.
        - destruct (LS model_A) as [N [h ele_el__h ] ].
          assert ( forall m (ρ : env term), ρ ⊨ (∃ atom m (cons term $0 0 (nil term)))).
          + intro m; specialize (ele_el__h (∃ atom m (cons term $0 0 (nil term)))).
            intro rho; rewrite ele_el__h.
            cbn; apply total_R.
          + exists (fun _ n => h (E_term n)).
            intro m; destruct (H0 m var) as [x Hx].
            exists (term_E x).
            specialize (ele_el__h (atom m (cons term ($0) 0 (nil term))) (fun _ => x)).
            cbn in ele_el__h.
            rewrite E_Κ.
            unfold ">>" in ele_el__h; rewrite <- ele_el__h.
            now cbn in Hx.
    Qed.

    Theorem LS_AC00_implies_CAC: (forall A R, @BCAC_on A R) -> AC00 -> CAC.
    Proof.
        intros BCAC AC00 B R tR.
        destruct (BCAC B R tR) as [f Hf].
        destruct (AC00 (fun n m => R n (f n m)) Hf).
        exists (fun n _ => f n (x n tt)).
        intro n; exists tt.
        now destruct (H n) as [[] H'].
    Qed.

End LS_imples_BCAC.



Section LS_imples_AC_κ.

    Hypothesis LS: (forall F P (M: @model F P), 𝕋 ⪳ M).
    Variable A: Type.
    Variable κ: Type.
    Variable P: κ -> A -> Prop.

    Instance sig_κ : preds_signature | 0 :=
        {| preds := κ;  ar_preds := fun _ => 1 |}.

    Instance interp_κ : interp A :=
    {
        i_func := fun F v => match F return A with end;
        i_atom := fun n v => P n (hd v)
    }.

    Instance model_κ: model :=
    {
        domain := A;
        interp' := interp_κ
    }.

    Variable E_term: κ -> term. 
    Variable term_E: term -> κ. 
    Hypothesis E_Κ: forall w, E_term (term_E w) = w.

    Definition WAC_on Κ B (R: Κ -> B -> Prop) :=
        inhabited B -> (forall n, exists y, R n y) -> exists f : Κ -> B, forall n, exists w, R n (f w).

    Theorem LS_implies_WAC_κ:
        @WAC_on κ A P.
    Proof.
        intros [] total_R.
        assert (forall n ρ, ρ ⊨ (∃ (atom _ _ _ _ n (cons _ ($0) _ (nil _))))).
        - cbn; intros; apply total_R.
        - destruct (LS model_κ) as [N [h ele_el__h] ].
          assert ( forall (m: κ) (ρ : env term), ρ ⊨ (∃ atom m (cons term $0 0 (nil term)))).
          + intro m; specialize (ele_el__h (∃ atom m (cons term $0 0 (nil term)))).
            intro rho; rewrite ele_el__h.
            cbn; apply total_R.
          + exists (fun (n: κ) => h (E_term n)).
            intro m; destruct (H0 m var) as [x Hx].
            exists (term_E x).
            specialize (ele_el__h (atom m (cons term ($0) 0 (nil term))) (fun _ => x)).
            cbn in ele_el__h.
            rewrite E_Κ.
            unfold ">>" in ele_el__h; rewrite <- ele_el__h.
            now cbn in Hx.
    Qed.


End LS_imples_AC_κ.


Section BDP'.

    Instance sig_unary : preds_signature | 0 :=
        {| preds := unit;  ar_preds := fun _ => 1 |}.

    Instance interp__U (A: Type) (P: A -> Prop): interp A :=
        {
            i_func := fun F v => match F return A with end;
            i_atom := fun P' v => P (hd v)
        }.

    Instance model__U (A: Type) (P: A -> Prop): model := 
        {
            domain := A;
            interp' := (@interp__U A P)
        }.

    Variable tnth_: nat -> term. 
    Hypothesis Hterm: forall t, exists n, tnth_ n = t. 

    Lemma LS_imples_BDP': 
        (forall M, 𝕋 ⪳ M) -> BDP'.
    Proof.
        intros LS A P a.
        destruct (LS (model__U P)) as [i_N [h emb]].
        exists (fun n => h (tnth_ n)).
        specialize (emb (∃ (atom tt) (cons _ ($0) 0 (nil _))) var) as emb'; cbn in emb'.
        intro H'.
        destruct emb' as [H1 [t Ht]].
        exact H'.
        destruct (Hterm t) as [w Hw].
        exists w.
        rewrite Hw.
        specialize (emb ((atom tt) (cons _ ($0) 0 (nil _))) (fun n => t)) ; cbn in emb.
        unfold ">>" in emb.
        now rewrite <- emb.
    Qed.

    Lemma LS_imples_BDP: 
        (forall M, 𝕋 ⪳ M) -> BDP.
    Proof.
        intros LS A P a.
        destruct (LS (model__U P)) as [i_N [h emb]].
        exists (fun n => h (tnth_ n)).
        specialize (emb (∀ (atom tt) (cons _ ($0) 0 (nil _))) var) as emb'; cbn in emb'.
        intro H'; apply emb'.
        intro d.
        specialize (emb ((atom tt) (cons _ ($0) 0 (nil _))) (fun n => d) ); cbn in emb.
        rewrite emb; unfold ">>".
        now destruct (Hterm d) as [x <-].
    Qed.

End BDP'.












